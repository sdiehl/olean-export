use clap::Parser;
use indicatif::{HumanBytes, HumanCount, ProgressBar, ProgressDrawTarget, ProgressStyle};
use std::{
    cell::Cell,
    fs::File,
    io::{self, BufWriter, Write},
    path::PathBuf,
    process::ExitCode,
    rc::Rc,
    time::{Duration, Instant},
};
use tiny_olean::{search_path, with_big_stack, Env, Exporter};

/// Read Lean 4 .olean files directly and emit the lean4export NDJSON stream.
#[derive(Debug, Parser)]
#[command(
    version,
    after_help = "Run under `lake env` so LEAN_PATH covers your build and the toolchain:\n  lake env tiny-olean Mathlib -o mathlib.ndjson"
)]
struct Cli {
    /// Root modules to load, e.g. `Mathlib` or `MyProject.Main`
    #[arg(required = true, value_name = "MODULE")]
    modules: Vec<String>,
    /// Export only these constants and what they depend on (repeatable)
    #[arg(short, long = "const", value_name = "NAME")]
    consts: Vec<String>,
    /// Write to FILE instead of stdout
    #[arg(short, long, value_name = "FILE")]
    output: Option<PathBuf>,
    /// Search DIR before `LEAN_PATH` (repeatable)
    #[arg(short = 'L', long = "search", value_name = "DIR")]
    search: Vec<PathBuf>,
    /// No progress bars or summary
    #[arg(short, long)]
    quiet: bool,
}

struct Counting<W> {
    inner: W,
    bytes: Rc<Cell<u64>>,
}

impl<W: Write> Write for Counting<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = self.inner.write(buf)?;
        self.bytes.set(self.bytes.get() + n as u64);
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match with_big_stack(move || run(&cli)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn bar(quiet: bool, len: Option<u64>, template: &str) -> ProgressBar {
    let pb = len.map_or_else(ProgressBar::new_spinner, ProgressBar::new);
    if quiet {
        pb.set_draw_target(ProgressDrawTarget::hidden());
    }
    pb.set_style(
        ProgressStyle::with_template(template)
            .expect("valid template")
            .progress_chars("=> "),
    );
    pb.enable_steady_tick(Duration::from_millis(100));
    pb
}

fn run(cli: &Cli) -> io::Result<()> {
    let start = Instant::now();
    let search: Vec<PathBuf> = cli.search.iter().cloned().chain(search_path()).collect();
    if search.is_empty() {
        return Err(io::Error::other(
            "no search path: run under `lake env` or pass -L DIR",
        ));
    }
    let roots: Vec<&str> = cli.modules.iter().map(String::as_str).collect();

    let pb = bar(
        cli.quiet,
        None,
        "{spinner:.cyan} decoding [{elapsed}] {msg}",
    );
    let env = Env::load_with(&search, &roots, &mut |env| {
        if let Some(m) = env.modules.last() {
            pb.set_message(format!(
                "{} modules, {} constants  {m}",
                HumanCount(env.modules.len() as u64),
                HumanCount(env.consts.len() as u64)
            ));
        }
    })?;
    pb.finish_and_clear();
    let loaded = start.elapsed();

    let targets = if cli.consts.is_empty() {
        env.roots().collect()
    } else {
        cli.consts
            .iter()
            .map(|n| {
                env.find_name(n).ok_or_else(|| {
                    io::Error::new(io::ErrorKind::NotFound, format!("unknown constant {n}"))
                })
            })
            .collect::<io::Result<Vec<_>>>()?
    };

    let sink: Box<dyn Write> = match &cli.output {
        Some(path) => Box::new(File::create(path)?),
        None => Box::new(io::stdout().lock()),
    };
    let bytes = Rc::new(Cell::new(0));
    let out = BufWriter::with_capacity(
        1 << 20,
        Counting {
            inner: sink,
            bytes: Rc::clone(&bytes),
        },
    );
    let pb = bar(
        cli.quiet,
        Some(targets.len() as u64),
        "{spinner:.cyan} emitting [{elapsed}] [{bar:30.cyan/blue}] {human_pos}/{human_len} {msg}",
    );
    let mut ex = Exporter::new(&env, out);
    ex.meta()?;
    for (i, &c) in targets.iter().enumerate() {
        ex.constant(c)?;
        if i % 256 == 0 {
            pb.set_position(i as u64);
            pb.set_message(HumanBytes(bytes.get()).to_string());
        }
    }
    let [names, levels, exprs] = ex.counts();
    ex.finish()?;
    pb.finish_and_clear();

    if !cli.quiet {
        let ms = start.elapsed().saturating_sub(loaded).as_millis().max(1);
        let rate = u64::try_from(u128::from(bytes.get()) * 1000 / ms).unwrap_or(u64::MAX);
        eprintln!(
            "{} modules, {} constants decoded in {:.2}s\n{} of NDJSON ({} names, {} levels, {} exprs) in {:.2}s total, {}/s",
            HumanCount(env.modules.len() as u64),
            HumanCount(env.consts.len() as u64),
            loaded.as_secs_f64(),
            HumanBytes(bytes.get()),
            HumanCount(names.into()),
            HumanCount(levels.into()),
            HumanCount(exprs.into()),
            start.elapsed().as_secs_f64(),
            HumanBytes(rate),
        );
    }
    Ok(())
}
