use clap::Parser;
use indicatif::{HumanBytes, HumanCount, ProgressBar, ProgressDrawTarget, ProgressStyle};
use olean_export::{search_path, with_big_stack, Env, Exporter};
use std::{
    cell::Cell,
    error::Error,
    fs::File,
    io::{self, BufWriter, Write},
    path::PathBuf,
    process::ExitCode,
    rc::Rc,
    thread,
    time::{Duration, Instant},
};

#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Read Lean 4 .olean files directly and emit the lean4export NDJSON stream.
#[derive(Debug, Parser)]
#[command(
    version,
    after_help = "Run under `lake env` so LEAN_PATH covers your build and the toolchain:\n  lake env olean-export Mathlib -o mathlib.ndjson"
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
    /// Decode modules on N threads [default: all cores]
    #[arg(short, long, value_name = "N")]
    jobs: Option<usize>,
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
    match with_big_stack(|| run(&cli)) {
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

fn run(cli: &Cli) -> Result<(), Box<dyn Error + Send + Sync>> {
    let start = Instant::now();
    let search: Vec<PathBuf> = cli.search.iter().cloned().chain(search_path()).collect();
    if search.is_empty() {
        return Err("no search path: run under `lake env` or pass -L DIR".into());
    }
    let roots: Vec<&str> = cli.modules.iter().map(String::as_str).collect();

    let pb = bar(
        cli.quiet,
        None,
        "{spinner:.cyan} decoding [{elapsed}] {msg}",
    );
    let jobs = cli
        .jobs
        .unwrap_or_else(|| thread::available_parallelism().map_or(1, usize::from));
    pb.set_message(format!("finding modules, {jobs} threads"));
    let env = Env::load_with(&search, &roots, jobs, &|modules, consts| {
        pb.set_message(format!(
            "{} modules, {} constants",
            HumanCount(modules as u64),
            HumanCount(consts as u64)
        ));
    })?;
    pb.finish_and_clear();
    let loaded = start.elapsed();

    let targets = if cli.consts.is_empty() {
        env.roots().collect()
    } else {
        cli.consts
            .iter()
            .map(|n| {
                env.find_name(n)
                    .ok_or_else(|| format!("unknown constant {n}"))
            })
            .collect::<Result<Vec<_>, _>>()?
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
    let counts = ex.counts();
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
            HumanCount(counts.names.into()),
            HumanCount(counts.levels.into()),
            HumanCount(counts.exprs.into()),
            start.elapsed().as_secs_f64(),
            HumanBytes(rate),
        );
    }
    Ok(())
}
