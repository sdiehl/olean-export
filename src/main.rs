use clap::{Parser, Subcommand};
use indicatif::{HumanBytes, HumanCount, ProgressBar, ProgressDrawTarget, ProgressStyle};
use olean_export::{resolve, search_path, with_big_stack, Env, Exporter, Summary};
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
    args_conflicts_with_subcommands = true,
    subcommand_negates_reqs = true,
    after_help = "Run under `lake env` so LEAN_PATH covers your build and the toolchain:\n  lake env olean-export Mathlib -o mathlib.ndjson"
)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
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
    #[arg(short = 'L', long = "search", value_name = "DIR", global = true)]
    search: Vec<PathBuf>,
    /// Decode modules on N threads [default: all cores]
    #[arg(short, long, value_name = "N")]
    jobs: Option<usize>,
    /// No progress bars or summary
    #[arg(short, long)]
    quiet: bool,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Summarize one olean: header, imports, constants and where its bytes go
    Inspect {
        /// A module name such as `Init.Prelude`, or a path to an .olean
        #[arg(value_name = "MODULE|FILE")]
        target: String,
        /// List every constant with its kind
        #[arg(short, long)]
        consts: bool,
    },
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
    let result = match &cli.command {
        Some(Command::Inspect { target, consts }) => inspect(&cli, target, *consts),
        None => with_big_stack(|| run(&cli)),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e)
            if e.downcast_ref::<io::Error>().map(io::Error::kind)
                == Some(io::ErrorKind::BrokenPipe) =>
        {
            ExitCode::SUCCESS
        }
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

type Res = Result<(), Box<dyn Error + Send + Sync>>;

fn search(cli: &Cli) -> Result<Vec<PathBuf>, Box<dyn Error + Send + Sync>> {
    let dirs: Vec<PathBuf> = cli.search.iter().cloned().chain(search_path()).collect();
    if dirs.is_empty() {
        return Err("no search path: run under `lake env` or pass -L DIR".into());
    }
    Ok(dirs)
}

fn inspect(cli: &Cli, target: &str, list: bool) -> Res {
    let path = PathBuf::from(target);
    let path = if path.is_file() {
        path
    } else {
        resolve(&search(cli)?, target)?
    };
    let s = Summary::open(&path)?;
    let flag = |on: bool, s: &'static str| if on { s } else { "" };
    let mut out = io::stdout().lock();
    writeln!(
        out,
        "Lean {} ({}){}{}",
        s.header.version,
        s.header.githash,
        flag(s.header.gmp, ", gmp"),
        flag(s.is_module, ", module")
    )?;
    for (p, n) in &s.parts {
        writeln!(out, "  {:>11}  {}", HumanBytes(*n).to_string(), p.display())?;
    }
    writeln!(out, "\nimports ({})", s.imports.len())?;
    for i in &s.imports {
        writeln!(
            out,
            "  {}{}{}{}",
            i.module,
            flag(i.all, " all"),
            flag(!i.exported, " private"),
            flag(i.meta, " meta")
        )?;
    }
    let mut kinds: Vec<(&str, usize)> = Vec::new();
    for d in &s.consts {
        match kinds.iter_mut().find(|k| k.0 == d.kind) {
            Some(k) => k.1 += 1,
            None => kinds.push((d.kind, 1)),
        }
    }
    kinds.sort_by_key(|k| std::cmp::Reverse(k.1));
    let kinds: Vec<String> = kinds.iter().map(|(k, n)| format!("{n} {k}")).collect();
    writeln!(
        out,
        "\nconstants ({}): {}",
        s.consts.len(),
        kinds.join(", ")
    )?;
    if list {
        let mut consts: Vec<_> = s.consts.iter().collect();
        consts.sort_by(|a, b| a.name.cmp(&b.name));
        for d in consts {
            let line = format!("  {:<9} {} {}", d.kind, d.name, d.safety);
            writeln!(out, "{}", line.trim_end())?;
        }
    }
    let mut sections: Vec<_> = s.sections.iter().filter(|x| x.items > 0).collect();
    sections.sort_by_key(|x| std::cmp::Reverse(x.bytes));
    let total = s.bytes().max(1);
    let row = |out: &mut io::StdoutLock<'_>, bytes: u64, items: String, name: &str| {
        #[allow(clippy::cast_precision_loss)]
        let share = 100.0 * bytes as f64 / total as f64;
        let size = HumanBytes(bytes).to_string();
        writeln!(out, "{size:>11}  {share:>5.1}%  {items:>6}  {name}")
    };
    writeln!(
        out,
        "\n{:>11}  {:>6}  {:>6}  section",
        "bytes", "share", "items"
    )?;
    for x in &sections {
        row(&mut out, x.bytes, x.items.to_string(), &x.name)?;
    }
    let reached: u64 = s.sections.iter().map(|x| x.bytes).sum();
    row(
        &mut out,
        total.saturating_sub(reached),
        String::new(),
        "(headers and unreached)",
    )?;
    Ok(())
}

fn run(cli: &Cli) -> Res {
    let start = Instant::now();
    let search = search(cli)?;
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
