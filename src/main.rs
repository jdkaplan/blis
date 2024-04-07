use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

use eyre::Context;

use blis::bytecode::Chunk;
use blis::compile::Compiler;
use blis::parse::Parser;
use blis::vm::Vm;

fn main() -> eyre::Result<()> {
    color_eyre::install()?;
    init_tracing();

    let cli = <Cli as clap::Parser>::parse();
    cli.execute()
}

fn init_tracing() {
    use tracing_subscriber::EnvFilter;

    tracing_subscriber::fmt()
        .pretty()
        .with_env_filter(EnvFilter::from_default_env())
        .init();
}

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Cmd>,
}

impl Cli {
    fn execute(&self) -> eyre::Result<()> {
        match &self.command {
            Some(cmd) => cmd.execute(),
            None => Cmd::default().execute(),
        }
    }
}

#[derive(clap::Subcommand, Default)]
enum Cmd {
    /// Start an interactive session
    #[default]
    Repl,

    /// Run a program
    Run(Run),

    /// Compile a program
    Build(Build),
}

impl Cmd {
    fn execute(&self) -> eyre::Result<()> {
        match self {
            Cmd::Repl => todo!(),
            Cmd::Run(cmd) => cmd.execute(),
            Cmd::Build(cmd) => cmd.execute(),
        }
    }
}

#[derive(Debug, clap::Args)]
struct Run {
    /// Path to the program
    path: PathBuf,

    /// Whether the program is a precompiled binary
    #[clap(long, default_value = "false")]
    precompiled: bool,
}

impl Run {
    fn execute(&self) -> eyre::Result<()> {
        let chunk: Chunk = if self.precompiled {
            let file = open_file(&self.path)?;
            Chunk::read(file).wrap_err("load precompiled program")?
        } else {
            let source = read_file(&self.path)?;
            let ast = Parser::parse(&source).wrap_err("parse file")?;
            Compiler::compile(&ast)?
        };

        let mut vm = Vm::default();
        vm.interpret(chunk).wrap_err("runtime error")
    }
}

#[derive(Debug, clap::Args)]
struct Build {
    /// Path to the program
    path: PathBuf,

    /// Path to the output file
    #[clap(long, value_parser)]
    output: Option<PathBuf>,
}

impl Build {
    fn execute(&self) -> eyre::Result<()> {
        let outpath = match &self.output {
            Some(path) => path.to_path_buf(),
            None => default_output_path(&self.path)?,
        };

        let source = read_file(&self.path)?;

        let ast = Parser::parse(&source).wrap_err("parse file")?;

        let chunk = Compiler::compile(&ast)?;

        let outfile = create_file(&outpath)?;
        chunk.write(outfile).wrap_err("encode blob")?;

        Ok(())
    }
}

fn read_file(path: &Path) -> eyre::Result<String> {
    let mut file = open_file(path)?;

    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .wrap_err_with(|| format!("read file: {:?}", path))?;

    Ok(contents)
}

fn open_file(path: &Path) -> eyre::Result<File> {
    File::open(path).wrap_err_with(|| format!("open file: {:?}", path))
}

fn create_file(path: &Path) -> eyre::Result<File> {
    File::create(path).wrap_err_with(|| format!("create file: {:?}", path))
}

fn default_output_path(path: &Path) -> eyre::Result<PathBuf> {
    let out = path.with_extension("blob");
    if path == out {
        return Err(eyre::eyre!(
            "output path is the same as input path: {:?}",
            out
        ));
    }
    Ok(out)
}
