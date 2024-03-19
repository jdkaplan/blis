use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use eyre::Context;

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
        match self.command.as_ref().unwrap_or(&Cmd::default()) {
            Cmd::Repl => todo!(),
            Cmd::Run(cmd) => cmd.run(),
            Cmd::Build(_) => todo!(),
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

#[derive(Debug, clap::Args)]
struct Run {
    /// Path to the program
    path: PathBuf,
}

impl Run {
    fn run(&self) -> eyre::Result<()> {
        let mut file =
            File::open(&self.path).wrap_err_with(|| format!("open file: {:?}", self.path))?;

        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .wrap_err_with(|| format!("read file: {:?}", self.path))?;

        let ast = Parser::parse(&contents).wrap_err("parse file")?;

        let chunk = Compiler::compile(&ast)?;

        let mut vm = Vm::default();
        vm.interpret(chunk)?;

        Ok(())
    }
}

#[derive(Debug, clap::Args)]
struct Build {
    /// Path to the program
    path: PathBuf,
}
