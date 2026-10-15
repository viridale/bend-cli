// The argbench command (examples/argbench/app.bend) in clap: it prints the
// line the Bend app prints for each argv tools/peerbench.sh checks.
use clap::{ArgAction, Parser, Subcommand, ValueEnum};

#[derive(Parser)]
#[command(name = "argbench", about = "Print the line an argv decodes to")]
#[command(arg_required_else_help = true)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Clone, Copy, ValueEnum)]
enum Format {
    Text,
    Json,
    Csv,
}

// A repeated option takes its last value and a repeated flag is accepted,
// as in bend-cli; clap rejects both by default.
#[derive(Subcommand)]
enum Command {
    /// Build inputs
    #[command(args_override_self = true)]
    Build {
        /// More output; repeat for more
        #[arg(short, long, action = ArgAction::Count)]
        verbose: u8,
        /// Less output
        #[arg(short, long)]
        quiet: bool,
        /// Write the result to FILE
        #[arg(short, long, value_name = "FILE", default_value = "out")]
        output: String,
        /// Search DIR for inputs
        #[arg(short = 'I', long, value_name = "DIR")]
        include: Vec<String>,
        /// Run N jobs at once
        #[arg(short, long, value_name = "N", default_value_t = 1)]
        jobs: u32,
        /// Output format
        #[arg(short, long, value_enum, value_name = "FMT", default_value_t = Format::Text)]
        format: Format,
        /// Files to build
        #[arg(value_name = "INPUT", required = true)]
        inputs: Vec<String>,
    },
    /// Check inputs
    #[command(args_override_self = true)]
    Check {
        /// Treat warnings as errors
        #[arg(short, long)]
        strict: bool,
        /// Files to check
        #[arg(value_name = "INPUT", required = true)]
        inputs: Vec<String>,
    },
}

fn main() {
    match Cli::parse().command {
        Command::Build { verbose, quiet, output, include, jobs, format, inputs } => {
            let format = match format {
                Format::Text => "text",
                Format::Json => "json",
                Format::Csv => "csv",
            };
            println!(
                "build verbose={verbose} quiet={quiet} output={output} include={} jobs={jobs} format={format} inputs={}",
                include.join(","),
                inputs.join(",")
            );
        }
        Command::Check { strict, inputs } => {
            println!("check strict={strict} inputs={}", inputs.join(","));
        }
    }
}
