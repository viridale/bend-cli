# Purpose: the argbench example app: two subcommands with a count, a flag,
# a defaulted option, a repeatable option, a u32 option, a one_of option and
# required positionals, and an action that prints the line its argv decodes
# to. The peers in bench/peers declare the same command in other CLI
# libraries and print the same line, so tools/peerbench.sh can check them
# against it and time them.
# Expected output: ALL PROOFS CHECK.
# Run: bend examples/argbench/app.bend --check-only

import Base
import ../../cli.bend as Cli

type Format is Data:
  Text{}
  Json{}
  Csv{}

type Job is Data:
  Build{verbose: Nat, quiet: Bool, output: String, include: List<&2, String>,
    jobs: U32, format: Format, inputs: List<&2, String>}
  Check{strict: Bool, inputs: List<&2, String>}

def cli() -> Cli.Cmd:
  Cli.cmd("argbench", "Print the line an argv decodes to", [
    Cli.sub("build", "Build inputs", [
      Cli.arg("-v, --verbose...", "More output; repeat for more", []),
      Cli.arg("-q, --quiet", "Less output", []),
      Cli.arg("-o, --output <FILE>", "Write the result to FILE",
        [Cli.default("out")]),
      Cli.arg("-I, --include <DIR>...", "Search DIR for inputs", []),
      Cli.arg("-j, --jobs <N>", "Run N jobs at once",
        [Cli.as_u32(), Cli.default("1")]),
      Cli.arg("-f, --format <FMT>", "Output format",
        [Cli.one_of(["text", "json", "csv"]), Cli.default("text")]),
      Cli.arg("<INPUT>...", "Files to build", []),
    ]),
    Cli.sub("check", "Check inputs", [
      Cli.arg("-s, --strict", "Treat warnings as errors", []),
      Cli.arg("<INPUT>...", "Files to check", []),
    ]),
  ])

def build(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    verbose : Nat <- Cli.count(m, "verbose")
    quiet : Bool <- Cli.flag(m, "quiet")
    output : String <- Cli.str(m, "output")
    include : List<&2, String> <- Cli.strs(m, "include")
    jobs : U32 <- Cli.u32(m, "jobs")
    format : Format <- Cli.choose(Format, m, "format",
      [("text", Text{}), ("json", Json{}), ("csv", Csv{})])
    inputs : List<&2, String> <- Cli.strs(m, "input")
    return Build{verbose, quiet, output, include, jobs, format, inputs}

def check(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    strict : Bool <- Cli.flag(m, "strict")
    inputs : List<&2, String> <- Cli.strs(m, "input")
    return Check{strict, inputs}

def decode(+m: Cli.Matches) -> Cli.Dec(Job):
  Cli.route(Job, m, [("build", build), ("check", check)])

def bool_word(b: Bool) -> String:
  match b:
    case True{}: "true"
    case False{}: "false"

def format_word(f: Format) -> String:
  match f:
    case Text{}: "text"
    case Json{}: "json"
    case Csv{}: "csv"

# The command, then each field as name=value in declaration order, with
# lists joined by commas.
def line(j: Job) -> String:
  match j:
    case Build{verbose, quiet, output, include, jobs, format, inputs}:
      String.concat(["build verbose=", Nat.show(verbose), " quiet=",
        bool_word(quiet), " output=", output, " include=",
        String.join(include, ","), " jobs=", U32.show(jobs), " format=",
        format_word(format), " inputs=", String.join(inputs, ",")])
    case Check{strict, inputs}:
      String.concat(["check strict=", bool_word(strict), " inputs=",
        String.join(inputs, ",")])

def act(+t: Cli.Term, j: Job) -> IO(U32):
  do IO<U32>:
    IO.print(line(j))
    return 0
