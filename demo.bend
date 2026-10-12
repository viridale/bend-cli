# Purpose: the pkg reference app, pure part: its spec, actions and decoder.
# Expected output: ALL PROOFS CHECK.
# Run: bend demo.bend --check-only

import Base
import ./cli.bend as Cli

def cli() -> Cli.Cmd:
  Cli.cmd("pkg", "A package manager (demo)", [
    Cli.version("0.1.0"),
    Cli.color(),
    Cli.arg("-v, --verbose...", "More output; repeat for more",
      [Cli.global()]),
    Cli.arg("-C <DIR>", "Run as if started in DIR",
      [Cli.global(), Cli.as_dir()]),
    Cli.sub("add", "Add packages", [
      Cli.arg("-D, --dev", "Add as development dependencies", []),
      Cli.arg("--registry <URL>", "Registry to fetch from",
        [Cli.env("PKG_REGISTRY"), Cli.default("https://registry.example")]),
      Cli.arg("<NAME>...", "Packages to add", []),
      Cli.example("pkg add -D left-pad", "Add a development dependency"),
    ]),
    Cli.sub("remove", "Remove packages", [
      Cli.alias("rm"),
      Cli.arg("<NAME>...", "Packages to remove", []),
    ]),
    Cli.sub("list", "List installed packages", [
      Cli.arg("-a, --all", "Include transitive packages", []),
      Cli.arg("--format <FMT>", "Output format",
        [Cli.one_of(["text", "json"]), Cli.default("text")]),
    ]),
    Cli.sub("run", "Run a package script", [
      Cli.arg("<SCRIPT>", "Script name", []),
      Cli.arg("[ARGS]...", "Arguments for the script", [Cli.rest()]),
    ]),
    Cli.completions(),
    Cli.man(),
  ])

type Format is Data:
  Text{}
  Json{}

type Job is Data:
  Add{dev: Bool, registry: String, names: List<&2, String>}
  Remove{names: List<&2, String>}
  Show{all: Bool, format: Format}
  Script{name: String, args: List<&2, String>}

type Action is Data:
  Action{verbose: Nat, dir: Maybe<&2, String>, job: Job}

def add(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    dev : Bool <- Cli.flag(m, "dev")
    registry : String <- Cli.str(m, "registry")
    names : List<&2, String> <- Cli.strs(m, "name")
    return Add{dev, registry, names}

def remove(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    names : List<&2, String> <- Cli.strs(m, "name")
    return Remove{names}

def show(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    all : Bool <- Cli.flag(m, "all")
    format : Format <- Cli.choose(Format, m, "format",
      [("text", Text{}), ("json", Json{})])
    return Show{all, format}

def script(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    name : String <- Cli.str(m, "script")
    args : List<&2, String> <- Cli.strs(m, "args")
    return Script{name, args}

def decode(+m: Cli.Matches) -> Cli.Dec(Action):
  do Cli.Dec<Action>:
    verbose : Nat <- Cli.count(m, "verbose")
    dir : Maybe<&2, String> <- Cli.str_opt(m, "C")
    job : Job <- Cli.route(Job, m, [
      ("add", add),
      ("remove", remove),
      ("list", show),
      ("run", script),
    ])
    return Action{verbose, dir, job}
