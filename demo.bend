# Purpose: the pkg reference app, pure part: its spec, actions, decoder,
# plan and act (§12.3).
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
  Plain{}
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
      [("text", Plain{}), ("json", Json{})])
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

# What act does: its exit code and the line it prints (§12.3).
type Plan is Data:
  Plan{code: U32, line: String}

def bool_word(b: Bool) -> String:
  match b:
    case True{}: "true"
    case False{}: "false"

def format_word(f: Format) -> String:
  match f:
    case Plain{}: "text"
    case Json{}: "json"

def dir_text(dir: Maybe<&2, String>) -> String:
  match dir:
    case None{}: ""
    case Some{d}: String.append(" dir=", d)

def read_code(found: Maybe<&2, U32>) -> U32:
  match found:
    case None{}: 0
    case Some{n}: n

# `run exit <N>` returns N, so end-to-end cases can reach any exit code.
def exit_code(exit: Bool, args: List<&2, String>) -> U32:
  match exit args:
    case True{} n <> Nil{}: read_code(U32.read(n))
    case _ _: 0

# The job's word and fields, then rest; only `run exit` sets the code.
def job_plan(j: Job, rest: String) -> Plan:
  match j:
    case Add{dev, registry, names}:
      Plan{0, String.concat(["add dev=", bool_word(dev), " registry=",
        registry, " names=", String.join(names, ","), rest])}
    case Remove{names}:
      Plan{0, String.concat(["remove names=", String.join(names, ","), rest])}
    case Show{all, format}:
      Plan{0, String.concat(["list all=", bool_word(all), " format=",
        format_word(format), rest])}
    case Script{+name, +args}:
      Plan{exit_code(String.eq(name, "exit"), args),
        String.concat(["run script=", name, " args=", String.join(args, ","),
          rest])}

def plan(a: Action) -> Plan:
  match a:
    case Action{verbose, dir, job}:
      job_plan(job, String.concat([" verbose=", Nat.show(verbose),
        dir_text(dir)]))

def said(p: Plan) -> IO(U32):
  match p:
    case Plan{code, line}:
      do IO<U32>:
        IO.print(line)
        return code

# pkg's act: print plan's line and return its code. pkg does nothing else,
# so it ignores the terminal.
def act(+t: Cli.Term, a: Action) -> IO(U32):
  said(plan(a))
