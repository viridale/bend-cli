# `git`-like: nested subcommands, globals and plugins

`vcs` is a small git-shaped tool. It shows:

- subcommands two levels deep (`vcs remote add`), with an alias (`rm`);
- a command that runs on its own and also has subcommands (`vcs remote`);
- global options valid at every level (`-C`, `-v`, `--color`);
- a required option (`commit -m`);
- git-style plugins: an unknown command `vcs foo` runs `vcs-foo` from
  `PATH`, with a did-you-mean error when there is none;
- completions and a man page.

```console
$ vcs --help
A tiny version control system

Usage: vcs [OPTIONS] <COMMAND>

Commands:
  init                Create an empty repository
  commit              Record changes
  remote              Manage remote repositories
  completions         Print a shell completion script
  help                Print this message or the help of the given subcommand(s)

Options:
  -C <PATH>           Run as if vcs was started in PATH [default: .]
  -v, --verbose...    Print more detail; repeat for more
      --color <WHEN>  When to use color [default: auto] [possible values: auto,
                      always, never]
  -h, --help          Print help
  -V, --version       Print version

Other commands run vcs-<COMMAND> from PATH, if it exists.
```

```console
$ vcs remote --help
Manage remote repositories

Usage: vcs remote [OPTIONS] [COMMAND]

Commands:
  add                 Add a remote
  remove              Remove a remote [aliases: rm]
  help                Print this message or the help of the given subcommand(s)

Options:
  -C <PATH>           Run as if vcs was started in PATH [default: .]
  -v, --verbose...    Print more detail; repeat for more
      --color <WHEN>  When to use color [default: auto] [possible values: auto,
                      always, never]
  -h, --help          Print help
```

## `app.bend`

```python
# Purpose: vcs, a git-like tool with nested subcommands, global options and plugins.
# Expected output: one line per command; plugins print their own output.
# Run: bend main.bend -- remote add origin https://example.com/r
import Base
import cli@1.0.0.0/cli.bend as Cli

type Job is Data:
  Init{dir: Maybe<&2, String>, bare: Bool}
  Commit{message: String, all: Bool, amend: Bool}
  Remotes{}
  RemoteAdd{name: String, url: String, fetch: Bool}
  RemoteRemove{name: String}
  Plugin{name: String, args: List<&2, String>}

type Vcs is Data:
  Vcs{cwd: String, verbose: Nat, job: Job}

def remote() -> Cli.Item:
  Cli.sub("remote", "Manage remote repositories", [
    Cli.sub_optional(),
    Cli.sub("add", "Add a remote", [
      Cli.arg("-f, --fetch", "Fetch from the remote after adding it", []),
      Cli.arg("<NAME>", "Name of the remote", []),
      Cli.arg("<URL>", "Where the remote lives", []),
    ]),
    Cli.sub("remove", "Remove a remote", [
      Cli.alias("rm"),
      Cli.arg("<NAME>", "Name of the remote", []),
    ]),
  ])

def cli() -> Cli.Cmd:
  Cli.cmd("vcs", "A tiny version control system", [
    Cli.version("0.3.0"),
    Cli.external(),
    Cli.arg("-C <PATH>", "Run as if vcs was started in PATH",
      [Cli.id("cwd"), Cli.global(), Cli.as_dir(), Cli.default(".")]),
    Cli.arg("-v, --verbose...", "Print more detail; repeat for more", [Cli.global()]),
    Cli.color(),
    Cli.sub("init", "Create an empty repository", [
      Cli.arg("--bare", "Create a repository without a working tree", []),
      Cli.arg("[DIR]", "Directory to create it in", [Cli.as_dir()]),
    ]),
    Cli.sub("commit", "Record changes", [
      Cli.arg("-m, --message <MSG>", "Commit message", [Cli.required()]),
      Cli.arg("-a, --all", "Stage every modified file first", []),
      Cli.arg("--amend", "Replace the last commit", []),
    ]),
    remote(),
    Cli.completions(),
    Cli.man(),
    Cli.after("Other commands run vcs-<COMMAND> from PATH, if it exists."),
  ])

def init(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    bare : Bool <- Cli.flag(m, "bare")
    dir : Maybe<&2, String> <- Cli.str_opt(m, "dir")
    return Init{dir, bare}

def commit(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    message : String <- Cli.str(m, "message")
    all : Bool <- Cli.flag(m, "all")
    amend : Bool <- Cli.flag(m, "amend")
    return Commit{message, all, amend}

def remotes(+m: Cli.Matches) -> Cli.Dec(Job):
  Cli.Dec.pure(Job, Remotes{})

def remote_add(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    fetch : Bool <- Cli.flag(m, "fetch")
    name : String <- Cli.str(m, "name")
    url : String <- Cli.str(m, "url")
    return RemoteAdd{name, url, fetch}

def remote_remove(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    name : String <- Cli.str(m, "name")
    return RemoteRemove{name}

def external(found: Maybe<(String & List<&2, String>)>) -> Cli.Dec(Job):
  match found:
    case Some{(name, args)}:
      Cli.Dec.pure(Job, Plugin{name, args})
    case None{}:
      Cli.fail(Job, "a command is required")

def plugin(+m: Cli.Matches) -> Cli.Dec(Job):
  external(Cli.external_args(m))

def decode(+m: Cli.Matches) -> Cli.Dec(Vcs):
  do Cli.Dec<Vcs>:
    cwd : String <- Cli.str(m, "cwd")
    verbose : Nat <- Cli.count(m, "verbose")
    job : Job <- Cli.route(Job, m, [
      ("", plugin),
      ("init", init),
      ("commit", commit),
      ("remote", remotes),
      ("remote add", remote_add),
      ("remote remove", remote_remove),
    ])
    return Vcs{cwd, verbose, job}

# What each built-in command reports. A real tool would do the work here.
def place(+cwd: String, dir: Maybe<&2, String>) -> String:
  match dir:
    case None{}:
      cwd
    case Some{d}:
      (cwd ++ "/" ++ d : String)

def kind(bare: Bool) -> String:
  match bare:
    case True{}:
      "bare "
    case False{}:
      ""

def fetched(fetch: Bool, +name: String) -> String:
  match fetch:
    case True{}:
      ("\nFetched '" ++ name ++ "'" : String)
    case False{}:
      ""

def amended(amend: Bool) -> String:
  match amend:
    case True{}:
      " (amended)"
    case False{}:
      ""

def staged(all: Bool) -> String:
  match all:
    case True{}:
      "Staged all modified files\n"
    case False{}:
      ""

def say_job(+cwd: String, job: Job) -> String:
  match job:
    case Init{dir, bare}:
      ("Initialized empty " ++ kind(bare) ++ "repository in " ++ place(cwd, dir) : String)
    case Commit{message, all, amend}:
      (staged(all) ++ "[main] " ++ message ++ amended(amend) : String)
    case Remotes{}:
      "No remotes"
    case RemoteAdd{+name, url, fetch}:
      ("Added remote '" ++ name ++ "' at " ++ url ++ fetched(fetch, name) : String)
    case RemoteRemove{name}:
      ("Removed remote '" ++ name ++ "'" : String)
    case Plugin{name, args}:
      ""

def say(verbose: Nat, +cwd: String, job: Job) -> String:
  match verbose:
    case 0n:
      say_job(cwd, job)
    case 1n+p:
      ("in " ++ cwd ++ ": " ++ say_job(cwd, job) : String)

# Plugins: run vcs-<name> with the remaining arguments.
def Ran() -> Type:
  Result<&1, &1, U32 & String, U32 & (String & String)>

# Stderr writes always end in a newline, so drop the plugin's own.
def chomp(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      match t:
        case SNil{}:
          Bool.pick(String, Char.is_eq(h, '\n'), SNil{}, SCon{h, SNil{}})
        case SCon{h2, t2}:
          SCon{h, chomp(SCon{h2, t2})}

def to_err(err: String) -> IO(Unit):
  match err:
    case SNil{}:
      IO.pure(Unit, Unit{})
    case SCon{h, t}:
      IO.print_err(chomp(SCon{h, t}))

# A missing plugin is reported like the library's own unknown-subcommand
# error, with the same did-you-mean rule.
def quoted(names: List<&2, String>) -> String:
  match names:
    case Nil{}:
      ""
    case n <> rest:
      (", '" ++ n ++ "'" ++ quoted(rest) : String)

def tip(names: List<&2, String>) -> String:
  match names:
    case Nil{}:
      ""
    case n <> rest:
      match rest:
        case Nil{}:
          ("\n\n  tip: a similar subcommand exists: '" ++ n ++ "'" : String)
        case r <> t:
          ("\n\n  tip: some similar subcommands exist: '" ++ n ++ "'" ++ quoted(r <> t) : String)

def missing(+name: String, msg: String) -> String:
  ("error: unrecognized subcommand '" ++ name ++ "' (vcs-" ++ name ++ ": " ++ msg ++ ")"
    ++ tip(Cli.suggest(name, ["init", "commit", "remote", "completions", "help"]))
    ++ "\n\nFor more information, try '--help'." : String)

def ran(+name: String, r: Ran()) -> IO(U32):
  match r:
    case Done{(status, (out, err))}:
      do IO<U32>:
        IO.write(out)
        to_err(err)
        return status
    case Fail{(code, msg)}:
      do IO<U32>:
        IO.print_err(missing(name, msg))
        return 2

# Process.run takes a List<String>; argv values are List<&2, String>.
def loose(xs: List<&2, String>) -> List<String>:
  match xs:
    case Nil{}:
      []
    case h <> t:
      h <> loose(t)

def run_plugin(+name: String, args: List<&2, String>) -> IO(U32):
  IO.bind(Ran(), U32,
    Process.run(("vcs-" ++ name : String), loose(args), "", 67108864, 4294967295),
    ran(name))

def act_job(verbose: Nat, cwd: String, +job: Job) -> IO(U32):
  match job:
    case Plugin{name, args}:
      run_plugin(name, args)
    case _:
      do IO<U32>:
        IO.print(say(verbose, cwd, job))
        return 0

def act(+t: Cli.Term, v: Vcs) -> IO(U32):
  match v:
    case Vcs{cwd, verbose, job}:
      act_job(verbose, cwd, job)
```

Notes:

- **One route table for the whole tree.** Keys are command paths below the
  root. `"remote"` is the bare `vcs remote` (allowed by `sub_optional()`),
  and `""` is the root itself, which is only reached through `external()`
  ([Subcommands](../how-to/subcommands.md#required-or-optional-subcommand)).
- **Ids are unique per scope, globals included.** The global `-C <PATH>`
  would get the id `C`; it is given `cwd` because `dir` is taken by
  `init [DIR]` in the same scope. The `cli_ok` law caught exactly that
  clash while this page was being written.
- **Globals read the same everywhere.** `-C` and `-v` are read once, in
  `decode`, whatever subcommand the user chose: `vcs -v remote rm x` and
  `vcs remote rm x -v` decode alike.
- **Plugins.** Everything after an unknown command name is passed through
  unscanned, so `vcs lint --fix src` hands `["--fix", "src"]` to `vcs-lint`
  even though `vcs` has no `--fix`. Globals before the name are still
  parsed. Because `external()` turns every unknown name into a plugin call,
  the library cannot report a mistyped built-in command; `act` does, with
  `Cli.suggest`, in the same shape as the library's own error.
- **Plugin output.** `Process.run` collects the plugin's output and returns
  it when the plugin exits, so output is not streamed, and the plugin's
  stdin is empty. That suits short, non-interactive plugins.

## `main.bend`

```python
# Purpose: vcs, a git-like tool with nested subcommands, global options and plugins.
# Expected output: one line per command; plugins print their own output.
# Run: bend main.bend -- remote add origin https://example.com/r
import Base
import ./app.bend as App
import cli@1.0.0.0/run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Vcs, ~App.decode, ~App.act, App.cli())
```

## `LAWS.bend`

```python
# Purpose: laws for vcs: the definition is valid, the tree routes, globals merge,
# plugins pass through, and messages are exact.
# Expected output: one TODO per law until PROOF.bend proves them.
# Run: bend LAWS.bend --check-only
import Base
import ./app.bend as App
import cli@1.0.0.0/cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Vcs, ~App.decode, App.cli()) == [] : List<&2, Cli.Problem>}

law remote_rm:
  {Cli.eval(~App.Vcs, ~App.decode, App.cli(), Cli.host(80n),
      ["-C", "repo", "remote", "rm", "origin", "-v"])
    == Cli.Go{App.Vcs{"repo", 1n, App.RemoteRemove{"origin"}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Vcs>}

law bare_remote:
  {Cli.eval(~App.Vcs, ~App.decode, App.cli(), Cli.host(80n), ["remote"])
    == Cli.Go{App.Vcs{".", 0n, App.Remotes{}}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Vcs>}

law plugin:
  {Cli.eval(~App.Vcs, ~App.decode, App.cli(), Cli.host(80n),
      ["-v", "lint", "--fix", "src"])
    == Cli.Go{App.Vcs{".", 1n, App.Plugin{"lint", ["--fix", "src"]}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Vcs>}

law no_message:
  {Cli.eval(~App.Vcs, ~App.decode, App.cli(), Cli.host(80n), ["commit"])
    == Cli.Exit{2, "", "error: the following required arguments were not provided:\n  --message <MSG>\n\nUsage: vcs commit [OPTIONS] --message <MSG>\n\nFor more information, try '--help'.\n"}
    : Cli.Step<App.Vcs>}

law init_here:
  {App.say(0n, ".", App.Init{None{}, False{}})
    == "Initialized empty repository in ." : String}

law add_verbose:
  {App.say(1n, "/src", App.RemoteAdd{"origin", "https://example.com/r", True{}})
    == "in /src: Added remote 'origin' at https://example.com/r\nFetched 'origin'"
    : String}

law two_tips:
  {App.tip(["commit", "remote"])
    == "\n\n  tip: some similar subcommands exist: 'commit', 'remote'" : String}
```

## `PROOF.bend`

```python
# Purpose: proofs of the vcs laws.
# Expected output: ALL PROOFS CHECK
# Run: bend PROOF.bend
import Base
import ./LAWS.bend as Laws

def Laws.cli_ok():
  {==}

def Laws.remote_rm():
  {==}

def Laws.bare_remote():
  {==}

def Laws.plugin():
  {==}

def Laws.no_message():
  {==}

def Laws.init_here():
  {==}

def Laws.add_verbose():
  {==}

def Laws.two_tips():
  {==}
```

## Running it

```console
$ bend main.bend -o vcs
$ ./vcs init --bare
Initialized empty bare repository in .
$ ./vcs -v -C src remote add -f origin https://example.com/r
in src: Added remote 'origin' at https://example.com/r
Fetched 'origin'
$ ./vcs commit -am "Fix typo"
Staged all modified files
[main] Fix typo
$ ./vcs --amend commit -m x
error: unexpected argument '--amend' found

  tip: '--amend' belongs to subcommand 'vcs commit'

Usage: vcs [OPTIONS] <COMMAND>

For more information, try '--help'.
$ ./vcs comit -m x
error: unrecognized subcommand 'comit' (vcs-comit: No such file or directory)

  tip: a similar subcommand exists: 'commit'

For more information, try '--help'.
$ ./vcs completions zsh > ~/.zfunc/_vcs
```

The two errors exit 2. A plugin's exit status becomes `vcs`'s.
