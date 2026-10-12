# Tutorial

This tutorial builds `greet`, a one-command program, then `notes`, a program
with subcommands. Each chapter adds one idea and shows the exact help and error
output it produces. By the end you will have proved the CLI's behavior with
laws and built native and JavaScript binaries.

You need Bend 2.0.36 or newer (`bend version`) and clang for native builds.
Read `bend guide` first if `do` blocks, `+` and `match` are new to you.

- [1. A first command](#1-a-first-command)
- [2. Flags and options](#2-flags-and-options)
- [3. Positionals](#3-positionals)
- [4. Types and validation](#4-types-and-validation)
- [5. Defaults and the environment](#5-defaults-and-the-environment)
- [6. Subcommands](#6-subcommands)
- [7. Laws: testing and proving the CLI](#7-laws-testing-and-proving-the-cli)
- [8. Shipping](#8-shipping)

## 1. A first command

A bend-cli program is two files. `app.bend` is pure: it defines the command,
a decoder that turns parsed arguments into your own type, and an action.
`main.bend` connects that to the process.

```python
# app.bend
import Base
import cli@1.0.0.0/cli.bend as Cli

type Greeting is Data:
  Greeting{name: String}

def cli() -> Cli.Cmd:
  Cli.cmd("greet", "Print a greeting", [
    Cli.arg("[NAME]", "Who to greet", [Cli.default("world")]),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Greeting):
  do Cli.Dec<Greeting>:
    name : String <- Cli.str(m, "name")
    return Greeting{name}

def act(+t: Cli.Term, g: Greeting) -> IO(U32):
  match g:
    case Greeting{name}:
      do IO<U32>:
        IO.print(("Hello, " ++ name ++ "!" : String))
        return 0
```

```python
# main.bend
import Base
import ./app.bend as App
import cli@1.0.0.0/run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Greeting, ~App.decode, ~App.act, App.cli())
```

The three parts of `app.bend`:

- **`cli()`** describes the interface. `Cli.cmd(name, about, items)` is the
  root command. `Cli.arg(usage, help, attributes)` declares an argument; its
  usage string `[NAME]` *is* the declaration: square brackets make it an
  optional positional. `Cli.default("world")` gives it a value when absent.
- **`decode(m)`** reads values by id. An argument's id comes from its usage
  string: `[NAME]` has id `name`. `Cli.Dec(A)` is a result that is either an
  `A` or a fault, and `do Cli.Dec<A>:` sequences reads.
- **`act(t, value)`** does the work and returns the exit code. `t` describes
  the terminal (color and width) for apps that format their own output.

Build and run:

```console
$ bend main.bend -o greet
$ ./greet
Hello, world!
$ ./greet Ada
Hello, Ada!
```

You already have help:

```console
$ ./greet --help
Print a greeting

Usage: greet [NAME]

Arguments:
  [NAME]      Who to greet [default: world]

Options:
  -h, --help  Print help
```

and errors that go to stderr with exit status 2:

```console
$ ./greet Ada Grace
error: unexpected argument 'Grace' found

Usage: greet [NAME]

For more information, try '--help'.
```

`Run.main` is the only code that touches the process. Everything it decides
comes from `Cli.eval`, a pure function from the command, the host (terminal
and environment) and argv to either "run the app with this value" or "print
this and exit with this code". Chapter 7 uses that to test the CLI without
running it.

## 2. Flags and options

Add a flag and an option:

```python
type Greeting is Data:
  Greeting{name: String, times: U32, shout: Bool}

def cli() -> Cli.Cmd:
  Cli.cmd("greet", "Print a greeting", [
    Cli.arg("-n, --times <N>", "Greet N times", [Cli.as_u32(), Cli.default("1")]),
    Cli.arg("--shout", "Greet in capitals", []),
    Cli.arg("[NAME]", "Who to greet", [Cli.default("world")]),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Greeting):
  do Cli.Dec<Greeting>:
    name : String <- Cli.str(m, "name")
    times : U32 <- Cli.u32(m, "times")
    shout : Bool <- Cli.flag(m, "shout")
    return Greeting{name, times, shout}
```

The usage string decides the kind of argument:

| Usage string | Kind | Read with |
|---|---|---|
| `--shout` | flag: present or not | `Cli.flag` → `Bool` |
| `-n, --times <N>` | option with one value | `Cli.u32` here, because of `Cli.as_u32()` |

An option's id is its long name without dashes (`times`), else its short
letter. `Cli.as_u32()` makes the parser check the value: `Cli.u32` never sees
text that is not a number.

Every common spelling works, and the last occurrence wins, so a shell alias
can set a default that the user overrides:

```console
$ ./greet -n 2 Ada
$ ./greet -n2 Ada
$ ./greet --times=2 Ada
$ ./greet --times 3 Ada --times 2
```

all print `Hello, Ada!` twice. Options may come before, between or after
positionals.

The help page lists options with their defaults:

```console
$ ./greet --help
Print a greeting

Usage: greet [OPTIONS] [NAME]

Arguments:
  [NAME]           Who to greet [default: world]

Options:
  -n, --times <N>  Greet N times [default: 1]
      --shout      Greet in capitals
  -h, --help       Print help
```

The parser reports bad input before your decoder runs:

```console
$ ./greet --times
error: a value is required for '--times <N>' but none was supplied

Usage: greet [OPTIONS] [NAME]

For more information, try '--help'.
$ ./greet --times two
error: invalid value 'two' for '--times <N>': expected a whole number from 0 to 4294967295

Usage: greet [OPTIONS] [NAME]

For more information, try '--help'.
$ ./greet --shuot
error: unexpected argument '--shuot' found

  tip: a similar argument exists: '--shout'

Usage: greet [OPTIONS] [NAME]

For more information, try '--help'.
```

Names match exactly. bend-cli never guesses that `--sh` means `--shout`,
because adding `--show` later would silently change what old command lines
mean; it suggests instead.

More: [flags, counts and `--[no-]` switches](how-to/flags.md),
[options](how-to/options.md).

## 3. Positionals

Greet several people at once. `[NAME]...` takes zero or more values; its
default applies when there are none:

```python
type Greeting is Data:
  Greeting{names: List<&2, String>, times: U32, shout: Bool}

def cli() -> Cli.Cmd:
  Cli.cmd("greet", "Print a greeting", [
    Cli.arg("-n, --times <N>", "Greet N times", [Cli.as_u32(), Cli.default("1")]),
    Cli.arg("--shout", "Greet in capitals", []),
    Cli.arg("[NAME]...", "Who to greet", [Cli.default("world")]),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Greeting):
  do Cli.Dec<Greeting>:
    names : List<&2, String> <- Cli.strs(m, "name")
    times : U32 <- Cli.u32(m, "times")
    shout : Bool <- Cli.flag(m, "shout")
    return Greeting{names, times, shout}
```

The four positional forms:

| Usage | Takes | Absent |
|---|---|---|
| `<NAME>` | exactly one | error |
| `[NAME]` | zero or one | default, else none |
| `<NAME>...` | one or more | error |
| `[NAME]...` | zero or more | default, else `[]` |

A list argument is read with the plural reader, `Cli.strs`. Now the action
builds its text purely and writes it once:

```python
def salute(+word: String, names: List<&2, String>) -> String:
  match names:
    case Nil{}:
      ""
    case name <> rest:
      (word ++ ", " ++ name ++ "!\n" ++ salute(word, rest) : String)

def loud(shout: Bool, text: String) -> String:
  match shout:
    case True{}:
      String.to_upper(text)
    case False{}:
      text

def render(g: Greeting) -> String:
  match g:
    case Greeting{names, times, shout}:
      String.repeat(loud(shout, salute("Hello", names)), U32.to_nat(times))

def act(+t: Cli.Term, g: Greeting) -> IO(U32):
  do IO<U32>:
    IO.write(render(g))
    return 0
```

```console
$ ./greet Ada Grace
Hello, Ada!
Hello, Grace!
```

Keeping `render` pure means laws can check the output too (chapter 7).

To pass a name that starts with `-`, end the options with `--`. The Bend
runtime takes the first `--` for itself, so a built program needs two:

```console
$ ./greet -- -- -dash-
Hello, -dash-!
```

See [Platform notes](concepts/platform.md) for why, and
[Positionals](how-to/positionals.md) for `cp`-style `<SRC>... <DST>`, `-` as
stdin, and arguments that pass through untouched.

## 4. Types and validation

Add a language, chosen from a fixed list and mapped to your own type:

```python
type Lang is Data:
  En{}
  Fr{}
  Es{}

type Greeting is Data:
  Greeting{names: List<&2, String>, times: U32, shout: Bool, lang: Lang}

def cli() -> Cli.Cmd:
  Cli.cmd("greet", "Print a greeting", [
    Cli.arg("-n, --times <N>", "Greet N times", [Cli.as_u32(), Cli.default("1")]),
    Cli.arg("--shout", "Greet in capitals", []),
    Cli.arg("--lang <LANG>", "Language",
      [Cli.one_of(["en", "fr", "es"]), Cli.default("en")]),
    Cli.arg("[NAME]...", "Who to greet", [Cli.default("world")]),
  ])
```

`Cli.choose` reads a `one_of` argument through a table. The table must list
exactly the `one_of` values; `Cli.check` (chapter 7) proves that it does.

```python
def decode(+m: Cli.Matches) -> Cli.Dec(Greeting):
  do Cli.Dec<Greeting>:
    names : List<&2, String> <- Cli.strs(m, "name")
    times : U32 <- Cli.u32(m, "times")
    shout : Bool <- Cli.flag(m, "shout")
    lang : Lang <- Cli.choose(Lang, m, "lang",
      [("en", En{}), ("fr", Fr{}), ("es", Es{})])
    return Greeting{names, times, shout, lang}
```

`render` picks the word from the language:

```python
def salutation(lang: Lang) -> String:
  match lang:
    case En{}:
      "Hello"
    case Fr{}:
      "Bonjour"
    case Es{}:
      "Hola"

def render(g: Greeting) -> String:
  match g:
    case Greeting{names, times, shout, lang}:
      String.repeat(loud(shout, salute(salutation(lang), names)),
        U32.to_nat(times))
```

A wrong value gets a suggestion:

```console
$ ./greet --lang fe
error: invalid value 'fe' for '--lang <LANG>': expected one of 'en', 'fr', 'es'

  tip: a similar value exists: 'fr'

Usage: greet [OPTIONS] [NAME]...

For more information, try '--help'.
```

Rules that the parser cannot express go in the decoder. `--times 0` greets
nobody, so reject it with `Cli.fail`, which produces a usage error (exit 2):

```python
def positive(+times: U32) -> Cli.Dec(U32):
  nonzero(U32.is_eq(times, 0), times)

def nonzero(zero: Bool, times: U32) -> Cli.Dec(U32):
  match zero:
    case True{}:
      Cli.fail(U32, "--times must be at least 1")
    case False{}:
      Cli.Dec.pure(U32, times)
```

Define `nonzero` above `positive` in the file (Bend requires a def above its
first caller), then bind through it in `decode`:

```python
    n : U32 <- Cli.u32(m, "times")
    times : U32 <- positive(n)
```

```console
$ ./greet -n 0
error: --times must be at least 1

Usage: greet [OPTIONS] [NAME]...

For more information, try '--help'.
```

`Cli.fail` is for the user's mistakes. For a mistake in your own program,
such as a branch that should be unreachable, use `Cli.bug`, which exits 70
and says `bug:`.

More: [Typed and restricted values](how-to/values.md),
[Errors and exit codes](how-to/errors.md).

## 5. Defaults and the environment

Let users set their language once in their shell profile:

```python
    Cli.arg("--lang <LANG>", "Language",
      [Cli.one_of(["en", "fr", "es"]), Cli.env("GREET_LANG"), Cli.default("en")]),
```

A value comes from the first source that has one:

1. the command line;
2. the environment variable, if it is set and not empty;
3. the default.

```console
$ GREET_LANG=fr ./greet Ada
Bonjour, Ada!
$ GREET_LANG=fr ./greet --lang es Ada
Hola, Ada!
```

The environment value is checked like a command-line value, and the error
names the variable:

```console
$ GREET_LANG=de ./greet
error: invalid value 'de' for '--lang <LANG>' from environment variable GREET_LANG: expected one of 'en', 'fr', 'es'

Usage: greet [OPTIONS] [NAME]...

For more information, try '--help'.
```

Help names the variable but never shows its value, which could be a secret:

```console
$ ./greet --help
Print a greeting

Usage: greet [OPTIONS] [NAME]...

Arguments:
  [NAME]...          Who to greet [default: world]

Options:
  -n, --times <N>    Greet N times [default: 1]
      --shout        Greet in capitals
      --lang <LANG>  Language [env: GREET_LANG] [default: en] [possible values:
                     en, fr, es]
  -h, --help         Print help
```

`Cli.source(m, "lang")` tells you where a value came from (`Argv{}`, `Env{}`,
`Default{}` or `Absent{}`). That is how an app layers a config file between
the environment and the default: see
[Defaults, environment variables and config files](how-to/sources.md).

## 6. Subcommands

`notes` keeps notes in a file and has two subcommands:

```python
# app.bend
import Base
import cli@1.0.0.0/cli.bend as Cli

type Job is Data:
  Add{text: List<&2, String>}
  Show{last: Maybe<&2, U32>}

type Notes is Data:
  Notes{file: String, job: Job}

def cli() -> Cli.Cmd:
  Cli.cmd("notes", "Keep short notes", [
    Cli.arg("-f, --file <PATH>", "Notes file",
      [Cli.global(), Cli.as_file(), Cli.env("NOTES_FILE"), Cli.default("notes.txt")]),
    Cli.sub("add", "Add a note", [
      Cli.arg("<TEXT>...", "Words of the note", []),
    ]),
    Cli.sub("list", "List notes", [
      Cli.alias("ls"),
      Cli.arg("-n, --last <N>", "Show only the last N notes", [Cli.as_u32()]),
    ]),
  ])

def add(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    text : List<&2, String> <- Cli.strs(m, "text")
    return Add{text}

def show(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    last : Maybe<&2, U32> <- Cli.u32_opt(m, "last")
    return Show{last}

def decode(+m: Cli.Matches) -> Cli.Dec(Notes):
  do Cli.Dec<Notes>:
    file : String <- Cli.str(m, "file")
    job : Job <- Cli.route(Job, m, [("add", add), ("list", show)])
    return Notes{file, job}
```

What is new:

- **`Cli.sub(name, about, items)`** declares a subcommand. Its items are
  arguments, attributes and further subcommands, nested as deep as you like.
- **`Cli.global()`** makes `--file` valid in every subcommand, before or after
  the subcommand name. Non-global options belong to their own command only.
- **`Cli.alias("ls")`** lets users type `notes ls`.
- **`Cli.route`** picks a decoder by command path. Keys are the subcommand
  names from the root, joined by spaces (`"remote add"` for a nested one).
- **`Cli.u32_opt`** reads an option that may be absent as a `Maybe`. Use the
  bare reader (`Cli.u32`) only when the argument always has a value: it has a
  default, is `required()`, or is a required positional.

Help lists the subcommands and adds a `help` subcommand:

```console
$ ./notes --help
Keep short notes

Usage: notes [OPTIONS] <COMMAND>

Commands:
  add                Add a note
  list               List notes [aliases: ls]
  help               Print this message or the help of the given subcommand(s)

Options:
  -f, --file <PATH>  Notes file [env: NOTES_FILE] [default: notes.txt]
  -h, --help         Print help
$ ./notes help list
List notes

Usage: notes list [OPTIONS]

Options:
  -n, --last <N>     Show only the last N notes
  -f, --file <PATH>  Notes file [env: NOTES_FILE] [default: notes.txt]
  -h, --help         Print help
```

Running `notes` with nothing prints the summary help to stderr and exits 2,
because a subcommand is required. Using a subcommand's option on the wrong
command gets a tip:

```console
$ ./notes --last 3 list
error: unexpected argument '--last' found

  tip: '--last' belongs to subcommand 'notes list'

Usage: notes [OPTIONS] <COMMAND>

For more information, try '--help'.
```

A command has either positionals or subcommands, never both: `notes add`
takes words, `notes` takes a subcommand. The definition check in the next
chapter reports a command that mixes them.

More: [Subcommands](how-to/subcommands.md), [Wrapping other
programs](how-to/wrappers.md), and the [git-like cookbook
entry](cookbook/git.md).

## 7. Laws: testing and proving the CLI

Because `Cli.eval` is pure, a test is a law: an equation that Bend checks.
Put the laws in `LAWS.bend` and their proofs in `PROOF.bend`. Laws import the
app module, never `main.bend`, which uses host effects.

```python
# LAWS.bend
import Base
import ./app.bend as App
import cli@1.0.0.0/cli.bend as Cli

# The definition is valid and the decoder never raises a bug.
law cli_ok:
  {Cli.check(~App.Greeting, ~App.decode, App.cli()) == []
    : List<&2, Cli.Problem>}

# No arguments: one greeting for "world", in English.
law no_args:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), [])
    == Cli.Go{App.Greeting{["world"], 1, False{}, App.En{}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Greeting>}

# The environment sets the language.
law env_lang:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(),
      Cli.host_var(Cli.host(80n), "GREET_LANG", "fr"), ["Ada"])
    == Cli.Go{App.Greeting{["Ada"], 1, False{}, App.Fr{}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Greeting>}

# --times 0 is a usage error with this exact text.
law zero_times:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), ["-n", "0"])
    == Cli.Exit{2, "", "error: --times must be at least 1\n\nUsage: greet [OPTIONS] [NAME]...\n\nFor more information, try '--help'.\n"}
    : Cli.Step<App.Greeting>}

# The action's text, without running it.
law shout_twice:
  {App.render(App.Greeting{["Ada"], 2, True{}, App.En{}})
    == "HELLO, ADA!\nHELLO, ADA!\n" : String}
```

```python
# PROOF.bend
import Base
import ./LAWS.bend as Laws

def Laws.cli_ok():
  {==}

def Laws.no_args():
  {==}

def Laws.env_lang():
  {==}

def Laws.zero_times():
  {==}

def Laws.shout_twice():
  {==}
```

```console
$ bend PROOF.bend
ALL PROOFS CHECK
$ bend PROOF.bend --verdict
ALL PROOFS CHECK
```

Each proof is `{==}`: Bend runs both sides and compares them. If a law is
false, the check prints both sides, so a changed help page shows you the
exact new text.

`Cli.check` is the most valuable law. It finds every mistake in the
definition (duplicate names, a default that does not parse, a `choose` table
that does not match its `one_of`, a reader used on the wrong kind of
argument, a `route` table missing a command) and runs the decoder once per
command path to make sure it never raises a bug. Without the law, those
mistakes surface at run time as exit 70.

`Cli.host(80n)` is a terminal 80 columns wide with no environment and no
TTY. Add variables with `Cli.host_var` and TTYs with `Cli.host_tty` to test
color and environment fallbacks.

More: [Testing and proving a CLI](how-to/testing.md).

## 8. Shipping

### Version and color

```python
def cli() -> Cli.Cmd:
  Cli.cmd("greet", "Print a greeting", [
    Cli.version("1.0.0"),
    Cli.arg("-n, --times <N>", "Greet N times", [Cli.as_u32(), Cli.default("1")]),
    Cli.arg("--shout", "Greet in capitals", []),
    Cli.arg("--lang <LANG>", "Language",
      [Cli.one_of(["en", "fr", "es"]), Cli.env("GREET_LANG"), Cli.default("en")]),
    Cli.color(),
    Cli.arg("[NAME]...", "Who to greet", [Cli.default("world")]),
  ])
```

`Cli.version` adds `-V, --version`. `Cli.color()` adds `--color <WHEN>`. Help
and errors are colored on a terminal unless `NO_COLOR` is set; `act` gets the
decision in `t` for its own output.

```console
$ ./greet --version
greet 1.0.0
$ ./greet --help
Print a greeting

Usage: greet [OPTIONS] [NAME]...

Arguments:
  [NAME]...           Who to greet [default: world]

Options:
  -n, --times <N>     Greet N times [default: 1]
      --shout         Greet in capitals
      --lang <LANG>   Language [env: GREET_LANG] [default: en] [possible values:
                      en, fr, es]
      --color <WHEN>  When to use color [default: auto] [possible values: auto,
                      always, never]
  -h, --help          Print help
  -V, --version       Print version
```

### Completions and man pages

`Cli.completions()` and `Cli.man()` add the subcommands `completions` and
`man`, so they fit apps that already have subcommands. Add them to `notes`:

```python
    Cli.completions(),
    Cli.man(),
```

```console
$ source <(./notes completions bash)
$ ./notes completions zsh > ~/.zsh/completions/_notes
$ ./notes completions fish > ~/.config/fish/completions/notes.fish
$ ./notes man | man -l -
$ ./notes man list | man -l -
```

For a one-command app like `greet`, see
[Shell completions](how-to/completions.md#apps-without-subcommands).

### Builds

```console
$ bend main.bend -o greet        # native binary
$ bend main.bend -o greet.js     # JavaScript; run with: bun greet.js
$ bend main.bend -- --shout Ada  # run from source, without building
```

When running from source, put `--` before the program's arguments: `bend`
rejects options that come before it. Output is identical in all three modes.

That is the whole library. Next:

- the [how-to guides](README.md#how-to-guides) for specific jobs;
- the [cookbook](README.md#cookbook) for complete programs;
- the [reference](README.md#reference) for every rule and message.
