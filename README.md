# bend-cli

`bend-cli` is a command-line library for Bend. Declare commands with usage
strings, decode typed values, and get help, errors, suggestions, color, shell
completions, and man pages from one definition. Parsing and rendering are pure
functions, so applications can state their CLI behavior as Bend laws.

The BendHub package is `cli`. Import `cli.bend` in application code and laws;
import `run.bend` only in the executable shell. Bend 2.0.36 or newer is required.

## Quickstart

Create `app.bend` with the command definition, decoder, and action:

```python
import Base
import cli@0.1.0.0/cli.bend as Cli

type Greeting is Data:
  Greeting{name: String}

def cli() -> Cli.Cmd:
  Cli.cmd("hello", "Print a greeting", [
    Cli.arg("[NAME]", "Who to greet", [Cli.default("world")]),
  ])

def decode(+m: Cli.Matches) -> Cli.Dec(Greeting):
  do Cli.Dec<Greeting>:
    name : String <- Cli.str(m, "name")
    return Greeting{name}

def act(+t: Cli.Term, greeting: Greeting) -> IO(U32):
  match greeting:
    case Greeting{name}:
      do IO<U32>:
        IO.print(("Hello, " ++ name ++ "!" : String))
        return 0
```

Create `main.bend` to connect the app to process arguments and output:

```python
import Base
import ./app.bend as App
import cli@0.1.0.0/run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Greeting, ~App.decode, ~App.act, App.cli())
```

Build and run it:

```sh
bend main.bend -o hello
./hello Ada          # Hello, Ada!
./hello --help       # full help
```

`-h` shows a summary; `--help` shows every help paragraph. Usage errors go
to stderr and exit 2. Invalid command definitions and decoder bugs exit 70.

[`examples/hello`](examples/hello) is this quickstart with its laws and
proofs. [`examples/grep`](examples/grep) adds options, an environment
fallback, color, and file reads, with laws for its parsing and output.

## Define commands

`Cli.cmd(name, about, items)` defines a root command. Add `Cli.sub` for
subcommands and `Cli.arg` for options or positionals. An argument's usage
string is its declaration:

| Usage string | Meaning |
|---|---|
| `-v, --verbose` | Boolean flag |
| `-v, --verbose...` | Occurrence count |
| `--[no-]cache` | Negatable flag |
| `-o, --output <FILE>` | Option with one value |
| `--include <PATH>...` | Repeatable option |
| `--color[=<WHEN>]` | Optional value; requires `Cli.bare(...)` |
| `<INPUT>` / `[OUTPUT]` | Required / optional positional |
| `<FILE>...` / `[FILE]...` | One or more / zero or more positionals |

Use argument attributes to add types, sources, and constraints. For example,
`Cli.as_u32()` checks a value while parsing; `Cli.env("PORT")` supplies an
environment fallback; `Cli.default("8080")` supplies a default; and
`Cli.one_of(["text", "json"])` limits accepted values. Argument values come
from argv first, then a nonempty environment value, then a default. Relations
such as `Cli.conflicts`, `Cli.requires`, `Cli.exclusive`, and
`Cli.need_one` apply to values supplied by argv or the environment.

Options may appear between operands. Short flags cluster (`-abc`), options
accept attached values (`-ofile`, `--output=file`), and a repeated
single-value option uses its last occurrence. Names match exactly;
misspellings receive suggestions. Add `Cli.global()` to recognize an option
in descendant commands. Commands with subcommands do not also take positionals.

Read values by id in a `do Cli.Dec<A>:` block. Use `Cli.flag` for flags,
`Cli.count` for count flags, and `Cli.str`, `Cli.nat`, `Cli.u32`,
`Cli.f32`, or `Cli.bool` for required or defaulted single values. Use
the corresponding `_opt` reader for a value that may be absent and the
plural reader (`Cli.strs`, `Cli.u32s`, and so on) for repeated values.
`Cli.source` reports whether a value came from argv, the environment, a
default, or nowhere. For nested commands, `Cli.route` dispatches a decoder
by command path.

Add `Cli.version("1.0.0")` for `-V` and `--version`,
`Cli.color()` for `--color`, `Cli.completions()` for bash, zsh, and
fish scripts, and `Cli.man()` for man pages. `Cli.eval` handles help,
version, completions, and man pages before invoking the app decoder.

To install generated completions, run `source <(pkg completions bash)` in
bash 4 or newer, save `pkg completions zsh` as `_pkg` in a directory on
`$fpath`, or write `pkg completions fish` to
`~/.config/fish/completions/pkg.fish` in fish 3.3 or newer. Add
`Cli.man()` to make `pkg man` print a man page; pass a subcommand path for
its page.

## State and prove CLI behavior

`Cli.eval` takes a command, a host value, and argv without the program name;
it returns either `Go{value, term}` or `Quit{code, out, err}`. No process IO
is needed to test parsing or exact output. `Cli.check` checks the command
definition and exercises the decoder on one sample per completable command
path.

`Cli.eval` lints the command on every call. To evaluate many argvs against
one command, lint it once with `Cli.linted(c)`, which returns `Done{l}` or
`Fail{problems}` with the problems `Cli.problems(c)` lists, then call
`Cli.eval_linted(~A, ~decode, l, h, argv)` for each argv. It answers as
`Cli.eval` does without linting again.

For the quickstart app, `LAWS.bend` can state both its definition check and
a parsing case:

```python
import Base
import ./app.bend as App
import cli@0.1.0.0/cli.bend as Cli

law cli_ok:
  {Cli.check(~App.Greeting, ~App.decode, App.cli()) == []
    : List<&2, Cli.Problem>}

law default_name:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), [])
    == Cli.Go{App.Greeting{"world"}, Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Greeting>}
```

`PROOF.bend` imports those laws and supplies one proof def for each:

```python
import Base
import ./LAWS.bend as Laws

def Laws.cli_ok():
  {==}

def Laws.default_name():
  {==}
```

Run `bend PROOF.bend`, then `bend PROOF.bend --verdict`. Keep golden laws
for help, errors, scripts, and man pages when those output bytes are part of
your app's interface. A passing proof covers the laws you stated; add cases
for behavior that matters to your users. `Cli.check` uses one sample per
command path, so decoders should read every argument before branching on
values.

## Output and terminal behavior

Help wraps to the terminal width, clamped to 40–100 columns. The `COLUMNS`
environment variable takes precedence over the terminal probe. Color is
decided separately for stdout and stderr: an explicit `--color=always` or
`--color=never` wins, then `NO_COLOR`, `CLICOLOR_FORCE`,
`CLICOLOR`, `TERM=dumb`, and finally whether that stream is a TTY.
Completions and man pages have no ANSI styling.

Applications choose their own output in `act(term, value)`. The shell
returns an action's exit code from 0 through 255; a code above 255 is an
internal error and exits 70. The library writes help and version output to
stdout and usage errors to stderr.

## Platform notes

- Bend's runtime consumes the first `--`. In a native or
  compiled-JavaScript app, use `hello -- -- -x` to pass `-x` as a
  positional value after the CLI's end-of-options marker. In development
  mode, use `bend main.bend -- -- -x`.
- Native Bend consumes `--threads N`, `--gpu V`, `--gpu-build`,
  and `--bend-help` before the app sees argv. Compiled JavaScript also
  consumes `--threads N`, `--gpu V`, and `--bend-help`. Do not use
  these as app options or values on those targets.
- The app module can be imported by laws. Keep the executable shell out of
  their import graph: terminal probing and exit are host effects.
- Display width counts Unicode code points. Emoji joined with U+200D and
  flags can align imperfectly. Invalid UTF-8 in argv becomes U+FFFD, so
  raw-byte filenames cannot be passed unchanged.
- Until a Bend release includes
  [bendlang/bend#1470](https://github.com/bendlang/bend/pull/1470), a closed
  stdout pipe (`hello | head -1`) produces Bend's short-write diagnostic and
  exits 1. With that fix, the program ends by SIGPIPE.

CI runs on macOS arm64 and Ubuntu 24.04 x86-64. Native builds need clang;
compiled JavaScript uses Bun 1.1 or newer. Windows is outside the 1.x support
scope. CI also completes in bash 4.4 and 5, zsh, fish 3.3 and 4, and lints
the man pages with mandoc.

## Upgrading

Package imports pin a four-part version such as `cli@0.1.0.0`. Update both
the pure and shell imports together. The first three parts follow SemVer; the
last part records a republish of the same source with a changed package hash.

Patch releases preserve public signatures and output bytes. Minor releases
may add API or change rendered output; the changelog lists each output change
with its previous and new form. Major releases may change public names, types,
or semantics; until 1.0, minor releases may too. Re-run app laws after an upgrade, especially golden output laws.

## License

MIT. See [LICENSE](LICENSE).
