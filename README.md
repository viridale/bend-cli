# bend-cli

`bend-cli` is a command-line interface library for Bend. Declare commands with
usage strings and decode typed arguments; a single definition produces help
text, usage errors with typo suggestions, ANSI color, shell completions, and
man pages. Because parsing and rendering are pure functions, applications can
state and prove their CLI behavior as Bend laws.

The BendHub package is `cli`. Import `cli.bend` in application logic and laws;
import `run.bend` only in the `IO` entry point. Bend 2.0.38 or newer is
required.

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

Create `main.bend` to wire the command into process arguments, terminal
probing, and standard streams:

```python
import Base
import ./app.bend as App
import cli@0.1.0.0/run.bend as Run

def main() -> IO(Unit):
  Run.main(~App.Greeting, ~App.decode, ~App.act, App.cli())
```

Build and run the binary:

```sh
bend main.bend -o hello
./hello Ada          # Hello, Ada!
./hello --help       # full help
```

`-h` prints compact help (the first paragraph of each description); `--help`
prints every paragraph. Usage errors write to stderr and exit with status `2`.
Invalid command definitions and decoder bugs write a `bug:` diagnostic to
stderr and exit with status `70`.

See [`examples/hello`](examples/hello) for this quickstart with its laws and
proofs, [`examples/grep`](examples/grep) for a multi-option command with
environment fallbacks, ANSI color, and file I/O, and
[`examples/argbench`](examples/argbench) for a benchmark CLI with equivalent
implementations in `clap`, `cobra`, `argparse`, and `commander` under
[`bench/peers`](bench/peers) (verified for identical output and timed by
`tools/peerbench.sh`).

## Define commands

`Cli.cmd(name, about, items)` defines a root command. Add `Cli.sub` for
subcommands and `Cli.arg` for options or positionals. An argument's usage
string determines its kind, flags, placeholder, and default ID:

| Usage string | Meaning |
|---|---|
| `-v, --verbose` | Boolean flag |
| `-v, --verbose...` | Occurrence count |
| `--[no-]cache` | Negatable flag |
| `-o, --output <FILE>` | Option with one value |
| `--include <PATH>...` | Repeatable option |
| `--color[=<WHEN>]` | Option with an optional value; requires `Cli.bare(...)` |
| `<INPUT>` / `[OUTPUT]` | Required / optional positional |
| `<FILE>...` / `[FILE]...` | One or more / zero or more positionals |

An argument's ID defaults to its long option name (`"output"`), its short flag
character when no long name is declared (`"v"`), or its lowercased placeholder
name for positionals (`"input"`). Use `Cli.id(...)` to override the derived ID.

Use argument attributes to declare types, value sources, and constraints. For
example, `Cli.as_u32()` validates values during parsing, `Cli.env("PORT")`
reads an environment fallback, `Cli.default("8080")` supplies a default, and
`Cli.one_of(["text", "json"])` restricts accepted values. Values resolve in
precedence order: `argv`, the first set and non-empty variable from one or more
`Cli.env` attributes, and finally `Cli.default`. Relationship constraints
(`Cli.conflicts`, `Cli.requires`, `Cli.exclusive`, and `Cli.need_one`) apply to
values supplied by `argv` or the environment, not to defaults.

Options may appear between positional operands. Short flags cluster (`-abc`),
options accept attached values (`-ofile`, `--output=file`), and a repeated
single-value option retains its last occurrence. Option and subcommand names
match exactly; close misspellings receive suggestions.

Add `Cli.global()` to propagate an option to descendant subcommands. A command
cannot declare both subcommands and positionals. When a command requires a
subcommand (the default unless `Cli.sub_optional()` is set), only its
`Cli.global()` options remain in scope for the subcommand, so lint rejects
`Cli.required()` on its local options.

Decode matched arguments by ID inside a `do Cli.Dec<A>:` block. Use `Cli.flag`
for boolean and negatable flags, `Cli.count` for occurrence counts, and
`Cli.str`, `Cli.nat`, `Cli.u32`, `Cli.f32`, or `Cli.bool` for required or
defaulted single values. Use the `<type>_opt` readers (such as `Cli.str_opt` or
`Cli.u32_opt`) for optional single values and the plural `<type>s` readers
(such as `Cli.strs` or `Cli.u32s`) for repeatable arguments. `Cli.source`
reports whether an argument resolved from `argv`, the environment, a default,
or was omitted (`Cli.Absent{}`). For nested subcommands, `Cli.route` dispatches
to a decoder by space-separated command path.

Add `Cli.version("1.0.0")` for `-V` and `--version`, `Cli.color()` for
`--color`, `Cli.completions()` for `completions <bash|zsh|fish>`, and
`Cli.man()` for a hidden `man [COMMAND]...` subcommand that prints `roff` man
pages. `Cli.eval` handles help, version, completions, and man pages before
invoking the application decoder.

To install generated completions, run `source <(pkg completions bash)` in
bash 4 or newer, save `pkg completions zsh` as `_pkg` in a directory on
`$fpath`, or write `pkg completions fish` to
`~/.config/fish/completions/pkg.fish` in fish 3.3 or newer.

## State and prove CLI behavior

`Cli.eval` takes a command definition, a `Cli.Host` value, and `argv` (excluding
the program name), and returns either `Go{value, term}` or
`Quit{code, out, err}`. Testing parsing or exact rendered output requires no
process I/O.

`Cli.check` validates the command definition and runs the decoder against one
synthesized sample per completable command path to catch mismatched argument
IDs, types, and kinds statically. Because `Cli.check` evaluates one sample per
path, decoders should read all arguments before branching on their values.

`Cli.eval` lints the command definition on every call. To evaluate multiple
`argv` lists against the same command, lint it once with `Cli.linted(c)`, which
returns `Done{l}` or `Fail{problems}` (matching `Cli.problems(c)`), and pass
`l` to `Cli.eval_linted(~A, ~decode, l, h, argv)`. `Cli.eval_linted` returns
the same `Step<A>` result as `Cli.eval` without re-running lint.

For the quickstart application, `LAWS.bend` states both the definition check
and a parsing law:

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

`PROOF.bend` imports those laws and provides one proof definition per law:

```python
import Base
import ./LAWS.bend as Laws

def Laws.cli_ok():
  {==}

def Laws.default_name():
  {==}
```

Run `bend PROOF.bend`, then `bend PROOF.bend --verdict`. A passing proof
verifies only the stated laws; add laws for each parsing rule and golden output
(help text, error diagnostics, completion scripts, and man pages) that forms
part of your CLI contract.

## Output and terminal behavior

Help output wraps to the resolved terminal width, clamped to 40–100 columns.
The `COLUMNS` environment variable takes precedence over the probed TTY width,
which falls back to 80 columns. Color is resolved independently for stdout and
stderr: an explicit `--color=always` or `--color=never` overrides the
environment, followed in precedence order by `NO_COLOR`, `CLICOLOR_FORCE`,
`CLICOLOR`, `TERM=dumb`, and whether that stream is a TTY. Completion scripts
and man pages never include ANSI escape sequences.

`Cli.Term{out_color, err_color, width}` passes the resolved stream color flags
and terminal width to `act(term, value)`. `Run.main` writes help, version,
completion, and man-page output to stdout (exiting `0`) and usage or definition
errors to stderr (exiting `2` or `70`). When `act` runs, `Run.main` exits with
the returned status code (`0`–`255`); a return value above `255` is reported to
stderr as an internal bug and exits `70`.

## Platform notes

- In a native or compiled-JavaScript build, Bend's runtime extracts its own
  options from `+RTS` through `-RTS` (or to the end of `argv` if `-RTS` is
  omitted), as in `hello +RTS --threads 4 -RTS Ada`; native builds also read
  runtime options from `BENDRTS`. The runtime strips `+RTS ... -RTS` blocks
  before passing `argv` to the application. After `--RTS`, all remaining
  arguments reach the application unchanged (so `hello --RTS +RTS` passes
  `+RTS`). Interpreted runs (`bend main.bend -- args`) do not scan `argv` for
  runtime options.
- Run compiled JavaScript under Bun as `bun hello.js -- args`: Bun consumes a
  `--` immediately following the script path, so the delimiter ensures
  subsequent arguments reach the script unchanged.
- Keep `run.bend` and `main.bend` out of `LAWS.bend` and `PROOF.bend` import
  graphs. `run.bend` links foreign host effects (`sys.c` and `sys.js`) to probe
  the terminal, and Bend's proof checker rejects any module whose import graph
  reaches foreign code.
- Display width sums each code point's East Asian Width, except that emoji
  sequences (ZWJ sequences joined with U+200D, skin-tone or VS16 modifiers,
  keycaps, regional indicator flags, and tag sequences) count as 2 columns,
  matching Rust's `unicode-width` 0.2. Terminals that render a sequence at a
  different width may still misalign columns. Invalid UTF-8 in `argv` is
  replaced with U+FFFD, so non-UTF-8 byte sequences in filenames cannot be
  passed unchanged.

CI runs on macOS arm64 and Ubuntu 24.04 x86-64. Native builds require `clang`;
compiled JavaScript requires Bun 1.1 or newer. Windows is outside the 1.x
support scope. CI also tests generated completions in bash 4.4 and 5, zsh, and
fish 3.3 and 4, and lints generated man pages with `mandoc`.

## Upgrading

Package imports pin a four-part version such as `cli@0.1.0.0`. Update the
`cli.bend` and `run.bend` imports together. The first three components follow
SemVer; the fourth increments when identical source is republished with a new
package hash.

Patch releases preserve public signatures and rendered output bytes. Minor
releases may add public definitions or change rendered output; the changelog
records each output diff. Major releases may change public names, types, or
semantics; prior to `1.0.0.0`, minor releases may also include breaking changes.
Re-run application laws after upgrading, especially golden output laws.

## License

MIT. See [LICENSE](LICENSE).
