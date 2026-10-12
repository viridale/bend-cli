# API

The names on this page are the public API. Everything else in `cli.bend`
and `run.bend` is internal and may change in any release.

```python
import cli@1.0.0.0/cli.bend as Cli    # pure; app modules and laws
import cli@1.0.0.0/run.bend as Run    # IO; main.bend only
```

## `cli.bend`: types

```python
type Term is Data:
  Term{out_color: Bool, err_color: Bool, width: Nat}   # width: host width, unclamped

type Step<-A: Type> is Type:
  Go{value: A, term: Term}                     # decoded: run the app
  Exit{code: U32, out: String, err: String}    # write out, write err, exit with code

type Fault is Data:
  Bug{msg: String}       # a defect in the definition or decoder: exit 70
  Usage{msg: String}     # a user error found while decoding: exit 2

type Src is Data:
  Argv{}
  Env{}
  Default{}
  Absent{}

type Shell is Data:
  Bash{}
  Zsh{}
  Fish{}

type Style is Data:
  Bold{}
  Dim{}
  Under{}
  Red{}
  Green{}
  Yellow{}
  Blue{}
  Magenta{}
  Cyan{}

def Dec(-A: Type) -> Type:
  Result<&2, &1, Fault, A>
```

Opaque types: `Cmd` (a root command), `Item` (an argument, subcommand or
attribute), `Matches` (a successful parse), `Host` (process facts).
`Problem` is listed in [Messages](messages.md#definition-problems).

## Declaring

```python
cmd(name: String, about: String, items: List<&2, Item>) -> Cmd
sub(name: String, about: String, items: List<&2, Item>) -> Item
arg(usage: String, help: String, items: List<&2, Item>) -> Item
```

Attribute builders are listed in [Attributes](attributes.md). Usage strings
are described in [Usage strings](usage-strings.md).

## Reading

Every reader, `choose`, `choose_opt`, `route`, `path`, `external_args`,
`fail`, `bug`, `keep` and `suggest` is in [Readers](readers.md).

## Running and checking

```python
eval(~A: Type, ~decode: @+m: Matches -> Dec(A), c: Cmd, h: Host,
     argv: List<&2, String>) -> Step<A>
check(~A: Type, ~decode: @+m: Matches -> Dec(A), c: Cmd) -> List<&2, Problem>
problems(c: Cmd) -> List<&2, Problem>
```

- `eval`: the whole CLI. `argv` excludes the program name; the program's
  display name is always the root command's name.
- `check`: `problems(c)`, then a `DecodeBug` for each `Bug` the decoder
  raises on the sample of each runnable command path.
- `problems`: definition problems only, without running the decoder.

Callbacks have these exact forms:

```python
def decode(+m: Cli.Matches) -> Cli.Dec(A)
def act(+t: Cli.Term, a: A) -> IO(U32)
```

The `+` is part of the type. A def with `m` instead of `+m` does not fit;
change the parameter or pass a lambda.

## Host and rendering

```python
host(width: Nat) -> Host                            # no variables, no TTYs
host_var(h: Host, name: String, value: String) -> Host
host_tty(h: Host, out: Bool, err: Bool) -> Host
vars(c: Cmd) -> List<&2, String>   # env names c reads, then NO_COLOR CLICOLOR CLICOLOR_FORCE TERM COLUMNS

help(c: Cmd, path: List<&2, String>, long: Bool, h: Host) -> String
usage(c: Cmd, path: List<&2, String>) -> String     # the text after "Usage: "
script(c: Cmd, s: Shell) -> String                  # a completion script
roff(c: Cmd, path: List<&2, String>) -> String      # a man page

paint(on: Bool, styles: List<&2, Style>, text: String) -> String
strip(text: String) -> String                       # removes SGR escape sequences
width(text: String) -> Nat                          # display columns
wrap(text: String, cols: Nat) -> String             # greedy wrap, keeps indentation
```

`help`, `usage` and `roff` render the longest valid prefix of `path`.

## `run.bend`

```python
main(~A: Type, ~decode: @+m: Cli.Matches -> Cli.Dec(A),
     ~act: @+t: Cli.Term -> A -> IO(U32), c: Cli.Cmd) -> IO(Unit)
host(c: Cli.Cmd) -> IO(Cli.Host)
exit(code: U32) -> IO(Unit)
```

`Run.main`:

1. reads argv without the program name, and the host with `Run.host`;
2. evaluates `Cli.eval`;
3. on `Exit{code, out, err}`, writes `out` to stdout and `err` to stderr,
   then exits with `code`;
4. on `Go{a, t}`, runs `act(t, a)` and exits with its result; a result above
   255 prints `bug: exit code <n> is out of range 0..255` and exits 70.

Exit 0 returns normally, so work started with `IO.fork` can finish. Any
other code ends the process at once.

`Run.host(c)` reads each variable in `Cli.vars(c)`, whether stdout and stderr
are terminals, and the width (`COLUMNS`, else the terminal, else 80).

`Run.exit(0)` returns; any other code flushes output and exits.
