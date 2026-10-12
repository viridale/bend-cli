# Color and terminal width

## Color

Help and version output (stdout) and errors (stderr) are colored separately,
each by the first rule that applies:

| # | Condition | Color |
|---|---|---|
| 1 | the last `--color` before `--` is `always` | on |
| 2 | the last `--color` before `--` is `never` | off |
| 3 | `NO_COLOR` is set and not empty | off |
| 4 | `CLICOLOR_FORCE` is set, not empty and not `0` | on |
| 5 | `CLICOLOR` is `0` | off |
| 6 | `TERM` is `dumb` | off |
| 7 | otherwise | on if that stream is a terminal |

Rules 1 and 2 need `Cli.color()` in the definition:

```python
Cli.cmd("app", "…", [Cli.color(), ...])
```

which declares `--color <WHEN>` with values `auto`, `always`, `never`,
default `auto`, as a global option. `--color` is read before anything else,
so `app --color=never --bogus` prints an uncolored error.

Completion scripts and man pages are never colored.

## Coloring your own output

`act` receives a `Cli.Term` with the decisions already made:

```python
type Term is Data:
  Term{out_color: Bool, err_color: Bool, width: Nat}
```

Pass the flag for the stream you write to into `Cli.paint`:

```python
def done(t: Cli.Term) -> IO(U32):
  match t:
    case Cli.Term{out_color, err_color, width}:
      do IO<U32>:
        IO.print(Cli.paint(out_color, [Cli.Bold{}, Cli.Green{}], "done"))
        return 0
```

`Cli.paint(False{}, styles, s)` returns `s` unchanged, so no branch is needed.
Styles are `Bold`, `Dim`, `Under`, `Red`, `Green`, `Yellow`, `Blue`,
`Magenta` and `Cyan`; several combine into one escape sequence. `Cli.strip`
removes escape sequences, for example before measuring.

Your output then follows `--color`, `NO_COLOR` and the rest exactly as the
library's does.

## Width

`Term.width` is the terminal width, unclamped:

1. `COLUMNS`, if it is a whole number of at least 1;
2. otherwise the width of stdout, if it is a terminal;
3. otherwise the width of stderr, if it is a terminal;
4. otherwise 80.

Library help wraps to that width clamped to 40–100 columns. For your own
text:

```python
Cli.wrap(text, cols)   # greedy wrapping, keeping leading indentation
Cli.width(text)        # display columns: East Asian wide characters count 2
```

`Cli.width` counts per code point, so emoji joined with zero-width joiners
and flag pairs can measure wrong.

## Testing color and width

`Cli.host(width)` is a host with no terminals and no variables. Build the
situation you want to test:

```python
Cli.host_tty(Cli.host(120n), True{}, False{})           # stdout is a terminal
Cli.host_var(Cli.host(80n), "NO_COLOR", "1")            # NO_COLOR set
```

A law over `Cli.eval` with such a host pins the exact escape bytes of help or
errors. The library itself proves that `NO_COLOR` always turns color off
unless `--color` is given, and that `--color=never` always does.
