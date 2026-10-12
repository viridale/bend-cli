# Architecture: a pure core and a thin shell

bend-cli is two files. `cli.bend` makes every decision and is pure, so laws
can prove its behavior. `run.bend` does the IO: it reads the process
environment, calls `cli.bend`, writes the output and exits. Your app is split
the same way.

```
argv, env, tty ─► Run.host ─► Cli.Host ─► Cli.eval ─► Step ─┬─ Exit{code, out, err} ─► write; exit
                                             │              └─ Go{value, term} ─► act(term, value) ─► exit
                                             ▼
          Cmd ─► lint ─► scope ─► scan ─► resolve ─► Matches ─► decode ─► A
                                   └─► render: help · usage · error · version · script · roff
```

## Why the split

Bend's proof checker refuses a law if anything it imports reaches foreign
code or `@unsafe`. Probing the terminal and exiting quietly need host effects
(small C and JavaScript functions), so the code that uses them cannot sit in
the import graph of any law.

The library therefore puts everything that can be decided without the
outside world in `cli.bend`, which imports only Base:

- parsing argv, assigning positionals, applying env and defaults;
- the relations: required, conflicts, requires, groups;
- running your decoder;
- rendering help, errors, version text, completion scripts and man pages;
- choosing color and line width from the facts in a `Cli.Host`.

`Cli.eval` takes those facts as a plain value. A law can build any host it
likes with `Cli.host`, `Cli.host_var` and `Cli.host_tty` and state exactly
what the program prints, byte for byte.

`run.bend` is short. `Run.host` reads the variables `Cli.vars(c)` names,
asks whether stdout and stderr are terminals, and finds the width.
`Run.main` passes that to `Cli.eval`, then either writes an `Exit` and exits
or calls your `act` with the decoded value.

## Your app

| File | Imports | Holds | Laws may import it |
|---|---|---|---|
| `app.bend` | `cli.bend`, Base | the definition `cli()`, the type it decodes to, `decode`, `act` | yes |
| `main.bend` | `app.bend`, `run.bend` | `main`, one call to `Run.main` | no |
| `LAWS.bend` | `app.bend`, `cli.bend` | the laws | — |
| `PROOF.bend` | `LAWS.bend` | one proof def per law | — |

`act` lives in `app.bend` and may use Base IO: reading files, printing,
spawning processes. Base IO does not block proofs; only foreign code does.
Laws simply do not call `act`. Keep the decisions `act` makes in pure
functions next to it, so laws can reach them too ([Testing](../how-to/testing.md)).

## Two phases

Parsing is split into two phases with different jobs.

1. **Matching** turns argv into `Cli.Matches` using only the definition. It
   knows names, arity, value types, sources and relations, and it produces
   every library error message. Help, completions and man pages are derived
   from the same definition, so they cannot drift from what the parser
   accepts.
2. **Decoding** is your function from `Matches` to your own type, written as a
   `do Cli.Dec<A>:` block. It reads typed values by id, maps strings to
   your types, and rejects combinations the definition cannot express with
   `Cli.fail` (a usage error, exit 2). `Cli.bug` reports a defect in your
   code (exit 70).

The definition is data, not a type derived from your record, because Bend
has no derive or reflection. `Cli.check` closes the gap: one law,
`{Cli.check(~A, ~decode, cli()) == []}`, proves that every name, usage string,
default and reference in the definition is valid, and that the decoder never
raises `Cli.bug` on a sample of each command path. The check runs once, at
proof time, not each time the program starts.

## What `eval` returns

```python
type Step<-A: Type> is Type:
  Go{value: A, term: Term}
  Exit{code: U32, out: String, err: String}
```

`Exit` covers everything the library prints itself: help, version, errors,
completion scripts and man pages. `Go` carries your decoded value and a
`Term`, which says whether each stream should be colored and how wide the
terminal is. `act` uses the `Term` to style its own output the same way the
library does ([Terminal output](../how-to/terminal.md)).

## Inside `cli.bend`

The file is laid out in layers, each using only the ones above it:

| Section | Job |
|---|---|
| `Text` | display width, wrapping, styled segments, `paint`, `strip` |
| model | `Item`, `Cmd`, the builders |
| `Usage` | the usage-string parser |
| `Lint` | definition problems |
| `Scope` | per-command name tables |
| `Scan` | tokens to occurrences |
| `Resolve` | env, defaults, positionals, relations |
| `Get` | readers and `route` |
| `Render` | help, usage, errors, version |
| `Comp` | completion scripts |
| `Roff` | man pages |
| `Eval` | the whole pipeline |
| `Check` | `check` and the decoder samples |

argv, occurrences and help segments are lists walked once; name tables are
`Map`s. Command lines are tens of tokens, so nothing runs in parallel: fork
overhead would exceed the work.

## Same output everywhere

`eval` depends only on the definition, the host and argv. A native build,
compiled JavaScript and `bend main.bend` print the same bytes for the same
input, and a law about `eval` holds for all three.
