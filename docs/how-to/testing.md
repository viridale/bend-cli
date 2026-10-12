# Testing and proving a CLI

`Cli.eval` is the whole command line as a pure function:

```python
Cli.eval(~A, ~decode, cli(), host, argv) -> Cli.Step<A>
```

It returns `Cli.Go{value, term}` when your action should run, or
`Cli.Exit{code, out, err}` with the exact bytes the program would print. A
test is therefore a law: an equation in `LAWS.bend`, proved in `PROOF.bend`,
checked by `bend PROOF.bend`. No process, no captured output, no flakiness.

## Layout

```
app.bend      the definition, decoder, act (pure; laws import it)
main.bend     Run.main only (host effects; laws must not import it)
LAWS.bend     imports app.bend and cli.bend; states the laws
PROOF.bend    imports LAWS.bend; one def per law
```

```console
$ bend PROOF.bend
ALL PROOFS CHECK
$ bend PROOF.bend --verdict      # recheck with Bend's verified kernel
ALL PROOFS CHECK
```

Run both in CI. A law with no proof is an open claim and fails the check.

## The definition check

Every app should have this law:

```python
law cli_ok:
  {Cli.check(~App.Action, ~App.decode, App.cli()) == [] : List<&2, Cli.Problem>}
```

```python
def Laws.cli_ok():
  {==}
```

`Cli.check` returns every problem in the definition, then runs the decoder on
one sample of each command path that can run and reports each `Cli.bug` it
hits. It catches:

- malformed usage strings, with the column of the first bad character;
- duplicate names, ids and aliases in a scope, and collisions with `--help`;
- attributes in the wrong place, two value types on one argument;
- missing help text;
- defaults that do not convert;
- `conflicts`/`requires` naming nothing, groups without rules;
- bad positional orders, positionals mixed with subcommands;
- reading an id that does not exist, or with the wrong reader (`Cli.str` on a
  count, a bare reader on an argument that may be absent);
- a `choose` table that does not match its `one_of`;
- a `route` table missing a runnable path or naming a non-command.

When it fails, the checker prints the problem list, for example
`[Cli.Dup{"pkg add", "--dev"}]`. The [Messages
reference](../reference/messages.md#definition-problems) explains each kind.

What it cannot catch: a sample sets every argument to one value (its default,
first choice, or `0`/`""`), so a read that happens only for *other* values is
not exercised. Read every argument at the top of the decoder, then branch.

## Golden parses

Fix argv and state the decoded value:

```python
law shout_twice:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), ["-n", "2", "--shout", "Ada"])
    == Cli.Go{App.Greeting{["Ada"], 2, True{}, App.En{}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Greeting>}
```

Cover the cases your users rely on: defaults, each subcommand, environment
fallbacks, globals before and after the subcommand, `--` handling.

## Golden errors

```python
law typo:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), ["--shuot"])
    == Cli.Exit{2, "", "error: unexpected argument '--shuot' found\n\n  tip: a similar argument exists: '--shout'\n\nUsage: greet [OPTIONS] [NAME]...\n\nFor more information, try '--help'.\n"}
    : Cli.Step<App.Greeting>}
```

## Golden help pages

```python
law help_short:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(), Cli.host(80n), ["-h"])
    == Cli.Exit{0, "Print a greeting\n\nUsage: greet [OPTIONS] [NAME]...\n\nArguments:\n  [NAME]...           Who to greet [default: world]\n\nOptions:\n  -n, --times <N>     Greet N times [default: 1]\n      --shout         Greet in capitals\n      --lang <LANG>   Language [env: GREET_LANG] [default: en] [possible values:\n                      en, fr, es]\n      --color <WHEN>  When to use color [default: auto] [possible values: auto,\n                      always, never]\n  -h, --help          Print help\n  -V, --version       Print version\n", ""}
    : Cli.Step<App.Greeting>}
```

or call `Cli.help(c, path, long, host)` directly. A help page is part of your
interface; a golden law makes every change to it deliberate. When a law
fails, the checker prints both sides, so copy the new text in after reviewing
it.

Pin pages at the widths your users see (`Cli.host(80n)`), and add one narrow
(`40n`) and one wide (`120n`) page if your help has long names.

## Hosts

| Host | Use |
|---|---|
| `Cli.host(80n)` | 80 columns, no terminal, no variables |
| `Cli.host_var(h, "NAME", "value")` | add an environment variable |
| `Cli.host_tty(h, out, err)` | mark stdout and/or stderr as terminals (turns color on) |

```python
law env_lang:
  {Cli.eval(~App.Greeting, ~App.decode, App.cli(),
      Cli.host_var(Cli.host(80n), "GREET_LANG", "fr"), [])
    == Cli.Go{App.Greeting{["world"], 1, False{}, App.Fr{}},
              Cli.Term{False{}, False{}, 80n}}
    : Cli.Step<App.Greeting>}
```

## Testing what `act` prints

`act` performs IO, so laws cannot run it. Split it: a pure function
computes the output and exit code, and `act` only writes them.

```python
type Out is Data:
  Out{code: U32, out: String, err: String}

def plan(+t: Cli.Term, a: Action) -> Out:
  ...   # all decisions here

def act(+t: Cli.Term, a: Action) -> IO(U32):
  emit(plan(t, a))
```

with `emit` writing `out` and `err` and returning `code`. Laws then pin
`plan`. Actions that read files can take the file contents as an argument to
the pure part, read by the thin IO layer.

## Universal laws

A golden law fixes one input. A universal law quantifies over inputs with
`for`, and its proof is an induction you write. The library already proves its universal properties for every definition
and input: `NO_COLOR` and `--color=never` turn color off, exit codes are only
0, 2 or 70, usage errors never write stdout, `--` ends options, wrapped lines
fit, and completion quoting round-trips. Your own universal laws are most
useful over your pure functions (`plan`, `render`, config layering), where
the induction is yours to write.

## End-to-end tests

Keep a few process-level tests for what laws cannot see: the binary's real
exit status, stream routing, and runtime behavior around `--`. Run the built
program with `Process.run` and compare status, stdout and stderr exactly;
the library's own `tests/e2e.bend` runs each case natively, as compiled
JavaScript and from source.

## A checklist

- `cli_ok` law;
- one golden parse per subcommand, plus defaults and env fallbacks;
- golden `-h` and `--help` for the root and each subcommand you document;
- golden errors for the mistakes users actually make;
- laws over your pure `plan`;
- `bend PROOF.bend --verdict` in CI.
