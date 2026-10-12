# Wrapping other programs

Two attributes hand tokens through untouched:

| Attribute | Goes on | Effect |
|---|---|---|
| `Cli.rest()` | the last positional, which must be variadic | from its first value on, every token is a value, including `--` and things that look like options |
| `Cli.external()` | a command with subcommands | an unknown subcommand name, and every token after it, is kept for you |

## Run a command with its own arguments: `rest()`

Give the program and its arguments one variadic slot with `rest()`:

```python
def cli() -> Cli.Cmd:
  Cli.cmd("retry", "Run a command until it succeeds", [
    Cli.arg("-n, --times <N>", "Give up after N attempts", [Cli.as_u32(), Cli.default("3")]),
    Cli.arg("<COMMAND>...", "The program to run, then its arguments", [Cli.rest()]),
  ])
```

```console
$ retry -n 5 curl -fsS --retry 0 https://example.com
```

gives `times = 5` and
`command = ["curl", "-fsS", "--retry", "0", "https://example.com"]`. The
program name is the slot's first value, so from there on every token is a
value: `-n` after `curl` belongs to `curl`, and so do `--help` and `--`.
Options for `retry` itself go before the program name.

Split the list in the decoder. `<COMMAND>...` is required, so the empty case
cannot happen at run time, but `Cli.check` may sample it, so answer it with
`Cli.fail` rather than `Cli.bug`:

```python
type Call is Data:
  Call{program: String, args: List<&2, String>}

def call(command: List<&2, String>) -> Cli.Dec(Call):
  match command:
    case Nil{}:
      Cli.fail(Call, "a command is required")
    case program <> args:
      Cli.Dec.pure(Call, Call{program, args})
```

Avoid a separate `<COMMAND>` slot followed by `[ARGS]...` with `rest()`.
`rest()` starts at its slot's first value, and that value is scanned like any
other token, so in `retry curl --help` the `--help` is `retry`'s, and
`retry curl -fsS` is an error unless the slot also has `Cli.hyphen()`.

Pass `program` and `args` to `Process.run(program, args, …)` in your action.
It runs the program directly, without a shell, so nothing is re-split or
expanded. `Process.run` takes a `List<String>`; convert from
`List<&2, String>` with a one-line recursion, as the cookbook entry does.

The [`timeout`-like cookbook entry](../cookbook/exec.md) is a full program.

## git-style plugins: `external()`

`git foo` runs `git-foo` when `foo` is not a built-in command. With
`Cli.external()`, an unknown subcommand is not an error; the parse completes
and `Cli.external_args` gives you the name and the remaining tokens:

```python
Cli.cmd("pkg", "A package manager", [
  Cli.external(),
  Cli.sub("add", "Add packages", [...]),
  ...
])
```

The external case has its own command path (the parent's), so route it with
the parent's key and read `Cli.external_args(m)` there:

```python
def external(found: Maybe<(String & List<&2, String>)>) -> Cli.Dec(Job):
  match found:
    case Some{(name, args)}:
      Cli.Dec.pure(Job, Plugin{name, args})
    case None{}:
      Cli.fail(Job, "a command is required")

def plugin(+m: Cli.Matches) -> Cli.Dec(Job):
  external(Cli.external_args(m))
```

```python
Cli.route(Job, m, [("", plugin), ("add", add), ...])
```

The `None{}` arm is not dead code: `Cli.check` runs the decoder on a sample
of each runnable path, and the sample for the root has no external name. A
`Cli.bug` there would fail your `cli_ok` law; `Cli.fail` is ignored by the
check, and at run time the parser has already required a subcommand.

Nothing after the unknown name is scanned,
so `pkg lint --fix src` gives `("lint", ["--fix", "src"])` even if `pkg` has
no `--fix`. Global options before the name are still parsed: `pkg -v lint`
counts the `-v`.

`act` then runs `pkg-lint` with the arguments, and reports a missing plugin
in its own words:

```
error: 'lint' is not a pkg command or an installed plugin (pkg-lint)
```

Help does not list plugins, because the library cannot know them; mention
the convention with `Cli.after(...)`.

## The `--` problem

The Bend runtime removes the first `--` from argv before your program sees
it, wherever it appears. For a wrapper that matters twice:

- Users rarely need a `--` of their own before the program name, because
  `rest()` already passes everything after it through.
- A `--` meant for the wrapped program is removed too:
  `retry grep -- -x f` reaches `retry` as `retry grep -x f`, and `grep`
  gets `-x` as an option. Users type `retry grep -- -- -x f`.

Say so in your help with `Cli.after(...)` or in your README. See
[Platform notes](../concepts/platform.md#the-runtime-takes-the-first---).
