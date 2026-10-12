# Flags, counts and `--[no-]` switches

A flag takes no value. Its usage string decides what it records:

| Usage string | Records | Absent | Read with |
|---|---|---|---|
| `-q`, `--quiet`, `-q, --quiet` | `True` when given | `False` | `Cli.flag` |
| `-v, --verbose...` | how many times it was given | `0n` | `Cli.count` |
| `--[no-]cache`, `-c, --[no-]cache` | `True` for `--cache`/`-c`, `False` for `--no-cache`; last wins | the default, else `False` | `Cli.flag` |

## A simple flag

```python
Cli.arg("-q, --quiet", "Print nothing on success", [])
```

```python
quiet : Bool <- Cli.flag(m, "quiet")
```

The id is the long name, else the short letter: `-q` alone has id `q`.

Giving a flag a value is an error:

```console
$ app --quiet=yes
error: unexpected value 'yes' for '--quiet' found; no more were expected
```

## A verbosity count

```python
Cli.arg("-v, --verbose...", "More output; repeat for more", [Cli.global()])
```

```python
verbose : Nat <- Cli.count(m, "verbose")
```

`-v -v -v`, `-vvv` and `--verbose -vv` all give `3n`. `Cli.global()` lets the
flag appear after a subcommand name too.

For a quiet/verbose pair, declare both and combine them in the decoder:
`-q` sets a floor and `-v` raises it. Do not make them `Cli.conflicts`, or an
alias like `alias app='app -q'` stops users from adding `-v`.

## An on/off switch

`--[no-]x` declares `--x` and `--no-x` in one argument. The last occurrence
wins, so a user can override an alias:

```python
Cli.arg("--[no-]cache", "Use the download cache", [Cli.default("true")])
```

```console
$ app --no-cache --cache    # cache on
$ app --cache --no-cache    # cache off
```

A switch's default is written in the `as_bool` vocabulary (`true`, `false`,
`yes`, `no`, `on`, `off`, `1`, `0`, any case). Without a default it is
`False`. Help shows the usage string as written: `--[no-]cache`.

A short name sets the switch to `True`: `-c, --[no-]cache`.

## Flags from the environment

`Cli.env` works on flags and switches. The variable is read in the `as_bool`
vocabulary; a count reads a whole number:

```python
Cli.arg("--[no-]color-diff", "Color diffs", [Cli.env("APP_COLOR_DIFF")])
Cli.arg("-v, --verbose...", "More output", [Cli.env("APP_VERBOSE")])
```

```console
$ APP_COLOR_DIFF=off app        # color-diff is False
$ APP_VERBOSE=2 app             # verbose is 2n
$ APP_COLOR_DIFF=maybe app      # error, exit 2:
error: invalid value 'maybe' for '--[no-]color-diff' from environment variable APP_COLOR_DIFF: expected true or false
```

An empty variable counts as unset.

## Was it given, or just false?

`Cli.flag` cannot tell "not given" from `--no-x`. Use `Cli.source`:

```python
cache : Bool <- Cli.flag(m, "cache")
from : Cli.Src <- Cli.source(m, "cache")
```

`from` is `Cli.Argv{}`, `Cli.Env{}`, `Cli.Default{}` or `Cli.Absent{}`.
`Cli.given(m, id)` is the shortcut for "from argv or the environment".

## Another spelling

`Cli.alias` adds another name, written with its dashes. Aliases parse but are
listed in help as `[aliases: …]`:

```python
Cli.arg("--colour-diff", "Color diffs", [Cli.alias("--color-diff")])
```

## Rules the definition check enforces

- A short name is one ASCII letter or digit. `-h` is yours if you declare it;
  then `--help` has no short. The same goes for `-V` with `--version`.
- `--help`, and `--version` when `Cli.version` is set, are reserved.
- A flag cannot have `Cli.default`, `Cli.required` or a value type: those
  are for arguments that take values.

See also: [Usage strings](../reference/usage-strings.md),
[Readers](../reference/readers.md).
