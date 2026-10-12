# Options that take values

| Usage string | Takes | Absent | Read with |
|---|---|---|---|
| `-o, --output <FILE>` | one value; the last occurrence wins | default, else none | `Cli.str` or `Cli.str_opt` |
| `-I, --include <DIR>...` | a value per occurrence, in order | default, else `[]` | `Cli.strs` |
| `--color[=<WHEN>]` | `--color=v` gives v; bare `--color` gives the `bare` value | default, else none | `Cli.str` or `Cli.str_opt` |

The placeholder (`FILE`, `DIR`) is what help shows. Any text without spaces,
`<`, `>`, `[`, `]` or `=` works.

## One value

```python
Cli.arg("-o, --output <FILE>", "Write to FILE instead of stdout", [Cli.as_file()])
```

Every spelling works: `-o out.txt`, `-oout.txt`, `-o=out.txt`,
`--output out.txt`, `--output=out.txt`. `--output=` gives the empty string.
Options may appear before, between or after positionals, and inside a short
cluster the option must come last: `-vo out.txt` works, `-ov out.txt` gives
`-o` the value `v`.

Choose the reader by whether the option always has a value:

```python
out : Maybe<&2, String> <- Cli.str_opt(m, "output")   # may be absent
out : String <- Cli.str(m, "output")                  # only with a default or required()
```

Using `Cli.str` on an option that may be absent is a definition error, and
[`Cli.check`](testing.md) reports it with the reader to use instead:

```
'output' may be absent; read it with Cli.str_opt
```

### A required option

```python
Cli.arg("--token <TOKEN>", "API token", [Cli.required(), Cli.env("APP_TOKEN")])
```

A required option must come from argv or the environment; a default does not
satisfy it, and the definition check rejects `required()` with `default`.
Usage text lists required options. With a `--quiet` flag also declared:

```console
$ app --quiet
error: the following required arguments were not provided:
  --token <TOKEN>

Usage: app [OPTIONS] --token <TOKEN>

For more information, try '--help'.
```

With an empty command line, a missing required argument prints the summary
help to stderr instead, still with exit status 2.

Prefer a positional or a default where you can: required options are a
smell in most CLIs.

### Values that start with `-`

By default, `--pattern -x` is an error, because `-x` looks like an option:

```console
$ app --pattern -x
error: a value is required for '--pattern <PAT>' but none was supplied
```

Users can always write `--pattern=-x`. To accept `--pattern -x` too, add
`Cli.hyphen()`:

```python
Cli.arg("-e, --pattern <PAT>", "Pattern to match", [Cli.hyphen()])
```

Numeric options with `Cli.as_f32()` accept negative numbers without
`hyphen()`, unless a short option in scope is a digit.

## Repeated values

```python
Cli.arg("-I, --include <DIR>...", "Add DIR to the search path", [Cli.as_dir()])
```

```python
dirs : List<&2, String> <- Cli.strs(m, "include")
```

`-I a -I b --include=c` gives `["a", "b", "c"]`. Each occurrence takes exactly
one value: `-I a b` makes `b` a positional. That is deliberate. See
[design choices](../concepts/design.md#one-value-per-occurrence).

### Delimited lists

`Cli.delim(',')` splits each value, so `--tag a,b --tag c` gives
`["a", "b", "c"]`:

```python
Cli.arg("--tag <TAG>...", "Tags to apply", [Cli.delim(',')])
```

`delim` also splits environment values and defaults, and each element is
checked on its own:

```python
Cli.arg("--port <PORT>...", "Ports to listen on",
  [Cli.as_u32(), Cli.delim(','), Cli.env("PORTS"), Cli.default("80,443")])
```

```console
$ PORTS=8080,x app
error: invalid value 'x' for '--port <PORT>...' from environment variable PORTS: expected a whole number from 0 to 4294967295
```

`delim` goes only on list options (`...`) and variadic positionals.

## An optional value

`--color[=<WHEN>]` may be given with or without a value. Without one it takes
the value from `Cli.bare`, which is required:

```python
Cli.arg("--color[=<WHEN>]", "When to color output",
  [Cli.bare("always"), Cli.default("auto"), Cli.one_of(["auto", "always", "never"])])
```

| argv | value |
|---|---|
| (nothing) | `auto` (the default) |
| `--color` | `always` (the bare value) |
| `--color=never` | `never` |
| `--color never` | `always`, and `never` is a positional |

The value must be attached with `=`: that is what keeps `--color never`
unambiguous. Optional-value options have no short form.

The built-in [`Cli.color()`](terminal.md) is a plain `--color <WHEN>` option
whose value also drives the library's own coloring.

## Grouping options in help

`Cli.heading("Network")` moves an option out of `Options:` into a section of
its own. Sections appear in order of first use:

```python
Cli.arg("--proxy <URL>", "Proxy to use", [Cli.heading("Network")]),
Cli.arg("--timeout <SECS>", "Give up after SECS", [Cli.as_u32(), Cli.heading("Network")]),
```

See also: [Typed values](values.md), [Defaults and the
environment](sources.md), [Usage strings](../reference/usage-strings.md).
