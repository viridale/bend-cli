# Positionals

Positionals are the arguments that are not options. Their usage string is a
placeholder in angle brackets (required) or square brackets (optional),
optionally followed by `...`:

| Usage | Takes | Absent | Read with |
|---|---|---|---|
| `<FILE>` | exactly one | error | `Cli.str` |
| `[FILE]` | zero or one | default, else none | `Cli.str` with a default, else `Cli.str_opt` |
| `<FILE>...` | one or more | error | `Cli.strs` |
| `[FILE]...` | zero or more | default, else `[]` | `Cli.strs` |

The id is the placeholder in lower case: `<FILE>` has id `file`. Use
`Cli.id("source")` to choose another.

Positionals fill slots in the order you declare them. A command that has
subcommands cannot have positionals; see
[Subcommands](subcommands.md).

## Several slots

Order the slots as a user would type them:

```python
Cli.arg("<PATTERN>", "Text to search for", []),
Cli.arg("[FILE]...", "Files to search; standard input if none", [Cli.as_file()]),
```

The definition check allows any number of single slots, at most one
variadic (`...`) slot, and only required single slots after the variadic.
These are rejected, each with a message saying why:

- a required slot after an optional one (`[A] <B>`);
- two variadic slots;
- an optional or variadic slot after the variadic one (`<A>... [B]`).

## `cp`-style: many sources, one destination

A variadic slot may be followed by required single slots. The variadic takes
whatever is left:

```python
Cli.arg("<SRC>...", "Files to copy", [Cli.as_file()]),
Cli.arg("<DEST>", "Directory or file to copy to", [Cli.as_file()]),
```

```python
srcs : List<&2, String> <- Cli.strs(m, "src")
dest : String <- Cli.str(m, "dest")
```

`cp a b c dir` gives `srcs = ["a", "b", "c"]` and `dest = "dir"`. The slots
after the variadic fill first, so `cp a` gives `dest = "a"` and leaves no
source:

```console
$ cp a
error: the following required arguments were not provided:
  <SRC>...

Usage: cp <SRC>... <DEST>

For more information, try '--help'.
```

The full program is in the [cookbook](../cookbook/cp.md).

## Too many values

A value with no slot left is an error:

```console
$ greet Ada Grace
error: unexpected argument 'Grace' found
```

If you want extra values, make the last slot variadic.

## Reading standard input from `-`

`-` is an ordinary positional value, so the parser passes it through. Your
action decides what it means. The convention is "standard input", which
Bend reads as a file:

```python
def input_path(dash: Bool, path: String) -> String:
  match dash:
    case True{}:
      "/dev/stdin"
    case False{}:
      path

def open_path(+path: String) -> String:
  input_path(String.eq(path, "-"), path)
```

`File.open(open_path(p), "r")` then works for both. Use `[FILE]...` with no
default and treat `[]` as `["-"]` for the `cat`/`grep` convention.

## Values that start with `-`

A token that starts with `-` is read as an option. A user passes such a value
after the end-of-options marker `--`:

```console
$ rm -- -file
```

Because the Bend runtime consumes the first `--` it sees, users of a built
program type it twice: `rm -- -- -file`. See [Platform
notes](../concepts/platform.md#the-runtime-takes-the-first---). When a
positional could take the token, the error says so:

```console
$ rm --draft
error: unexpected argument '--draft' found

  tip: to pass '--draft' as a value, use '-- --draft'

Usage: rm [FILE]...

For more information, try '--help'.
```

Two attributes avoid the `--`:

- **`Cli.hyphen()`** on a positional accepts a token that starts with `-` when
  it is not an option in scope. `calc -5 + 3` works if `-5` is not a declared
  short.
- **`Cli.as_f32()`** accepts negative numbers (`-5`, `-0.5`, `-1e3`) as
  values, unless a short option in scope is a digit.

## Passing everything through: `rest()`

`Cli.rest()` on the last, variadic positional makes every token from its first
value on a value, including ones that look like options and `--`:

```python
Cli.sub("run", "Run a package script", [
  Cli.arg("<SCRIPT>", "Script name", []),
  Cli.arg("[ARGS]...", "Arguments for the script", [Cli.rest(), Cli.hyphen()]),
])
```

`pkg run test --watch -- -x` gives `script = "test"` and
`args = ["--watch", "--", "-x"]`. Options *before* the script name are still
`pkg run`'s own. The first value is scanned normally, so add `Cli.hyphen()`
when it may start with `-`: without it, `--watch` above is an unknown
option. Even with it, a first value that is one of `pkg run`'s own options
is taken as that option: `pkg run test --help` prints `pkg run`'s help. When
the name in front is only something to pass on, such as a program to run,
put it in the rest slot too; see [Wrapping other programs](wrappers.md).

## Defaults and environment for positionals

`[FILE]` and `[FILE]...` take `Cli.default`; `Cli.env` works on any
positional. A required positional (`<FILE>`) must come from argv or the
environment.

See also: [Parsing rules](../reference/parsing.md#positionals),
[Usage strings](../reference/usage-strings.md).
