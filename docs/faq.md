# FAQ

## Parsing

### My program never sees `--`.

The Bend runtime removes the first `--` before `main` runs. Users of a built
program type it twice: `app -- -- -x`. From source, `bend main.bend -- -- -x`.
See [Platform notes](concepts/platform.md#the-runtime-takes-the-first---).

### I declared `--threads` and it never arrives.

Native builds remove `--threads N`, `--gpu V`, `--gpu-build` and
`--bend-help` from argv, and compiled JavaScript removes all but
`--gpu-build`. Pick another name, such as `--jobs`.

### `-I a b` gives one include and a stray positional.

Each occurrence takes exactly one value. Write `-I a -I b`, or declare
`Cli.delim(',')` and write `-I a,b`.
[Why](concepts/design.md#one-value-per-occurrence).

### How do I accept a negative number?

`as_f32` options and positionals take `-5` and `-0.5` as values, unless some
short option in scope is a digit. For other values that start with `-`, add
`Cli.hyphen()`. See [Positionals](how-to/positionals.md) and
[Options](how-to/options.md#values-that-start-with--).

### Why doesn't `--verb` work for `--verbose`?

bend-cli matches names exactly. If prefixes were accepted, adding
`--version` later would change what `--ver` means in existing scripts. The
error suggests `--verbose`.

### I want an option that takes two values, like `--point 3 4`.

Use one value with a delimiter (`--point 3,4` with `Cli.delim(',')`) and
check the count in the decoder, or two options (`--x 3 --y 4`).

### Can a command take both positionals and subcommands?

No; the definition check reports `Mixed`, because `app build` could then
mean the subcommand `build` or a file named `build`. Give the positionals
their own subcommand.

### How do I run a default subcommand when none is given?

Add `Cli.sub_optional()` to the parent and give the parent's own path a
`route` key (`""` for the root). See
[Subcommands](how-to/subcommands.md#required-or-optional-subcommand).

### How do I wrap another program and pass its options through?

Give the program and its arguments one `<COMMAND>...` slot with
`Cli.rest()`. See [Wrapping other programs](how-to/wrappers.md).

## Values and sources

### My environment variable is set but ignored.

An empty value counts as unset. Also check the name: `Cli.env` names are
exact and case-sensitive.

### How do I know whether a value came from the command line?

`Cli.source(m, id)` returns `Argv{}`, `Env{}`, `Default{}` or `Absent{}`;
`Cli.given(m, id)` is `True` for the first two. See
[Sources](how-to/sources.md#which-source-did-a-value-come-from).

### How do I validate a value beyond its type?

In the decoder: read it, check it, and `Cli.fail(A, msg)` on failure. The
message is printed in the usage-error shape and the program exits 2. See
[Values](how-to/values.md).

### How do I read a config file?

The library does not read files. Read the file in `main` or `act`, then
layer it between the command line and the defaults with `Cli.source`. See
[Sources](how-to/sources.md#layering-a-config-file).

## Help and output

### Help is narrower than my terminal.

Help wraps at the terminal width, capped at 100 columns, and at no less
than 40. `COLUMNS` overrides the terminal's width.

### There are no colors in CI.

Color is on only when the stream is a terminal, unless `CLICOLOR_FORCE` is
set or the user passes `--color always`. `NO_COLOR` turns it off. See
[Terminal output](how-to/terminal.md#color).

### How do I hide an option but keep it working?

`Cli.hidden()`. It still parses; it is left out of help, completions, man
pages and suggestions.

### How do I color my own output the same way?

Use the `Cli.Term` that `act` receives: `Cli.paint(out_color, styles, text)`.
See [Terminal output](how-to/terminal.md#coloring-your-own-output).

### Can help show a default my program computes at run time?

Not as a tag: `[default: ...]` shows the literal from `Cli.default`. Leave
the default out and describe it in the help text.

## Checking and testing

### `cli_ok` fails with `DecodeBug`.

`Cli.check` ran your decoder on a sample command line for each command path,
and the decoder raised `Cli.bug`. The message says why: usually a reader that
does not fit the argument (`read it with Cli.str_opt`), an id that is not in
scope, or a `route` table missing a path. Arms that cannot happen at run
time, such as the `None` arm of `Cli.external_args`, should use `Cli.fail`,
which the check ignores.

### My program prints `bug: invalid command-line definition` and exits 70.

The definition has a problem that a `cli_ok` law would have caught. Add the
law; its failure shows the problem list. See
[Messages](reference/messages.md#definition-problems).

### `Run.main` rejects my decoder's type.

Callbacks have fixed forms: `decode(+m: Cli.Matches)` and
`act(+t: Cli.Term, a: A)`. The `+` is part of the function's type, so a def
with `m` instead of `+m` does not fit. Change the parameter or pass a lambda.

### How do I test what `act` prints?

Split it: a pure function computes the output and exit code, and `act` only
writes them. Laws pin the pure part. See
[Testing](how-to/testing.md#testing-what-act-prints).

### Why can't my laws import `main.bend`?

`main.bend` reaches `run.bend`, which uses host effects for terminal
probing and exit, and a law's import graph may not contain foreign code.
Laws import your pure `app.bend`. See
[Architecture](concepts/architecture.md).

## Platforms and versions

### Does it run on Windows?

Not in 1.x. CI covers macOS arm64 and Ubuntu x86-64, native and compiled
JavaScript.

### How do I upgrade?

Change the version in both imports (`cli@…/cli.bend` and `cli@…/run.bend`)
and re-run your laws. Patch releases never change output bytes; minor
releases list every output change in the [changelog](../CHANGELOG.md).
