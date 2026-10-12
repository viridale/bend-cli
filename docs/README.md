# bend-cli documentation

bend-cli turns one command definition into a parser, typed decoding, help
pages, error messages with suggestions, color, shell completions and man
pages. Every decision it makes is a pure function, so you can state how your
CLI behaves as Bend laws and prove them.

```python
def cli() -> Cli.Cmd:
  Cli.cmd("greet", "Print a greeting", [
    Cli.arg("-n, --times <N>", "Greet N times", [Cli.as_u32(), Cli.default("1")]),
    Cli.arg("--shout", "Greet in capitals", []),
    Cli.arg("[NAME]", "Who to greet", [Cli.default("world")]),
  ])
```

```console
$ greet --tims 2
error: unexpected argument '--tims' found

  tip: a similar argument exists: '--times'

Usage: greet [OPTIONS] [NAME]

For more information, try '--help'.
```

## Where to start

| You want to… | Read |
|---|---|
| see it work in five minutes | [Quickstart](../README.md#quickstart) |
| learn the library end to end | [Tutorial](tutorial.md), eight short chapters with one app that grows |
| get one job done | [How-to guides](#how-to-guides) |
| copy a whole program | [Cookbook](#cookbook) |
| look up an exact rule, name or message | [Reference](#reference) |
| understand why it works this way | [Concepts](#concepts) |

## Tutorial

[The tutorial](tutorial.md) builds `greet`, then a `notes` app with
subcommands, and proves both:

1. [A first command](tutorial.md#1-a-first-command)
2. [Flags and options](tutorial.md#2-flags-and-options)
3. [Positionals](tutorial.md#3-positionals)
4. [Types and validation](tutorial.md#4-types-and-validation)
5. [Defaults and the environment](tutorial.md#5-defaults-and-the-environment)
6. [Subcommands](tutorial.md#6-subcommands)
7. [Laws: testing and proving the CLI](tutorial.md#7-laws-testing-and-proving-the-cli)
8. [Shipping: version, completions, man pages, builds](tutorial.md#8-shipping)

## How-to guides

Arguments

- [Flags, counts and `--[no-]` switches](how-to/flags.md)
- [Options that take values](how-to/options.md): single, repeated, optional
  values, delimited lists
- [Positionals](how-to/positionals.md): optional, variadic, `cp`-style
  `<SRC>... <DST>`, `-` for stdin, values that start with `-`
- [Typed and restricted values](how-to/values.md): numbers, booleans, choices
  mapped to your own types, custom validation
- [Defaults, environment variables and config files](how-to/sources.md)
- [Required arguments, conflicts, dependencies and groups](how-to/relations.md)

Commands

- [Subcommands](how-to/subcommands.md): nesting, `route`, global options,
  aliases, optional subcommands
- [Wrapping other programs](how-to/wrappers.md): `rest()`, `external()`,
  git-style plugins

Output

- [Writing help text](how-to/help.md): summaries, paragraphs, headings,
  examples, hidden items, `--version`
- [Errors and exit codes](how-to/errors.md): failing from a decoder, exit
  statuses, which stream gets what
- [Color and terminal width](how-to/terminal.md)
- [Shell completions](how-to/completions.md)
- [Man pages](how-to/man-pages.md)

Quality and delivery

- [Testing and proving a CLI](how-to/testing.md)
- [Building, publishing and upgrading](how-to/distribution.md)

## Cookbook

Complete programs, each with its definition, decoder, `act` and laws.

- [`cp`: a variadic before a required positional](cookbook/cp.md)
- [`git`-like: nested subcommands, globals, plugins](cookbook/git.md)
- [`grep`: flags, env, color, exit statuses, real file IO](cookbook/grep.md)
- [`timeout`-like: run another command with its own options](cookbook/exec.md)

## Reference

- [Usage strings](reference/usage-strings.md): the grammar and every form
- [Attributes](reference/attributes.md): every builder, where it may go, what
  it does
- [Readers](reference/readers.md): which reader fits which argument
- [API](reference/api.md): every public type and function in `cli.bend` and
  `run.bend`
- [Messages](reference/messages.md): every error, tip, lint problem and exit
  code, with the exact text
- [Parsing rules](reference/parsing.md): how argv is scanned, assigned and
  checked
- [Environment variables](reference/environment.md) the library reads

## Concepts

- [Architecture: a pure core and a thin shell](concepts/architecture.md)
- [Design choices](concepts/design.md): the goals behind bend-cli, and what
  it rejects on purpose
- [Platform notes](concepts/platform.md): what the Bend runtime does to argv,
  output and exit

## Also

- [FAQ](faq.md)
- [Changelog](../CHANGELOG.md)

## Conventions in these docs

- Code blocks tagged `python` are Bend (Bend's syntax highlights as Python).
- `$` lines are commands; the lines after them are the exact output. Exit
  codes are given in the text when they are not 0.
- `Cli.` names come from `cli.bend` and `Run.` names from `run.bend`,
  imported as the [Quickstart](../README.md#quickstart) shows.
- Help pages are shown at 80 columns without color.
