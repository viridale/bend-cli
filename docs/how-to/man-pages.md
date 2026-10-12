# Man pages

```python
Cli.cmd("pkg", "A package manager", [..., Cli.man()])
```

adds a hidden subcommand `man [COMMAND]...` that prints a man(7) page:

```console
$ pkg man | man -l -              # the root page, pkg(1)
$ pkg man add > pkg-add.1         # the page for 'pkg add'
```

On macOS, use `pkg man | mandoc -a` instead of `man -l -`.

## What a page contains

The page name is the command path joined with `-` (`pkg-add`). Sections, in
order:

| Section | Content |
|---|---|
| NAME | `pkg-add \- Add packages` |
| SYNOPSIS | the usage line |
| DESCRIPTION | every paragraph of the about text |
| ARGUMENTS | visible positionals, with full help |
| OPTIONS | visible options: names in bold, placeholders in italics, full help and tags |
| COMMANDS | subcommands, each with its summary and a reference to its page |
| ENVIRONMENT | every variable named by `Cli.env` |
| EXIT STATUS | 0, 1, 2 and 70, with their meanings |
| EXAMPLES | `Cli.example` entries |
| SEE ALSO | the subcommand pages |

The header carries the program name and version but no date, so the same
definition always produces the same bytes. That keeps packaged pages
reproducible and lets a law pin them.

## Installing

Generate one file per command path at build time:

```console
$ pkg man > share/man/man1/pkg.1
$ pkg man add > share/man/man1/pkg-add.1
$ pkg man remove > share/man/man1/pkg-remove.1
```

## Apps without subcommands

`man()` is a subcommand. For a one-command app, print `Cli.roff(cli(), [])`
from `act` behind a hidden option, as shown for
[completions](completions.md#apps-without-subcommands).

## Writing for man pages

The DESCRIPTION is your about text, so the later paragraphs of `about` are
where the manual lives. Use `"\n"` for line breaks and two-space indents for
simple lists; the library escapes everything, including lines starting with
`.` or `'`, which roff would otherwise treat as commands.
