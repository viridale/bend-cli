# Writing help text

Help is generated from the definition. You write the text; the library does
the layout, the tags (`[default: …]`, `[env: …]`), the usage line and the
wrapping.

## Summary and full help

`about` and `help` strings are paragraphs separated by a blank line
(`"\n\n"`). The first paragraph is the **summary**:

- `-h` shows summaries only;
- `--help` shows every paragraph;
- command lists, completions and `-h` use the summary;
- man pages use everything.

```python
Cli.cmd("backup", "Copy files to a backup location\n\nFiles are copied only when they changed since the last run. Use --full to copy everything.", [
  Cli.arg("--full", "Copy every file\n\nSlower, but repairs a damaged backup.", []),
  Cli.arg("<DEST>", "Where to copy to", []),
  Cli.example("backup --full /mnt/disk", "Rebuild a backup from scratch"),
])
```

```console
$ backup -h
Copy files to a backup location

Usage: backup [OPTIONS] <DEST>

Arguments:
  <DEST>      Where to copy to

Options:
      --full  Copy every file
  -h, --help  Print help (see more with '--help')

Examples:
  Rebuild a backup from scratch:
    $ backup --full /mnt/disk
$ backup --help
Copy files to a backup location

Files are copied only when they changed since the last run. Use --full to copy
everything.

Usage: backup [OPTIONS] <DEST>

Arguments:
  <DEST>      Where to copy to

Options:
      --full  Copy every file

              Slower, but repairs a damaged backup.
  -h, --help  Print help (see a summary with '-h')

Examples:
  Rebuild a backup from scratch:
    $ backup --full /mnt/disk
```

`--help` mentions `-h` only when the two pages differ, that is, when some
visible text has more than one paragraph.

Guidelines that keep help consistent with the library's own text:

- Start summaries with a verb in the imperative: "Copy files", "Print
  version". No final period.
- Keep a summary under about 50 characters so it fits beside the names.
- Put details, caveats and examples in later paragraphs.

A single `"\n"` inside a paragraph is a hard line break. Leading spaces on a
line are kept and repeated on wrapped continuation lines, so you can write
simple indented lists:

```python
"Output formats:\n  text  one line per item\n  json  an array of objects"
```

## Text is required

Every visible command and argument needs non-empty help. An empty one is a
`NoHelp` problem from `Cli.check`, and the program exits 70 until you fix
it. Hidden items are exempt.

## What help shows for you

| Section | Contains |
|---|---|
| about | the summary, or all paragraphs |
| `Usage:` | the command path, `[OPTIONS]`, required options, `need_one` groups, positionals, `<COMMAND>` |
| `Commands:` | visible subcommands in order, then `help` |
| `Arguments:` | visible positionals |
| `Options:` | the command's options, then inherited globals (root first), then `-h, --help` and `-V, --version` |
| one per `Cli.heading` | options moved there, in order of first use |
| `Examples:` | `Cli.example` entries |
| after text | `Cli.after` paragraphs |

Tags follow the last paragraph of an argument's help, in this order:
`[env: NAME]`, `[default: v]`, `[possible values: a, b]`,
`[aliases: --x, -y]`. Subcommands show `[aliases: …]`.

Help wraps to the terminal width, clamped to 40–100 columns. `COLUMNS`
overrides the terminal. The description column adapts to the names; a name
too long for it puts its description on the next line.

## Examples and closing text

```python
Cli.example("pkg add -D left-pad", "Add a development dependency"),
Cli.after("See https://pkg.example/docs for the manual."),
```

Examples appear in help and in the man page's EXAMPLES section. Write the
full command line, starting with the program name.

## Hiding things

`Cli.hidden()` on an argument or subcommand keeps it working but removes it
from help, completions, man pages and suggestions. Use it for debugging
switches and for old names you still accept. It is not a security feature:
anyone can still type the name.

## Ordering

Everything appears in declaration order: positionals, options, subcommands,
headings. Declare the most used things first.

## `--version`

```python
Cli.version("1.4.2")
```

adds `-V, --version` to the root, printing `name 1.4.2` to stdout. If you
declare your own `-V`, `--version` keeps working without a short form. The
version is a string you maintain; a law can tie it to your changelog or
package version if you keep both in Bend.

## Checking help in laws

`Cli.help(c, path, long, host)` renders a page as a string, so a law can pin
it exactly:

```python
law help_page:
  {Cli.help(App.cli(), [], False{}, Cli.host(80n))
    == "Copy files to a backup location\n\nUsage: backup [OPTIONS] <DEST>\n\nArguments:\n  <DEST>      Where to copy to\n\nOptions:\n      --full  Copy every file\n  -h, --help  Print help (see more with '--help')\n\nExamples:\n  Rebuild a backup from scratch:\n    $ backup --full /mnt/disk\n"
    : String}
```

When the page changes, the failed check shows the new text. See [Testing and
proving a CLI](testing.md#golden-help-pages).
