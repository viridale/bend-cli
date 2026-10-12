# Shell completions

## Adding the `completions` subcommand

```python
Cli.cmd("pkg", "A package manager", [
  Cli.sub("add", ...),
  ...
  Cli.completions(),
])
```

adds `pkg completions <SHELL>`, where `SHELL` is `bash`, `zsh` or `fish`. It
prints a self-contained script to stdout. Your decoder and `route` table never
see this subcommand; `Cli.eval` handles it.

## What completes

At every point in a command line the script offers:

- the visible subcommands, with their summaries where the shell shows
  descriptions (zsh, fish);
- the visible options in scope, including inherited globals;
- values: the `one_of` list, file names for `Cli.as_file()`, directory
  names for `Cli.as_dir()`, and nothing for other types;
- positionals complete by the slot they would fill.

Hidden arguments and subcommands never appear.

## Installing

Tell your users (or ship the files in your package):

| Shell | Install |
|---|---|
| bash 4+ | add `source <(pkg completions bash)` to `~/.bashrc` |
| zsh | `pkg completions zsh > "${fpath[1]}/_pkg"`, then restart zsh |
| fish | `pkg completions fish > ~/.config/fish/completions/pkg.fish` |

Packagers can generate the files at build time with the same commands.

## Apps without subcommands

`completions()` is a subcommand, and a command with positionals cannot have
subcommands, so a one-command app like `greet [NAME]...` cannot add it.
Generate the script yourself with `Cli.script`, which is pure:

```python
Cli.arg("--completions <SHELL>", "Print a shell completion script",
  [Cli.one_of(["bash", "zsh", "fish"]), Cli.hidden()]),
```

```python
shell : Maybe<&2, Cli.Shell> <- Cli.choose_opt(Cli.Shell, m, "completions",
  [("bash", Cli.Bash{}), ("zsh", Cli.Zsh{}), ("fish", Cli.Fish{})])
```

and in `act`, when `shell` is `Some{s}`, print `Cli.script(cli(), s)` with
`IO.write` and return 0. The same works for man pages with `Cli.roff`.

The option is hidden, so the generated script does not offer it. It is an
ordinary option, so it works only when the rest of the command line is
valid: with a required positional, `app --completions bash` fails before your
decoder runs. Give such apps subcommands, or make the positional optional
and check it in the decoder.

## Testing

`Cli.script(c, shell)` returns the script as a string, so a golden law can
pin it. Every name and description enters the script through a quoting
function that the library proves round-trips, so help text containing
quotes, backslashes or `$` cannot break or inject into the script.

## Limits

- Completions are static: they cannot ask your program for values (such
  as package names from a registry).
- PowerShell, Elvish and Nushell are not supported.
