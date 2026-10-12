# Subcommands

`Cli.sub(name, about, items)` declares a subcommand. Its items are the same
as a command's: arguments, attributes and more subcommands.

```python
def cli() -> Cli.Cmd:
  Cli.cmd("git", "A version control system", [
    Cli.arg("-C <DIR>", "Run as if started in DIR", [Cli.global(), Cli.as_dir()]),
    Cli.sub("remote", "Manage remotes", [
      Cli.sub("add", "Add a remote", [
        Cli.arg("<NAME>", "Remote name", []),
        Cli.arg("<URL>", "Remote URL", []),
      ]),
      Cli.sub("remove", "Remove a remote", [
        Cli.alias("rm"),
        Cli.arg("<NAME>", "Remote name", []),
      ]),
    ]),
    Cli.sub("status", "Show the working tree status", [
      Cli.arg("-s, --short", "Give the output in the short format", []),
    ]),
  ])
```

## Decoding by path

The command path is the list of subcommand names from the root:
`git remote add` has path `["remote", "add"]`. `Cli.route` picks a decoder by
path, with the names joined by single spaces:

```python
def decode(+m: Cli.Matches) -> Cli.Dec(Action):
  do Cli.Dec<Action>:
    dir : Maybe<&2, String> <- Cli.str_opt(m, "C")
    job : Job <- Cli.route(Job, m, [
      ("remote add", remote_add),
      ("remote remove", remote_remove),
      ("status", status),
    ])
    return Action{dir, job}
```

Each callback has the decoder's form, `def remote_add(+m: Cli.Matches) ->
Cli.Dec(Job)`. Keys are canonical names; aliases (`git remote rm`) route to
the same key. Only paths that can run need a key: `remote` alone requires a
subcommand, so it has none.

`Cli.check` verifies the table against the definition: a runnable path
without a key, or a key that names no command, is reported. So adding a
subcommand without decoding it fails your `cli_ok` law.

`Cli.path(m)` gives the path directly when you prefer to match on it
yourself.

## Options and scope

A subcommand sees its own arguments and the `Cli.global()` arguments of
every ancestor. Options of a parent that are not global must come *before*
the subcommand name, and the error says so:

```console
$ app sync --dry-run
error: unexpected argument '--dry-run' found

  tip: '--dry-run' belongs to 'app'; place it before 'sync'
```

Global arguments may appear anywhere: `git -C repo status` and
`git status -C repo` are the same. Occurrences on both sides merge, and the
last one wins.

Use globals for cross-cutting settings (verbosity, color, working directory,
config file). Keep everything else on the command it belongs to.

When an option of a subcommand is used too early, the tip points to it:

```console
$ git --short status
error: unexpected argument '--short' found

  tip: '--short' belongs to subcommand 'git status'
```

## Required or optional subcommand

By default a command with subcommands requires one. With no arguments at all
the root prints its summary help to stderr (exit 2); deeper, it is an error
that lists the subcommands:

```console
$ git remote
error: 'git remote' requires a subcommand but none was provided
```

`Cli.sub_optional()` lets the command run alone. Route the bare command with
its own key; the root's key is `""`:

```python
Cli.sub("stash", "Stash changes", [
  Cli.sub_optional(),
  Cli.arg("-m, --message <MSG>", "Description of the stash", []),
  Cli.sub("pop", "Apply and drop the latest stash", []),
])
```

```python
Cli.route(Job, m, [("stash", stash_push), ("stash pop", stash_pop)])
```

## Positionals and subcommands do not mix

A command has either positionals or subcommands. `git remote` takes a
subcommand; `git remote add` takes a name and a URL. Mixing them makes
`app build` ambiguous (a file called `build`, or the subcommand?), so the
definition check reports `Mixed`. To accept arbitrary names after a
subcommand position, use [`Cli.external()`](wrappers.md).

## The `help` subcommand

Every command with subcommands gets `help [COMMAND]...`, listed last under
`Commands:`:

```console
$ git help remote add       # same as: git remote add --help
```

`help` with a name that does not exist is an error with suggestions. You
cannot declare your own subcommand named `help`.

## Aliases and hidden subcommands

```python
Cli.sub("remove", "Remove a remote", [Cli.alias("rm"), ...])
Cli.sub("debug-dump", "Dump internal state", [Cli.hidden(), ...])
```

Aliases appear in help as `[aliases: rm]`. Hidden subcommands work but do
not appear in help, completions or man pages. There is no prefix matching:
`git rem` is an error, and a near miss such as `git remot` suggests `remote`.

## Sharing arguments between subcommands

An item list is an ordinary Bend list, so build shared parts with functions:

```python
def output_args() -> List<&2, Cli.Item>:
  [
    Cli.arg("--json", "Print JSON", []),
    Cli.arg("-o, --output <FILE>", "Write to FILE", [Cli.as_file()]),
  ]

Cli.sub("list", "List things", List.append(&2, Cli.Item, output_args(), [
  Cli.arg("-a, --all", "Include hidden things", []),
]))
```

and decode them with a shared helper that each route callback calls:

```python
def output(+m: Cli.Matches) -> Cli.Dec(Output):
  do Cli.Dec<Output>:
    json : Bool <- Cli.flag(m, "json")
    file : Maybe<&2, String> <- Cli.str_opt(m, "output")
    return Output{json, file}
```

If the arguments really apply to every subcommand, declare them once on the
parent with `Cli.global()` instead.

The full program is in the [git-like cookbook entry](../cookbook/git.md).
