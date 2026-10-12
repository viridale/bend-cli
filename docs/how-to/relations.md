# Required arguments, conflicts, dependencies and groups

Relations are declared as attributes and checked after parsing, before your
decoder runs. Each failure is a usage error (exit 2) with a fixed message.

| You want | Declare | Error |
|---|---|---|
| an option must be given | `Cli.required()` on it | `the following required arguments were not provided:` |
| two args never together | `Cli.conflicts("other")` on either | `the argument '<a>' cannot be used with '<b>'` |
| one arg needs another | `Cli.requires("other")` on the first | `the argument '<a>' requires '<b>'` |
| at most one of a set | `Cli.group("g")` on each, `Cli.exclusive("g")` on the command | `the argument '<a>' cannot be used with '<b>'` |
| at least one of a set | `Cli.group("g")` on each, `Cli.need_one("g")` on the command | `the following required arguments were not provided:` |
| exactly one of a set | both `exclusive("g")` and `need_one("g")` | either |

Relations count only arguments given in **argv or the environment**. A
default never conflicts with anything and never satisfies a requirement.

## Required options

Positionals are required by their brackets (`<FILE>`). Options are optional
unless you add `Cli.required()`:

```python
Cli.arg("--token <TOKEN>", "API token", [Cli.required(), Cli.env("APP_TOKEN")])
```

Every missing item is listed at once, in declaration order. Here `deploy`
also has a `--dry-run` flag:

```console
$ deploy --dry-run
error: the following required arguments were not provided:
  --token <TOKEN>
  <TARGET>

Usage: deploy [OPTIONS] --token <TOKEN> <TARGET>

For more information, try '--help'.
```

(With a completely empty command line, the summary help is printed instead,
also with exit status 2.)

## Conflicts

```python
Cli.arg("--offline", "Use only the local cache", [Cli.conflicts("registry")]),
Cli.arg("--registry <URL>", "Registry to fetch from", [Cli.default("https://registry.example")]),
```

`conflicts` is symmetric: declare it on one side. Because defaults are
ignored, `--offline` works with the default registry and fails only when the
user sets one:

```console
$ pkg add --registry https://r.example --offline x
error: the argument '--offline' cannot be used with '--registry <URL>'
```

The first argument named is the one given later on the command line.

## Dependencies

```python
Cli.arg("--key <FILE>", "TLS private key", [Cli.requires("cert"), Cli.as_file()]),
Cli.arg("--cert <FILE>", "TLS certificate", [Cli.as_file()]),
```

```console
$ serve --key k.pem
error: the argument '--key <FILE>' requires '--cert <FILE>'
```

For "both or neither", declare `requires` in both directions.

## Groups

A group is a name shared by several arguments. Rules on the command refer to
it:

```python
Cli.cmd("export", "Export the database", [
  Cli.exclusive("format"),
  Cli.need_one("format"),
  Cli.arg("--json", "Write JSON", [Cli.group("format")]),
  Cli.arg("--csv", "Write CSV", [Cli.group("format")]),
  Cli.arg("--sql", "Write SQL statements", [Cli.group("format")]),
])
```

The usage line shows the choice:

```console
$ export -h
Export the database

Usage: export [OPTIONS] <--json|--csv|--sql>
…
$ export --json --csv
error: the argument '--csv' cannot be used with '--json'
```

To turn the flags into one value, read each with `Cli.flag` and pick in the
decoder; `need_one` guarantees one of them is `True`. When the choice is
really a value, `--format <FMT>` with `Cli.one_of` is usually simpler.

## Rules the definition check enforces

- `conflicts` and `requires` must name an id in scope.
- `exclusive` and `need_one` must name a group with members, and every
  `group` must be used by a rule.
- `required()` goes only on options; it cannot be combined with `default`.

Each mistake is a `BadRef`, `Misplaced` or `BadDefault` problem from
[`Cli.check`](testing.md#the-definition-check).

## When a rule depends on a value

"`--out` is required when `--format` is `file`" cannot be declared. Check it
in the decoder after reading both values and use `Cli.fail` with a sentence
in the same style:

```python
Cli.fail(Job, "the argument '--format file' requires '--out <FILE>'")
```

See also: [Defaults and the environment](sources.md),
[Messages](../reference/messages.md).
