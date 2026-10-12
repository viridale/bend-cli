# Defaults, environment variables and config files

Each argument's value comes from the first source that has one:

1. **argv**: the command line;
2. **the environment**: the variable named by `Cli.env(NAME)`, if it is set
   and not empty;
3. **the default**: `Cli.default(text)`.

Otherwise the argument is absent.

```python
Cli.arg("--registry <URL>", "Registry to fetch from",
  [Cli.env("PKG_REGISTRY"), Cli.default("https://registry.example")])
```

```console
$ pkg add left-pad                                      # https://registry.example
$ PKG_REGISTRY=https://mirror.example pkg add left-pad  # https://mirror.example
$ PKG_REGISTRY= pkg add left-pad                        # empty counts as unset: the default
$ PKG_REGISTRY=https://mirror.example pkg add --registry https://r.example left-pad
                                                        # https://r.example
```

## Defaults

A default is written as text and converted exactly like a command-line value,
so `Cli.default("1")` on an `as_u32` argument is the number 1. A default that
does not convert, or is not one of its `one_of` values, is a definition error
that [`Cli.check`](testing.md) reports. With `Cli.delim`, the default splits
into elements: `Cli.default("80,443")`.

Defaults go on options, list options, optional positionals (`[P]`, `[P]...`)
and `--[no-]` switches. A plain flag is `False` and a count is `0n` when
absent, with no default to set.

Help shows defaults as `[default: v]`.

## Environment variables

`Cli.env(NAME)` works on every kind of argument:

| Kind | The variable is read as |
|---|---|
| flag, `--[no-]` switch | `as_bool`: `true false yes no on off 1 0` |
| count | a whole number |
| option or positional | its value type; split on `delim` if set |

A value that does not convert is a usage error naming the variable:

```console
$ PKG_JOBS=many pkg build
error: invalid value 'many' for '--jobs <N>' from environment variable PKG_JOBS: expected a whole number from 0 to 4294967295
```

Help shows `[env: NAME]` but never the variable's current value, which might
be a secret. Man pages list every variable in an ENVIRONMENT section.

The shell reads only the variables your definition names, plus the ones that
control output: `NO_COLOR`, `CLICOLOR`, `CLICOLOR_FORCE`, `TERM` and
`COLUMNS`. `Cli.vars(cli())` returns that list.

## Which source did a value come from?

```python
from : Cli.Src <- Cli.source(m, "registry")
```

gives `Cli.Argv{}`, `Cli.Env{}`, `Cli.Default{}` or `Cli.Absent{}`.
`Cli.given(m, id)` is `True` for argv or the environment.

## How sources affect requirements and relations

- `Cli.required()` is satisfied by argv or the environment, never by a
  default. The definition check rejects `required()` with `default`.
- `conflicts`, `requires`, `exclusive` and `need_one` see only arguments
  given in argv or the environment. A default never causes a conflict and
  never satisfies a requirement.

So `--registry` with a default and `--offline` with
`Cli.conflicts("registry")` work together: the conflict fires only when the
user sets a registry.

## Layering a config file

bend-cli does not read config files; your action does. To put a config file
between the environment and the default, keep the default on the argument (so
help shows it) and record where the value came from:

```python
type Opt is Data:
  Opt{value: String, from: Cli.Src}

def opt(+m: Cli.Matches, +id: String) -> Cli.Dec(Opt):
  do Cli.Dec<Opt>:
    value : String <- Cli.str(m, id)
    from : Cli.Src <- Cli.source(m, id)
    return Opt{value, from}
```

Then, in `act`, after reading the file:

```python
# argv and env beat the file; the file beats the default
def pick(from: Cli.Src, value: String, file: Maybe<&2, String>) -> String:
  match from:
    case Cli.Default{}:
      Maybe.default(&2, String, file, value)
    case _:
      value

def layer(o: Opt, file: Maybe<&2, String>) -> String:
  match o:
    case Opt{value, from}:
      pick(from, value, file)
```

`layer` is pure, so a law can pin the precedence:

```python
law file_beats_default:
  {App.layer(App.Opt{"a", Cli.Default{}}, Some{"b"}) == "b" : String}

law env_beats_file:
  {App.layer(App.Opt{"a", Cli.Env{}}, Some{"b"}) == "a" : String}
```

A `--config <FILE>` option with its own `Cli.env("APP_CONFIG")` lets users
choose the file.

See also: [Required arguments and relations](relations.md),
[Parsing rules](../reference/parsing.md#sources).
