# Attributes

Attributes are `Cli.Item`s in the item list of a command (`Cli.cmd`,
`Cli.sub`) or an argument (`Cli.arg`). "Where" lists the only valid
positions; anywhere else, `Cli.check` reports `Misplaced`.

## On commands

| Builder | Where | Effect | Guide |
|---|---|---|---|
| `version(v: String)` | root | adds `-V, --version`, printing `<name> <v>` | [help](../how-to/help.md#--version) |
| `alias(n: String)` | subcommand | another name for it | [subcommands](../how-to/subcommands.md#aliases-and-hidden-subcommands) |
| `hidden()` | subcommand | parses, but omitted from help, completions, man pages, suggestions | [help](../how-to/help.md#hiding-things) |
| `example(line: String, what: String)` | command | an entry under `Examples:` and in the man page | [help](../how-to/help.md#examples-and-closing-text) |
| `after(text: String)` | command | paragraphs after all help sections | [help](../how-to/help.md#examples-and-closing-text) |
| `sub_optional()` | command with subcommands | the command may run without one | [subcommands](../how-to/subcommands.md#required-or-optional-subcommand) |
| `external()` | command with subcommands | an unknown subcommand and every later token are kept | [wrappers](../how-to/wrappers.md#git-style-plugins-external) |
| `exclusive(g: String)` | command | at most one member of group `g` | [relations](../how-to/relations.md#groups) |
| `need_one(g: String)` | command | at least one member of group `g` | [relations](../how-to/relations.md#groups) |

## On arguments

| Builder | Where | Effect | Guide |
|---|---|---|---|
| `id(s: String)` | any | explicit id | [usage strings](usage-strings.md#ids) |
| `alias(n: String)` | flag or option | another `--long` or `-s`, written with dashes | [flags](../how-to/flags.md#another-spelling) |
| `hidden()` | any | parses, but omitted from help, completions, man pages, suggestions | [help](../how-to/help.md#hiding-things) |
| `required()` | option, list option | must come from argv or the environment | [relations](../how-to/relations.md#required-options) |
| `default(v: String)` | option, list option, `[P]`, `[P]...`, negatable | value when absent; must convert | [sources](../how-to/sources.md#defaults) |
| `env(name: String)` | any | environment fallback | [sources](../how-to/sources.md#environment-variables) |
| `global()` | flag or option | valid in every descendant command | [subcommands](../how-to/subcommands.md#options-and-scope) |
| `heading(h: String)` | flag or option | help section title instead of `Options` | [options](../how-to/options.md#grouping-options-in-help) |
| `as_nat()` `as_u32()` `as_f32()` `as_bool()` | takes a value | value type, checked while parsing | [values](../how-to/values.md) |
| `as_file()` `as_dir()` | takes a value | string; completes files or directories | [values](../how-to/values.md) |
| `one_of(xs: List<&2, String>)` | takes a value | the value must be one of `xs` | [values](../how-to/values.md#choices-mapped-to-your-own-type) |
| `delim(c: Char)` | list option, variadic | splits each value on `c` | [options](../how-to/options.md#delimited-lists) |
| `hyphen()` | takes a value | accepts values that start with `-` | [positionals](../how-to/positionals.md#values-that-start-with--) |
| `rest()` | last positional, variadic | from its first value on, every token is a value | [wrappers](../how-to/wrappers.md) |
| `bare(v: String)` | `--x[=<V>]` (required there) | the value of `--x` given without `=` | [options](../how-to/options.md#an-optional-value) |
| `conflicts(id: String)` | any | may not be present with `id`; symmetric | [relations](../how-to/relations.md#conflicts) |
| `requires(id: String)` | any | when present, `id` must be present | [relations](../how-to/relations.md#dependencies) |
| `group(g: String)` | any | member of group `g` | [relations](../how-to/relations.md#groups) |

"Takes a value" means an option, list option, optional-value option or
positional. An argument has at most one value type (`as_*`); `one_of` may be
combined with a value type.

## Built-in items

| Builder | Expands to |
|---|---|
| `color()` | `arg("--color <WHEN>", "When to use color", [one_of(["auto", "always", "never"]), default("auto"), global()])`, whose value also drives the library's color |
| `completions()` | subcommand `completions <SHELL>` (`bash`, `zsh`, `fish`), "Print a shell completion script" |
| `man()` | hidden subcommand `man [COMMAND]...`, "Print the man page" |

`completions()` and `man()` behave as subcommands for scanning, help and
lint, but only `Cli.eval` acts on them: decoders, `route` tables and
`Cli.check` never see them. A `Cli.sub` with the same name is an ordinary
subcommand.

## Built in to every command

You do not declare these; they are reserved:

- `-h, --help` on every command (`-h` is yours if you declare it);
- `-V, --version` on the root when `version` is set (`-V` is yours if you
  declare it);
- the `help` subcommand on every command that has subcommands.
