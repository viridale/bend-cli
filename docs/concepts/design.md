# Design choices

bend-cli has four goals, in this order:

1. **Checkable.** Every decision is a pure, total function, so a CLI's
   definition, decoder, help text and error output can be stated and proved
   as laws.
2. **Excellent by default.** Help and errors are clear and complete, with
   suggestions and convention-following color, and need no configuration.
3. **Small and regular.** One import for the pure API, one for the shell, and
   names you can guess.
4. **Honest about the platform.** Nothing depends on `@unsafe`; what the Bend
   runtime does to argv and exit is documented, not hidden.

Most choices below follow from the first two.

## What it rejects, and why

### No abbreviations or prefix matching

`--verb` does not mean `--verbose`, and `git rem` does not mean
`git remote`. If abbreviations were accepted, adding `--version` later would
silently change what `--ver` means in someone's script. bend-cli matches
names exactly and suggests the closest names instead.

### The last occurrence wins

A single-valued option given twice keeps its last value rather than raising
an error, so a shell alias can set a default the user overrides:
`alias ls='ls --color=auto'`, then `ls --color=never`.

### One value per occurrence

An option takes exactly one value each time it appears. `-I a b` gives `-I`
the value `a` and makes `b` a positional. If an option could swallow
several tokens, nobody could tell, by reading a command line, where its
values end and the positionals begin. Use a repeated option (`-I a -I b`)
or a delimiter (`--tags a,b`) instead. See
[Options](../how-to/options.md#repeated-values).

### No positionals next to subcommands

A command has positionals or subcommands, not both. With both, `app build`
could be the subcommand `build` or a file named `build`. The definition
check reports `Mixed`.

### Errors instead of panics

A mistake in the definition, such as a bad usage string, a duplicate name or
a default that does not convert, is a `Problem`, not a crash. `Cli.check`
returns them so one law proves there are none, and if one slips through,
the program exits 70 with the list.

### Environment values never appear in help

Help shows `[env: TOKEN]`, never the variable's current value, because the
value may be a secret and help output gets pasted into bug reports.

### No derive

Bend has no derive or reflection, so the definition is a value and the
decoder is a function. `Cli.check` gives the guarantee a derive would: the
decoder reads only names the definition declares, with the right types.

## Out of scope for 1.x

- prompts and passwords;
- progress bars, spinners and tables;
- config files (layer them yourself with `Cli.source`; see
  [Sources](../how-to/sources.md#layering-a-config-file));
- several values per occurrence;
- dynamic completions computed by the program;
- PowerShell, Elvish and Nushell completion scripts;
- Markdown docs generated from the definition;
- translated messages;
- Windows.

Each of these is a decision for 1.x, not a promise for later. The project's
backlog records which may be revisited.

## What bend-cli is not

If you need a parser that accepts anything a 1980s Unix tool accepted
(`-long` options, `+x` flags, abbreviations, options that take a variable
number of values), bend-cli will refuse some of it on purpose. What you get
in return is that every command line has one reading, the program can prove
which, and the help and errors are good without configuration.
