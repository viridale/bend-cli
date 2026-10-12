# Environment variables

The shell (`Run.host`) reads only the variables your definition names with
`Cli.env`, plus these. `Cli.vars(c)` returns the full list.

| Variable | Effect |
|---|---|
| `NO_COLOR` | set and not empty: no color, unless `--color` says otherwise |
| `CLICOLOR_FORCE` | set, not empty and not `0`: color even when not a terminal |
| `CLICOLOR` | `0`: no color |
| `TERM` | `dumb`: no color |
| `COLUMNS` | a whole number ≥ 1: the terminal width, before probing the terminal |

The [color rules](../how-to/terminal.md#color) give the full precedence.

For variables named by `Cli.env`:

- an empty value counts as unset;
- the value is converted like a command-line value, and a failure is an
  error naming the variable;
- help shows `[env: NAME]`, never the value;
- man pages list each variable under ENVIRONMENT.

The Bend runtime itself reads no variables that affect parsing.
