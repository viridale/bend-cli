# Errors and exit codes

## Exit statuses

| Status | Meaning | Output |
|---|---|---|
| 0 | success; also help, version, completions and man pages | stdout |
| 1–255 | whatever `act` returns; 1 means failure by convention | your choice |
| 2 | the user made a mistake on the command line | stderr |
| 70 | the program has a bug: an invalid definition, a `Cli.bug` from the decoder, or `act` returning more than 255 | stderr |

70 is `EX_SOFTWARE` from sysexits(3). Scripts can rely on 2 meaning "fix the
command line" and 70 meaning "report a bug".

Library output never goes to both streams at once. Help asked for with `-h`
goes to stdout, so `app -h | less` works; help printed because the command
line was empty goes to stderr with status 2.

## The shape of a usage error

```
error: <what went wrong>

  tip: <how to fix it>

Usage: <the usage line of the command where it happened>

For more information, try '--help'.
```

There may be several tips or none. On a terminal, `error:` is red, the
quoted input yellow, `tip:` and suggestions green. [Messages](../reference/messages.md)
lists every error and tip with its exact text.

## Failing from the decoder

The parser catches malformed input. Everything else is the decoder's job:

```python
Cli.fail(A, "--since must be before --until")   # usage error, exit 2
Cli.bug(A, "no handler for format 'xml'")       # bug, exit 70
```

`Cli.fail` produces the usage error shape above with your message. Write it
like the library's own messages: lower case, naming the arguments as the user
typed them, without a final period.

`Cli.bug` prints `bug: <msg>` and exits 70. Use it for states that should be
impossible. `Cli.check` runs your decoder on a sample of every command path
and reports every `bug` it reaches, so a `cli_ok` law catches most of them
before release.

## Failing from `act`

`act` returns the exit status. Print your own message to stderr first:

```python
def act(+t: Cli.Term, job: Job) -> IO(U32):
  ...
      case Fail{(code, why)}:
        do IO<U32>:
          IO.print_err(("error: cannot open '" ++ path ++ "': " ++ why : String))
          return 1
```

Conventions worth following:

- start with `error: ` so your messages look like the library's;
- quote names and paths with single quotes;
- return 1 for ordinary failure; use other codes only if you document them;
- never return 2 or 70 from `act` for other reasons: scripts read them as
  "usage error" and "bug".

A status above 255 cannot be represented by the process, so the shell prints
`bug: exit code <n> is out of range 0..255` and exits 70.

## Invalid definitions

If the definition itself is wrong (a duplicate name, a malformed usage string,
a default that does not parse), every run exits 70 with one line per problem,
each naming the command path where it was found:

```
bug: invalid command-line definition
  <command path>: <what is wrong>
```

Do not wait for a user to see this: add the [`cli_ok` law](testing.md#the-definition-check).

## Errors are pure values

`Cli.eval` returns `Exit{code, out, err}` for every outcome above except
`act`'s, with the exact bytes the program prints. That is what makes error
messages testable as laws; see [Testing](testing.md#golden-errors).
