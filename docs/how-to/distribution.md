# Building, publishing and upgrading

## Builds

| Target | Build | Run | Needs |
|---|---|---|---|
| native | `bend main.bend -o app` | `./app …` | clang 14+ |
| JavaScript | `bend main.bend -o app.js` | `bun app.js …` | Bun 1.1+ |
| from source | — | `bend main.bend -- …` | Bend |

The library's output bytes are identical on all three. When running from
source, `bend` rejects options before a `--`, so put one in front of the
program's arguments.

macOS (arm64) and Linux (x86-64) are supported. Windows is not.

## Depending on bend-cli

```python
import cli@1.0.0.0/cli.bend as Cli    # app.bend and LAWS.bend
import cli@1.0.0.0/run.bend as Run    # main.bend only
```

Both imports must name the same version; they share one copy of the
library, so `Cli.Cmd` in your app and in `run.bend` are the same type. Bend
fetches the package on first use and checks it against its hash.

## Versions

BendHub versions have four parts, `A.B.C.D`. `A.B.C` is SemVer; `D` counts
republishes of the same source (for example after a license file change).
Imports pin an exact version, so nothing changes until you edit the import.

| Release | May change |
|---|---|
| patch (`1.0.1`) | nothing public: no signature and no output byte |
| minor (`1.1.0`) | adds API; may change help, error, completion or man page text |
| major (`2.0.0`) | public names, types or behavior |

Every minor release lists each output change, before and after, under
"Output changes" in the [changelog](../../CHANGELOG.md).

## Upgrading

1. Change both imports to the new version.
2. Read the changelog's "Output changes" for every version you skip.
3. Run `bend PROOF.bend`. Golden laws for help and errors fail exactly where
   output changed; review each new text and update the law.
4. Rebuild and run your end-to-end tests.

Pinning output in laws is what makes upgrades safe: a minor release cannot
silently change what your users or their scripts see.

## Publishing your own app

A Bend program is published as source:

```console
$ bend login
$ bend main.bend --publish greet@1.0.0.0
```

This uploads `main.bend` and everything it imports, foreign `.c`/`.js` files
and `LICENSE` files beside them. Publishing is public and permanent; put a
`LICENSE` next to `main.bend` first. Users then build it themselves, or you
ship the binaries from your own release process.

Ship generated completions and man pages with binaries:

```console
$ ./app completions bash > dist/app.bash
$ ./app completions zsh > dist/_app
$ ./app completions fish > dist/app.fish
$ ./app man > dist/app.1
```

## CI

A minimal pipeline for an app:

```console
$ bend version                    # fail early on a too-old Bend
$ bend app.bend --check-only
$ bend PROOF.bend --verdict
$ bend main.bend -o build/app
$ bend main.bend -o build/app.js
```

followed by your end-to-end cases against `build/app` and `bun build/app.js`.
