# Purpose: the completion scripts and man pages of LAWS.bend's quirks() and
# launch() fixtures, for tests/complete/run.sh to load into real shells and
# lint (§11). The specs repeat LAWS.bend's, which pins their bytes.
# Expected output: each file as a line `@@<file>` and then its text.
# `--check-only` prints ALL PROOFS CHECK.
# Run: bend tests/complete/fixtures.bend

import Base
import ../../cli.bend as Cli

def quirks() -> Cli.Cmd:
  Cli.cmd("my-tool",
    "It's a \"tool\": [all] of it\n\nSecond paragraph.\n.A hard break", [
    Cli.version("2.0-rc.1"),
    Cli.arg("-q, --[no-]quiet", "Say less\n\n'Quoted' second paragraph",
      [Cli.global(), Cli.env("MY_QUIET")]),
    Cli.arg("--mode[=<M>]", "Pick a mode: [a] or b",
      [Cli.one_of(["it's", "a b", "$x", "c:d", "e\\f"]), Cli.bare("a b")]),
    Cli.arg("--key <K>", "Secret", [Cli.hidden()]),
    Cli.arg("-o, --out <FILE>", "Write to FILE",
      [Cli.as_file(), Cli.alias("--output"), Cli.heading("Output")]),
    Cli.sub("remote", "Manage remotes", [
      Cli.alias("rem"),
      Cli.sub("add", "Add a remote", [
        Cli.arg("-t, --tag <T>...", "Tag the remote", []),
        Cli.arg("<NAME>", "Remote name", []),
        Cli.arg("[DIR]", "Where to clone", [Cli.as_dir()]),
      ]),
      Cli.sub("prune", "Prune remotes", [Cli.hidden()]),
    ]),
    Cli.example("my-tool --mode='it'\\''s' rem add x", "Quote a mode"),
    Cli.example("my-tool -q", "Be quiet"),
    Cli.after("'Quoted' notes\\with a backslash"),
  ])

def launch() -> Cli.Cmd:
  Cli.cmd("launch", "Start a program", [
    Cli.arg("-n, --dry-run", "Print the command instead", []),
    Cli.arg("<PROG>", "Program to start", [Cli.as_file()]),
    Cli.arg("[ARGS]...", "Arguments for the program",
      [Cli.rest(), Cli.as_file()]),
  ])

def file(name: String, text: String) -> String:
  String.concat(["@@", name, "\n", text])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.write(String.concat([
      file("my-tool.bash", Cli.script(quirks(), Cli.Bash{})),
      file("my-tool.zsh", Cli.script(quirks(), Cli.Zsh{})),
      file("my-tool.fish", Cli.script(quirks(), Cli.Fish{})),
      file("launch.bash", Cli.script(launch(), Cli.Bash{})),
      file("launch.zsh", Cli.script(launch(), Cli.Zsh{})),
      file("launch.fish", Cli.script(launch(), Cli.Fish{})),
      file("my-tool.1", Cli.roff(quirks(), [])),
      file("my-tool-remote.1", Cli.roff(quirks(), ["remote"])),
      file("my-tool-remote-add.1", Cli.roff(quirks(), ["remote", "add"])),
      file("my-tool-remote-prune.1", Cli.roff(quirks(), ["remote", "prune"])),
      file("launch.1", Cli.roff(launch(), [])),
    ]))
