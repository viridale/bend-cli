#!/usr/bin/env bash
# Purpose: completion scripts in real shells, and man pages through mandoc
# (§11). For each shell named, load the pkg script (build/pkg completions)
# and the fixtures' (tests/complete/fixtures.bend) into that shell, complete
# the input of each line of tests/complete/<cmd>.<shell>.txt, and compare
# with the file; `man` lints every page of pkg and the fixtures.
# Expected output: `ok <file>` for each file checked, and exit 0; otherwise a
# diff for each file that differs, and exit 1. A line's input is the text
# before its first ` => `; build/complete/<cmd>.<shell>.got has the output.
# Run: tests/complete/run.sh [bash] [zsh] [fish] [man], from the repository
#   root after building build/pkg. BASH_CMD starts the bash under test (see
#   bash.zsh); a container must mount the repository at the same path, as
#   in BASH_CMD="docker run --rm -it -v $PWD:$PWD bash:4.4 bash".
set -euo pipefail

root=$PWD
dir=$root/tests/complete
work=$root/build/complete
rm -rf "$work"
# The shells run in cwd, which holds only the tree the cases complete in.
mkdir -p "$work/cwd/sand/dir1" "$work/cwd/sand/dir2"
: > "$work/cwd/sand/file1"

for shell in bash zsh fish; do
  build/pkg completions "$shell" > "$work/pkg.$shell"
done
build/pkg man > "$work/pkg.1"
for sub in add remove list run completions; do
  build/pkg man "$sub" > "$work/pkg-$sub.1"
done
bend tests/complete/fixtures.bend |
  awk -v dir="$work" '/^@@/ { f = dir "/" substr($0, 3); next } { print > f }'

failed=0
# compare WANT GOT: reports whether the output GOT matches WANT.
compare() {
  if cmp -s "$1" "$2"; then
    echo "ok ${1#"$root"/}"
  else
    echo "FAIL ${1#"$root"/}:"
    diff "$1" "$2" || true
    failed=1
  fi
}

# complete_in SHELL CMD: runs the inputs of CMD.SHELL.txt in SHELL.
complete_in() {
  local want=$dir/$2.$1.txt got=$work/$2.$1.got
  sed 's/ => .*//' "$want" > "$work/$2.$1.in"
  case $1 in
    bash) (cd "$work/cwd" && zsh -f "$dir/bash.zsh" "$work/$2.bash" "$2") ;;
    zsh) mkdir -p "$work/fp-$2"
         cp "$work/$2.zsh" "$work/fp-$2/_$2"
         (cd "$work/cwd" && zsh -f "$dir/zsh.zsh" "$work/fp-$2") ;;
    fish) (cd "$work/cwd" && fish "$dir/fish.fish" "$work/$2.fish") ;;
  esac < "$work/$2.$1.in" > "$got"
  compare "$want" "$got"
}

for what in "$@"; do
  case $what in
    bash|zsh|fish)
      for cmd in pkg my-tool launch; do complete_in "$what" "$cmd"; done ;;
    man)
      # The header has no date on purpose (§11.2), so that warning is
      # expected; anything else at style level or above fails.
      for page in "$work"/*.1; do
        lint=$(mandoc -T lint -W style "$page" 2>&1 |
          grep -v ': missing date' || true)
        if [ -z "$lint" ]; then
          echo "ok ${page#"$root"/}"
        else
          printf 'FAIL %s:\n%s\n' "${page#"$root"/}" "$lint"
          failed=1
        fi
      done ;;
    *) echo "run.sh: unknown test $what" >&2; exit 2 ;;
  esac
done
exit "$failed"
