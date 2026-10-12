#!/usr/bin/env bash
# Purpose: `bend <file> --check-only` that hides the failures a file is
#   expected to have, so only real errors print.
# Expected output: nothing per clean file, the remaining output of each other
#   file under a "== <file>" line, then "chk: <n> ok, <m> with errors";
#   exit 0 when every file is clean, else 1.
# Run: tools/chk.sh [file.bend...]
#
# With no files it checks every .bend file in the repo but PROOF.bend files
# (bend PROOF.bend checks those), skipping .git, .claude, tmp and build.
# Expected failures:
# - "N defs rely on unsafe or foreign code": a listed def is expected when
#   its file reaches user effects (has a def whose body imports a .c or .js
#   file, or imports a .bend file that does) and is not itself @unsafe or a
#   `def f?(`. Base's effects are never listed.
# - "N TODOs found" in a LAWS.bend, when N is its number of laws.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
if [ $# -eq 0 ]; then
  cd "$root"
  files=()
  while IFS= read -r f; do files+=("$f"); done < <(
    find . \( -path ./.git -o -path ./.claude -o -path ./tmp -o -path ./build \) -prune \
      -o -name '*.bend' ! -name PROOF.bend -print | LC_ALL=C sort)
else
  files=("$@")
fi

# reaches <file>: whether file defines or imports a foreign effect. The
# answers are cached by path in $reach; cycles do not occur in Bend.
reach=$'\n'
reaches() {
  local f dir dep
  f=$(cd "$(dirname "$1")" && pwd -P)/$(basename "$1")
  case $reach in *$'\n'"+$f"$'\n'*) return 0 ;; *$'\n'"-$f"$'\n'*) return 1 ;; esac
  if LC_ALL=C grep -Eq '^[ \t]+import "[^"]+\.(c|js)"' "$f"; then
    reach+="+$f"$'\n'; return 0
  fi
  dir=$(dirname "$f")
  while IFS= read -r dep; do
    if [ -r "$dir/$dep" ] && reaches "$dir/$dep"; then
      reach+="+$f"$'\n'; return 0
    fi
  done < <(LC_ALL=C sed -nE 's/^import (\.{1,2}\/[^ ]+\.bend)( .*)?$/\1/p' "$f")
  reach+="-$f"$'\n'
  return 1
}

# expected <file> <listed name>: whether a def in the unsafe/foreign list is
# expected. A name is "<path>.<def>" with the path relative to file and
# without .bend, or a def of file itself; module names have no dots.
expected() {
  local file=$1 name=$2 dir path rest mod def
  dir=$(dirname "$file") mod=$file def=$name path='' rest=$name
  while [[ $rest == *.* ]]; do
    path+=${rest%%.*} rest=${rest#*.}
    if [ -f "$dir/$path.bend" ]; then mod=$dir/$path.bend def=$rest; break; fi
    path+=.
  done
  reaches "$mod" || return 1
  ! LC_ALL=C grep -Fq -e "@unsafe def $def(" -e "def $def?(" "$mod"
}

ok=0 bad=0
for file in "${files[@]}"; do
  [ -r "$file" ] || { echo "chk: cannot read $file" >&2; bad=$((bad + 1)); continue; }
  out=$(bend "$file" --check-only 2>&1 </dev/null) && rc=0 || rc=$?
  keep=()
  listing=0 todo_ok=0
  if [ "$(basename "$file")" = LAWS.bend ]; then
    n=$(LC_ALL=C grep -c '^law ' "$file" || true)
    [[ $out == *"Error: $n TODOs found."* || $out == *"Error: $n TODO found."* ]] && todo_ok=1
  fi
  while IFS= read -r line; do
    case $line in
      'Error: '*' defs rely on unsafe or foreign code:'|'Error: '*' def relies on unsafe or foreign code:')
        listing=1; continue ;;
      '- '*)
        if [ "$listing" = 1 ]; then
          expected "$file" "${line#- }" && continue
          line+=': relies on unsafe or foreign code'
        fi ;;
      *) listing=0 ;;
    esac
    case $line in
      'SOME PROOFS FAIL'|'ALL PROOFS CHECK'|'Use --verdict for mathematical validity.') continue ;;
      'Error: '*' TODOs found.'|'Error: '*' TODO found.'|'The code is incomplete, and not a valid proof yet.')
        [ "$todo_ok" = 1 ] && continue ;;
    esac
    keep+=("$line")
  done <<<"$out"
  if [ "${#keep[@]}" -eq 0 ] && { [ "$rc" = 0 ] || [[ $out == 'SOME PROOFS FAIL'* ]]; }; then
    ok=$((ok + 1))
  else
    echo "== $file (exit $rc)"
    if [ "${#keep[@]}" -gt 0 ]; then printf '%s\n' "${keep[@]}"; fi
    bad=$((bad + 1))
  fi
done
echo "chk: $ok ok, $bad with errors"
[ "$bad" -eq 0 ]
