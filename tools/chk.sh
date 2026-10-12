#!/usr/bin/env bash
# Purpose: `bend <file> --check-only` with an exact allowlist for known
#   unsafe/foreign diagnostics, so unexpected defs remain visible.
# Expected output: nothing per clean file, the remaining output of each other
#   file under a "== <file>" line, then "chk: <n> ok, <m> with errors";
#   exit 0 when every file is clean, else 1.
# Run: tools/chk.sh [-e expected.tsv] [file.bend...]
#
# With no files it checks every .bend file in the repo but PROOF.bend files
# (bend PROOF.bend checks those), skipping .git, .claude, tmp and build.
# Defaults to tools/chk-expected.tsv, with one
# <repo-relative file><TAB><listed def> per line.
# Only those exact unsafe/foreign diagnostics are hidden; blank lines and
# lines beginning with # are ignored.
# - "N TODOs found" in a LAWS.bend, when N is its number of laws.
set -euo pipefail
BEND_TOOLS_PIN=2.0.36
# shellcheck source=.bend-version.sh
source "$(dirname "${BASH_SOURCE[0]}")/.bend-version.sh"
bend_tools_warn_version "$BEND_TOOLS_PIN" "$(basename "$0")"

root=$(git rev-parse --show-toplevel)
usage() { echo 'usage: tools/chk.sh [-e expected.tsv] [file.bend...]' >&2; exit 2; }
expected_file=$(dirname "${BASH_SOURCE[0]}")/chk-expected.tsv
while getopts e: opt; do
  case $opt in e) expected_file=$OPTARG ;; *) usage ;; esac
done
shift $((OPTIND - 1))
declare -A expected_defs=()
if [ -n "$expected_file" ]; then
  [ -r "$expected_file" ] || { echo "chk: cannot read $expected_file" >&2; exit 2; }
  while IFS=$'\t' read -r path name extra || [ -n "${path:-}${name:-}${extra:-}" ]; do
    [[ $path == \#* || -z $path ]] && continue
    if [ -z "${name:-}" ] || [ -n "${extra:-}" ]; then
      echo "chk: expected tab-separated file and def in $expected_file" >&2
      exit 2
    fi
    expected_defs["$path"$'\t'"$name"]=1
  done <"$expected_file"
fi
if [ $# -eq 0 ]; then
  cd "$root"
  files=()
  while IFS= read -r f; do files+=("$f"); done < <(
    find . \( -path ./.git -o -path ./.claude -o -path ./tmp -o -path ./build \) -prune \
      -o -name '*.bend' ! -name PROOF.bend -print | LC_ALL=C sort)
else
  files=("$@")
fi

ok=0 bad=0
for file in "${files[@]}"; do
  [ -r "$file" ] || { echo "chk: cannot read $file" >&2; bad=$((bad + 1)); continue; }
  file_key=$(cd "$(dirname "$file")" && pwd -P)/$(basename "$file")
  case $file_key in "$root"/*) file_key=${file_key#"$root"/} ;; esac
  out=$(bend "$file" --check-only 2>&1 </dev/null) && rc=0 || rc=$?
  keep=()
  listing=0 todo_ok=0 suppressed=0
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
          if [ -n "${expected_defs["$file_key"$'\t'"${line#- }"]:-}" ]; then
            suppressed=1
            continue
          fi
          line+=': relies on unsafe or foreign code'
        fi ;;
      *) listing=0 ;;
    esac
    case $line in
      'SOME PROOFS FAIL'|'ALL PROOFS CHECK'|'Use --verdict for mathematical validity.') continue ;;
      'Error: '*' TODOs found.'|'Error: '*' TODO found.'|'The code is incomplete, and not a valid proof yet.')
        if [ "$todo_ok" = 1 ]; then suppressed=1; continue; fi ;;
    esac
    keep+=("$line")
  done <<<"$out"
  if [ "${#keep[@]}" -eq 0 ] && { [ "$rc" = 0 ] || [ "$suppressed" = 1 ]; }; then
    ok=$((ok + 1))
  else
    echo "== $file (exit $rc)"
    if [ "${#keep[@]}" -gt 0 ]; then printf '%s\n' "${keep[@]}"; fi
    bad=$((bad + 1))
  fi
done
echo "chk: $ok ok, $bad with errors"
[ "$bad" -eq 0 ]
