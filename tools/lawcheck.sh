#!/usr/bin/env bash
# Purpose: check that new laws type-check against planned signatures before
#   their code exists, and that each adds exactly one TODO over a base ref.
# Expected output: "lawcheck: +<n> TODOs = <n> new laws: <names>", exit 0;
#   else the checker's output or the mismatch, exit 1.
# Run: tools/lawcheck.sh [-b main] [-l LAWS.bend] [-m cli.bend] [-p] [stub.bend]
#
# The worktree (less .git, .claude, tmp and build) is copied to
# tmp/lawcheck/new and the base ref is extracted to tmp/lawcheck/base. The
# stub holds the planned defs, with ?TODO bodies, and is appended to the
# module (-m) in the copy, so every importer of the module (demo.bend and
# LAWS.bend alike) sees one module with the planned signatures; a separate
# module would give its types distinct names. TODOs in the module itself,
# the stub's included, are counted apart and subtracted on both sides.
# -p then plants a law with a type error and requires the check to reject
# it, so a passing count is not vacuous.
set -euo pipefail

usage() {
  echo 'usage: tools/lawcheck.sh [-b ref] [-l laws.bend] [-m module.bend] [-p] [stub.bend]' >&2
  exit 2
}
ref=main laws=LAWS.bend module=cli.bend plant=0
while getopts b:l:m:p opt; do
  case $opt in
    b) ref=$OPTARG ;;
    l) laws=$OPTARG ;;
    m) module=$OPTARG ;;
    p) plant=1 ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ $# -le 1 ] || usage
stub=${1:-}
if [ -n "$stub" ]; then
  [ -r "$stub" ] || { echo "lawcheck: cannot read $stub" >&2; exit 2; }
  stub=$(cd "$(dirname "$stub")" && pwd)/$(basename "$stub")
fi

root=$(git rev-parse --show-toplevel)
cd "$root"
[ -r "$laws" ] || { echo "lawcheck: cannot read $laws" >&2; exit 2; }
[ -r "$module" ] || { echo "lawcheck: cannot read $module" >&2; exit 2; }
git rev-parse -q --verify "$ref^{commit}" >/dev/null ||
  { echo "lawcheck: no commit $ref" >&2; exit 2; }

work=tmp/lawcheck
rm -rf "$work"
mkdir -p "$work/base" "$work/new"
git archive "$ref" | tar -x -C "$work/base"
rsync -a --exclude=/.git --exclude=/.claude --exclude=/tmp --exclude=/build \
  ./ "$work/new/"
if [ -n "$stub" ]; then
  printf '\n' >>"$work/new/$module"
  cat "$stub" >>"$work/new/$module"
fi

# todos <file>: prints the file's TODO count; on any other failure prints
# the checker's output to stderr and returns 1.
todos() {
  local out
  out=$(bend "$1" --check-only 2>&1 </dev/null) || true
  if [[ $out =~ (^|$'\n')Error:\ ([0-9]+)\ TODOs?\ found\. ]]; then
    echo "${BASH_REMATCH[2]}"
  elif [[ $out == 'ALL PROOFS CHECK'* ]]; then
    echo 0
  else
    printf 'lawcheck: %s does not type-check:\n%s\n' "${1#"$work"/}" "$out" >&2
    return 1
  fi
}
names() {
  [ -r "$1" ] || return 0
  LC_ALL=C sed -nE 's/^law ([A-Za-z0-9_]+):.*/\1/p' "$1" | LC_ALL=C sort
}

base_mod=0 base_laws=0
if [ -r "$work/base/$module" ]; then base_mod=$(todos "$work/base/$module"); fi
if [ -r "$work/base/$laws" ]; then base_laws=$(todos "$work/base/$laws"); fi
new_mod=$(todos "$work/new/$module")
new_laws=$(todos "$work/new/$laws")

removed=$(LC_ALL=C comm -23 <(names "$work/base/$laws") <(names "$work/new/$laws"))
added=$(LC_ALL=C comm -13 <(names "$work/base/$laws") <(names "$work/new/$laws"))
n_added=$(printf '%s' "$added" | grep -c . || true)
added=$(printf '%s' "$added" | paste -sd ' ' -)
removed=$(printf '%s' "$removed" | paste -sd ' ' -)
delta=$(( (new_laws - new_mod) - (base_laws - base_mod) ))

echo "lawcheck: $ref $laws: $base_laws TODOs ($base_mod in $module)"
echo "lawcheck: worktree$([ -n "$stub" ] && echo ' + stub') $laws: $new_laws TODOs ($new_mod in $module)"
status=0
if [ -n "$removed" ]; then
  echo "lawcheck: laws removed or renamed since $ref: $removed"
  status=1
fi
if [ "$delta" -ne "$n_added" ]; then
  echo "lawcheck: +$delta TODOs but $n_added new laws: $added"
  status=1
else
  echo "lawcheck: +$delta TODOs = $n_added new laws: $added"
fi

if [ "$plant" = 1 ]; then
  printf '\nlaw lawcheck_planted:\n  {0n == "planted" : Nat}\n' >>"$work/new/$laws"
  if out=$(todos "$work/new/$laws" 2>&1); then
    echo "lawcheck: planted type error was not rejected ($out TODOs)"
    status=1
  else
    echo "lawcheck: planted type error rejected:"
    printf '%s\n' "$out" | grep -E '^- ' | head -3
  fi
fi
exit "$status"
