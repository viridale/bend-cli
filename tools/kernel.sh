#!/usr/bin/env bash
# Purpose: run --verdict's proven kernel by hand, to name the def it rejects
#   and why ("out of fuel", or the expected and observed terms), which
#   --verdict itself does not print.
# Expected output: "kernel: ALL PROOFS CHECK", exit 0; or "kernel: <def>:
#   <reason>" with the reason's lines, exit 1.
# Run: tools/kernel.sh [-t secs] [PROOF.bend]
#
# The file is translated into a unique tmp/kernel.* directory.
# The kernel is $BENDTT when set, as for bend; else the one bend built at
# ~/.bend/bendtt/<hash>/bendtt, where <hash> is the first 16 hex digits of
# sha256(<LEAN_VERSION> NUL <bendtt.lean>), LEAN_VERSION read from the bend
# binary and bendtt.lean from the bend2 directory beside its bin directory.
set -euo pipefail
BEND_TOOLS_PIN=2.0.37
# shellcheck source=.bend-version.sh
source "$(dirname "${BASH_SOURCE[0]}")/.bend-version.sh"
bend_tools_warn_version "$BEND_TOOLS_PIN" "$(basename "$0")"

usage() { echo 'usage: tools/kernel.sh [-t secs] [file.bend]' >&2; exit 2; }
secs=1800
while getopts t: opt; do
  case $opt in
    t) secs=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ $# -le 1 ] || usage
src=${1:-PROOF.bend}
[ -r "$src" ] || { echo "kernel: cannot read $src" >&2; exit 2; }

root=$(git rev-parse --show-toplevel)
mkdir -p "$root/tmp"
work=$(mktemp -d "$root/tmp/kernel.XXXXXX")
trap 'rm -rf "$work"' EXIT
name=$(basename "$src" .bend)
tt=$work/$name.bendtt

if [ -n "${BENDTT:-}" ]; then
  kernel=$BENDTT
else
  bend=$(command -v bend) || { echo 'kernel: bend is not on PATH' >&2; exit 2; }
  while [ -L "$bend" ]; do
    link=$(readlink "$bend")
    case $link in /*) bend=$link ;; *) bend=$(dirname "$bend")/$link ;; esac
  done
  lean=$(dirname "$bend")/../bend2/bendtt.lean
  version=$(LC_ALL=C grep -a -o -m 1 'LEAN_VERSION = "[0-9.]*"' "$bend" |
    head -n 1 | cut -d'"' -f2)
  [ -n "$version" ] || { echo "kernel: no LEAN_VERSION in $bend" >&2; exit 2; }
  [ -r "$lean" ] || { echo "kernel: cannot read $lean" >&2; exit 2; }
  if command -v sha256sum >/dev/null; then sha=(sha256sum); else sha=(shasum -a 256); fi
  hash=$({ printf '%s\0' "$version"; cat "$lean"; } | "${sha[@]}" | cut -c1-16)
  kernel=$HOME/.bend/bendtt/$hash/bendtt
  if [ ! -x "$kernel" ]; then
    echo "kernel: no kernel at $kernel (Lean $version); run bend $src --verdict once to build it" >&2
    exit 2
  fi
  # bend copies the source beside the kernel it builds; a mismatch means the
  # derivation above no longer matches bend's.
  cmp -s "$lean" "$(dirname "$kernel")/bendtt.lean" ||
    { echo "kernel: $kernel was not built from $lean" >&2; exit 2; }
fi
echo "kernel: $kernel"

out=$(bend "$src" -o "$tt" 2>&1 </dev/null) || {
  printf 'kernel: bend %s -o %s failed:\n%s\n' "$src" "$tt" "$out"
  exit 1
}
[ -z "$out" ] || printf '%s\n' "$out"
[ -s "$tt" ] || { echo "kernel: bend wrote no $tt" >&2; exit 1; }

# bend runs the kernel with a 4 GB Lean stack; it reads only its argument.
got=$(LEAN_STACK_SIZE_KB=4194304 timeout "$secs" "$kernel" "$tt" 2>&1) && rc=0 || rc=$?
if [ "$rc" = 124 ]; then
  echo "kernel: timed out after ${secs}s on $tt"
  exit 1
fi
if [ "$rc" = 0 ] && [ "$got" = 'ALL PROOFS CHECK' ]; then
  echo 'kernel: ALL PROOFS CHECK'
  exit 0
fi
# The kernel prints "SOME PROOFS FAIL", "In <def>:" and the reason; terms in
# an expected/observed pair can be long, so each line is cut at 400 bytes.
def=$(printf '%s\n' "$got" | LC_ALL=C sed -nE 's/^In (.*):$/\1/p' | head -n 1)
if [ -z "$def" ]; then
  printf 'kernel: exit %s:\n%s\n' "$rc" "$got"
  exit 1
fi
reason=$(printf '%s\n' "$got" | LC_ALL=C sed -n '/^In .*:$/,$p' | sed 1d)
first=$(printf '%s\n' "$reason" | head -n 1)
echo "kernel: $def: ${first:0:400}"
printf '%s\n' "$reason" | sed 1d | LC_ALL=C cut -c1-400 | sed 's/^/  /'
exit 1
