#!/usr/bin/env bash
# Purpose: check each law of a proof or probe file in its own file, since
#   the checker stops at the first failure, and show every failure at once.
# Expected output: a line per law, "ok", "OPEN" (it left TODOs), "FAIL" with
#   the checker's expected/observed lines, or "TIMEOUT"; then a summary.
#   Exit 0 when every law is ok, else 1.
# Run: tools/perlaw.sh [-j jobs] [-t secs] PROOF.bend [name-regex]
#
# A law unit is a local "law x:" with its "def x", or a "def A.x" that fills
# law x of a file imported as A. The base file keeps every other block
# (imports, types, lemmas) and each law file adds one unit; either also
# keeps any unit its blocks call. Both go to a copy of the repo (less .git,
# .claude, tmp and build) under a unique tmp/perlaw.* directory, at the
# source's own path, so relative imports resolve. A law is ok when its file leaves exactly the
# base's TODOs less the imported laws it fills.
set -euo pipefail
BEND_TOOLS_PIN=2.0.36
# shellcheck source=.bend-version.sh
source "$(dirname "${BASH_SOURCE[0]}")/.bend-version.sh"
bend_tools_warn_version "$BEND_TOOLS_PIN" "$(basename "$0")"

usage() {
  echo 'usage: tools/perlaw.sh [-j jobs] [-t secs] <file.bend> [name-regex]' >&2
  exit 2
}
jobs=4 secs=60
while getopts j:t: opt; do
  case $opt in
    j) jobs=$OPTARG ;;
    t) secs=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ $# -ge 1 ] && [ $# -le 2 ] || usage
src=$1 pick=${2:-}
[ -r "$src" ] || { echo "perlaw: cannot read $src" >&2; exit 2; }
src=$(cd "$(dirname "$src")" && pwd -P)/$(basename "$src")
root=$(git rev-parse --show-toplevel)
root=$(cd "$root" && pwd -P)
case $src in
  "$root"/*) rel=${src#"$root"/} ;;
  *) echo "perlaw: $src is outside the repo $root" >&2; exit 2 ;;
esac

mkdir -p "$root/tmp"
work=$(mktemp -d "$root/tmp/perlaw.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/tree" "$work/run"
rsync -a --exclude=/.git --exclude=/.claude --exclude=/tmp --exclude=/build \
  "$root/" "$work/tree/"
dir=$work/tree/$(dirname "$rel")
mkdir -p "$dir"

# Laws that imports declare, as Alias.name, for telling a fill from a def.
srcdir=$(dirname "$src")
while read -r path alias; do
  [ -r "$srcdir/$path" ] || continue
  LC_ALL=C sed -nE "s/^law ([A-Za-z0-9_]+):.*/$alias.\1/p" "$srcdir/$path"
done < <(LC_ALL=C sed -nE 's/^import (\.{1,2}\/[^ ]+\.bend) as ([A-Za-z0-9_]+).*/\1 \2/p' "$src") \
  >"$work/imported"

# Splits src into numbered files and lists "<id> <fills> <unit>" in
# $work/units, base first. IDs avoid collisions between qualified law names.
LC_ALL=C awk -v dir="$dir" -v pick="$pick" -v list="$work/units" \
    -v laws="$work/imported" '
  BEGIN { while ((getline l < laws) > 0) imported[l] = 1 }
  /^(@unsafe[ \t]+)?(def|law|type|import)[ \t]/ {
    nb++
    if (match($0, /^(@unsafe[ \t]+)?(def|law)[ \t]+[^ \t(:?]+/)) {
      s = substr($0, RSTART, RLENGTH); sub(/^.*[ \t]/, "", s)
      kind[nb] = $0 ~ /^law/ ? "law" : "def"; name[nb] = s
    }
  }
  { text[nb] = text[nb] $0 "\n" }
  END {
    for (b = 1; b <= nb; b++) if (kind[b] == "law") local[name[b]] = 1
    for (b = 1; b <= nb; b++) {
      if (name[b] in local) unit[b] = name[b]
      else if (kind[b] == "def" && name[b] in imported) {
        unit[b] = name[b]; fills[name[b]] = 1
      }
      if (unit[b] != "" && !(unit[b] in seen)) { seen[unit[b]] = 1; order[++nu] = unit[b] }
    }
    # calls[b, u]: block b names unit u as a call.
    for (b = 1; b <= nb; b++)
      for (i = 1; i <= nu; i++) {
        u = order[i]; t = " " text[b]
        if (unit[b] == u) continue
        while ((k = index(t, u "(")) > 0) {
          if (substr(t, k - 1, 1) !~ /[A-Za-z0-9_.]/) { calls[b, u] = 1; break }
          t = substr(t, k + 1)
        }
      }
    emit("_base", "")
    for (i = 1; i <= nu; i++)
      if (pick == "" || order[i] ~ pick) emit(order[i], order[i])
  }
  function emit(tag, target,   inc, b, i, more, n, file, id) {
    split("", inc)
    if (target != "") inc[target] = 1
    do {
      more = 0
      for (b = 1; b <= nb; b++) {
        if (unit[b] != "" && !(unit[b] in inc)) continue
        for (i = 1; i <= nu; i++)
          if ((b, order[i]) in calls && !(order[i] in inc)) { inc[order[i]] = 1; more = 1 }
      }
    } while (more)
    id = emitted++
    file = dir "/perlaw_" id ".bend"
    printf "" > file
    for (b = 0; b <= nb; b++)
      if (unit[b] == "" || unit[b] in inc) printf "%s", text[b] > file
    close(file)
    n = 0
    for (u in inc) if (u in fills) n++
    print id, n, tag > list
  }
' "$src"

# Each check writes <file>.out and <file>.rc; rc 124 is a timeout.
# shellcheck disable=SC2016 # $1 and $2 expand in the inner bash
cut -d' ' -f1 "$work/units" |
  xargs -P "$jobs" -I{} bash -c \
    'file=$2/perlaw_$3.bend; timeout "$1" bend "$file" --check-only >"$file.out" 2>&1 </dev/null; echo $? >"$file.rc"' \
    _ "$secs" "$dir" {}

# todo_count <out>: the TODO count, 0 on a clean check, empty on an error.
todo_count() {
  local n
  n=$(LC_ALL=C sed -nE 's/^Error: ([0-9]+) TODOs? found\..*/\1/p' "$1")
  if [ -n "$n" ]; then echo "$n"
  elif grep -q '^ALL PROOFS CHECK' "$1"; then echo 0
  fi
}
failure() {
  local lines
  lines=$(grep -E '^- (expected|observed) :' "$1" || true)
  [ -n "$lines" ] || lines=$(grep -E '^- |^Location:' "$1" || sed -n 1,8p "$1")
  printf '%s\n' "$lines" | sed 's/^/        /'
}

ok=0 open=0 fail=0 timeouts=0 status=0
{ read -r base_id base_fills _; cat; } <"$work/units" >"$work/laws"
base_file=$dir/perlaw_$base_id.bend
base=$(todo_count "$base_file.out")
if [ "$(cat "$base_file.rc")" = 124 ] || [ -z "$base" ]; then
  echo "perlaw: the file without its laws fails; nothing below is per law:"
  failure "$base_file.out"
  exit 1
fi
while read -r id fills law; do
  file=$dir/perlaw_$id.bend
  rc=$(cat "$file.rc")
  n=$(todo_count "$file.out")
  want=$((base - (fills - base_fills)))
  if [ "$rc" = 124 ]; then
    printf 'TIMEOUT %s (%ss)\n' "$law" "$secs"; timeouts=$((timeouts + 1))
  elif [ -z "$n" ]; then
    printf 'FAIL    %s\n' "$law"; failure "$file.out"; fail=$((fail + 1))
  elif [ "$n" -eq "$want" ]; then
    printf 'ok      %s\n' "$law"; ok=$((ok + 1))
  else
    printf 'OPEN    %s (%d TODOs, want %d)\n' "$law" "$n" "$want"; open=$((open + 1))
  fi
done <"$work/laws"
total=$((ok + open + fail + timeouts))
echo "perlaw: $ok ok, $open open, $fail failed, $timeouts timed out, of $total laws in $rel"
[ "$ok" -eq "$total" ] || status=1
exit "$status"
