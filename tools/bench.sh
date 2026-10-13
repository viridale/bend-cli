#!/usr/bin/env bash
# Purpose: compare a harness's native build at a base ref with the worktree's:
#   median wall time, peak RSS, and the --threads 1 over all-cores speedup.
# Expected output: a table of old and new by thread count, then whether the
#   stdouts match; exit 0 only when every run exits 0 and every stdout
#   agrees. Stderr isn't compared, since a harness may print its timings
#   there (bench/main.bend does); a failed run prints its stderr.
#   Refuses to run (exit 3) while the 1-minute load average is above -L.
# Run: tools/bench.sh [-r main] [-n 5] [-L load] harness.bend [app args...]
#
# The old build comes from a detached worktree in a unique tmp/bench.*
# directory, removed on exit; the new one from the worktree as it is. Each
# binary is warmed once per thread count, then runs alternate old and new, swapping
# which goes first each round. App args follow the runtime's "--", so they
# may not be the runtime's own options (README, Platform notes). The load
# limit defaults to a quarter of the CPUs; after building, the script waits
# up to 2 minutes for the load its builds raised to fall below it.
set -euo pipefail
BEND_TOOLS_PIN=2.0.37
# shellcheck source=.bend-version.sh
source "$(dirname "${BASH_SOURCE[0]}")/.bend-version.sh"
bend_tools_warn_version "$BEND_TOOLS_PIN" "$(basename "$0")"

usage() {
  echo 'usage: tools/bench.sh [-r ref] [-n runs] [-L max-load] <harness.bend> [app args...]' >&2
  exit 2
}
if [ "$(uname)" = Darwin ]; then ncpu=$(sysctl -n hw.ncpu); else ncpu=$(nproc); fi
ref=main runs=5 limit=$(awk -v n="$ncpu" 'BEGIN { print n / 4 }')
while getopts r:n:L: opt; do
  case $opt in
    r) ref=$OPTARG ;;
    n) runs=$OPTARG ;;
    L) limit=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ $# -ge 1 ] || usage
harness=$1
shift
args=("$@")

load() { uptime | sed -E 's/.*load averages?: *([0-9.]+).*/\1/'; }
above() { awk -v l="$(load)" -v m="$limit" 'BEGIN { exit !(l > m) }'; }
if above; then
  echo "bench: load $(load) is above $limit; refusing to run (-L to change)" >&2
  exit 3
fi

root=$(git rev-parse --show-toplevel)
cd "$root"
[ -r "$harness" ] || { echo "bench: cannot read $harness" >&2; exit 2; }
git rev-parse -q --verify "$ref^{commit}" >/dev/null ||
  { echo "bench: no commit $ref" >&2; exit 2; }
mkdir -p "$root/tmp"
work=$(mktemp -d "$root/tmp/bench.XXXXXX")
# shellcheck disable=SC2329 # Called by the EXIT trap.
cleanup() {
  git worktree remove --force "$work/old" >/dev/null 2>&1 || true
  rm -rf "$work"
}
trap cleanup EXIT
git worktree add --quiet --detach "$work/old" "$ref"
[ -r "$work/old/$harness" ] || { echo "bench: $harness is not in $ref" >&2; exit 2; }

echo "bench: building $harness at $ref ($(git rev-parse --short "$ref")) and in the worktree"
bend "$work/old/$harness" -o "$work/old.bin" </dev/null
bend "$harness" -o "$work/new.bin" </dev/null

waited=0
while above && [ "$waited" -lt 120 ]; do sleep 5; waited=$((waited + 5)); done
if above; then
  echo "bench: load $(load) is still above $limit after the builds; refusing to time" >&2
  exit 3
fi

# run <build> <threads> <tag>: one timed run; records stdout, stderr, and
# timer output separately. A failed run or missing RSS invalidates the bench.
if [ "$(uname)" = Darwin ]; then
  timer=(/usr/bin/time -l) rss_re='^ *([0-9]+) +maximum resident set size' rss_k=1
else
  timer=(/usr/bin/time -v) rss_re='^.*Maximum resident set size \(kbytes\): ([0-9]+)' rss_k=1024
fi
run() {
  local bin=$work/$1.bin flags=() t0 t1 rc rss
  [ "$2" = all ] || flags=(--threads "$2")
  t0=$EPOCHREALTIME
  "${timer[@]}" -o "$work/$3.time" "$bin" "${flags[@]}" -- "${args[@]}" >"$work/$3.out" 2>"$work/$3.err" </dev/null &&
    rc=0 || rc=$?
  t1=$EPOCHREALTIME
  if [ "$rc" -ne 0 ]; then
    echo "bench: $3 exited $rc" >&2
    cat "$work/$3.err" "$work/$3.time" >&2
    return 1
  fi
  rss=$(LC_ALL=C sed -nE "s/$rss_re/\\1/p" "$work/$3.time" | tail -n 1)
  if [[ ! $rss =~ ^[0-9]+$ ]]; then
    echo "bench: $3 has no peak RSS measurement" >&2
    cat "$work/$3.time" >&2
    return 1
  fi
  if [[ $3 != *.warm ]]; then
    awk -v a="$t0" -v b="$t1" -v r="$rss" -v k="$rss_k" \
      'BEGIN { printf "%.3f %d\n", (b - a) * 1000, r * k }' >>"$work/$1.$2.t"
  fi
}

for build in old new; do
  for threads in 1 all; do run "$build" "$threads" "$build.$threads.warm"; done
done
for ((i = 1; i <= runs; i++)); do
  if ((i % 2)); then order=(old new); else order=(new old); fi
  for threads in 1 all; do
    for build in "${order[@]}"; do run "$build" "$threads" "$build.$threads.$i"; done
  done
done

median() { cut -d' ' -f1 "$1" | sort -n | awk '{ v[NR] = $1 } END { print v[int((NR + 1) / 2)] }'; }
peak() { cut -d' ' -f2 "$1" | sort -n | tail -n 1; }
ratio() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.2fx", a / b }'; }
mb() { awk -v b="$1" 'BEGIN { printf "%.1f MB", b / 1048576 }'; }

echo "bench: $harness -- ${args[*]}  ($runs runs each, load limit $limit, $ncpu CPUs)"
printf '%-12s %14s %14s %10s %10s\n' '' 'threads=1' 'all cores' speedup 'peak RSS'
for build in old new; do
  t1=$(median "$work/$build.1.t") ta=$(median "$work/$build.all.t")
  p1=$(peak "$work/$build.1.t") pa=$(peak "$work/$build.all.t")
  label=$build; [ "$build" = old ] && label="old ($ref)"
  printf '%-12s %11s ms %11s ms %10s %10s\n' "$label" "$t1" "$ta" "$(ratio "$t1" "$ta")" \
    "$(mb "$((p1 > pa ? p1 : pa))")"
done
printf '%-12s %14s %14s\n' 'old/new' \
  "$(ratio "$(median "$work/old.1.t")" "$(median "$work/new.1.t")")" \
  "$(ratio "$(median "$work/old.all.t")" "$(median "$work/new.all.t")")"

status=0
for build in old new; do
  for f in "$work/$build".*.out; do
    if ! cmp -s "$f" "$work/$build.1.warm.out"; then
      echo "bench: $build stdout differs: $(basename "$f") vs $build.1.warm.out"
      status=1
    fi
  done
done
if ! cmp -s "$work/old.1.warm.out" "$work/new.1.warm.out"; then
  echo 'bench: old and new stdout differ:'
  diff "$work/old.1.warm.out" "$work/new.1.warm.out" | head -n 20 || true
  status=1
fi
[ "$status" -ne 0 ] || echo 'bench: stdout identical across builds and thread counts'
exit "$status"
