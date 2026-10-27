#!/usr/bin/env bash
# Purpose: check the argbench peers in bench/peers against the Bend app
#   (examples/argbench), then time every implementation on eight argvs:
#   one input, a typical build, build's help, the root's help, a misspelt
#   option, a bad number, and a mid and a large argv.
# Expected output: "peerbench: <impl> agrees on <n> argvs" per
#   implementation, then a table of median wall time per argv and peak RSS
#   on the typical and the large argv, with a last row for /usr/bin/true,
#   the cost of starting a process; -m prints the table as Markdown. It
#   exits 0 only when every implementation agrees with the native Bend app on
#   every checked argv and every timed run exits as expected. A peer whose
#   toolchain is missing is skipped with a note. Refuses to run (exit 3)
#   while the 1-minute load average is above -L; after building, waits up
#   to 2 minutes for the load its builds raised to fall below it.
# Run: tools/peerbench.sh [-n 10] [-s 10000] [-L load] [-c] [-m]
#
# Implementations: the Bend app built native (all cores, and --threads 1)
# and as JS under Bun; clap (cargo), cobra (go), argparse (python3) and
# commander (bun). The check compares stdout and exit code with the native
# Bend app on argvs that put options before inputs (argparse reads an
# option after an input as the end of INPUT...); an error argv must exit 2
# with nothing on stdout, and stderr is not compared, since each library
# words its errors and help in its own way. -c stops after the check. The
# large argv is build with -s pairs `-I dK` and -s inputs `fK`, and the mid
# one has a tenth as many; macOS limits argv to 1 MiB, about 25000 pairs.
# Each run is timed from the shell, so a time includes process start; runs
# rotate which implementation goes first.
set -euo pipefail
BEND_TOOLS_PIN=2.0.39
# shellcheck source=.bend-version.sh
source "$(dirname "${BASH_SOURCE[0]}")/.bend-version.sh"
bend_tools_warn_version "$BEND_TOOLS_PIN" "$(basename "$0")"

usage() {
  echo 'usage: tools/peerbench.sh [-n runs] [-s size] [-L max-load] [-c] [-m]' >&2
  exit 2
}
if [ "$(uname)" = Darwin ]; then ncpu=$(sysctl -n hw.ncpu); else ncpu=$(nproc); fi
runs=10 size=10000 limit=$(awk -v n="$ncpu" 'BEGIN { print n / 4 }') check_only=0
markdown=0
while getopts n:s:L:cm opt; do
  case $opt in
    n) runs=$OPTARG ;;
    s) size=$OPTARG ;;
    L) limit=$OPTARG ;;
    c) check_only=1 ;;
    m) markdown=1 ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ $# -eq 0 ] || usage
[[ $runs =~ ^[1-9][0-9]*$ && $size =~ ^[1-9][0-9]*$ ]] || usage

load() { uptime | sed -E 's/.*load averages?: *([0-9.]+).*/\1/'; }
above() { awk -v l="$(load)" -v m="$limit" 'BEGIN { exit !(l > m) }'; }

if [ "$check_only" = 0 ] && above; then
  echo "peerbench: load $(load) is above $limit; refusing to run (-L to change)" >&2
  exit 3
fi

root=$(git rev-parse --show-toplevel)
cd "$root"
out=$root/build/peerbench
mkdir -p "$out" "$root/tmp"
work=$(mktemp -d "$root/tmp/peerbench.XXXXXX")
trap 'rm -rf "$work"' EXIT
peers=$root/bench/peers

# ---- Build ----

impls=(bend bend-1t)
echo "peerbench: building examples/argbench and the peers"
bend examples/argbench/main.bend -o "$out/bend" </dev/null
if command -v bun >/dev/null; then
  bend examples/argbench/main.bend -o "$out/bend.js" </dev/null
  impls+=(bend-js)
else
  echo "peerbench: no bun; skipping bend-js and commander"
fi
if command -v cargo >/dev/null; then
  cargo build --release --locked --quiet --manifest-path "$peers/clap/Cargo.toml" \
    --target-dir "$out/clap"
  impls+=(clap)
else
  echo "peerbench: no cargo; skipping clap"
fi
if command -v go >/dev/null; then
  go build -C "$peers/cobra" -o "$out/cobra" .
  impls+=(cobra)
else
  echo "peerbench: no go; skipping cobra"
fi
if command -v python3 >/dev/null; then
  impls+=(argparse)
else
  echo "peerbench: no python3; skipping argparse"
fi
if command -v bun >/dev/null; then
  bun install --frozen-lockfile --silent --cwd "$peers/commander"
  impls+=(commander)
fi

# cmd <impl>: sets c to the command that runs impl, before its argv. Bun
# takes a -- right after the script path (README, Platform notes).
cmd() {
  case $1 in
    bend) c=("$out/bend") ;;
    bend-1t) c=("$out/bend" +RTS --threads 1 -RTS) ;;
    bend-js) c=(bun "$out/bend.js" --) ;;
    clap) c=("$out/clap/release/argbench") ;;
    cobra) c=("$out/cobra") ;;
    argparse) c=(python3 "$peers/argparse/argbench.py") ;;
    commander) c=(bun "$peers/commander/argbench.js") ;;
    true) c=(/usr/bin/true) ;;
  esac
}

# big_argv <n>: sets big to build with n pairs `-I dK`, then n inputs `fK`.
big_argv() {
  local i
  big=(build)
  for ((i = 0; i < $1; i++)); do big+=(-I "d$i"); done
  for ((i = 0; i < $1; i++)); do big+=("f$i"); done
}
mid_size=$((size / 10 > 0 ? size / 10 : 1))
big_argv "$mid_size"
mid=("${big[@]}")
big_argv "$size"
large=("${big[@]}")

# ---- Check ----

# Each line: what every implementation must do, then the argv: 0 is exit 0
# with the native Bend app's stdout, 2 is exit 2 with nothing on stdout,
# and h is exit 0 with a help page of the library's own on stdout.
checks=$(cat <<'EOF'
0 build -vv -o out.bin -I src -I lib -j 4 -f json a.c b.c
0 build -vvq -oout.bin --include=src -Ilib --jobs=4 -fjson a.c
0 build --verbose --verbose --quiet --output=o --format=csv x y z
0 build a.c
0 build -o a -I y -o b -I x -j 2 -j 3 in
0 build -- -x
0 build -j 4294967295 a
0 check -s -s a b
0 check a
2 build --ouput x a.c
2 build -j 4294967296 a
2 build -j x a
2 build -f xml a
2 build
2 buld a
2 check -v a
2
h --help
h -h
h build --help
h check --help
EOF
)

# agree <impl> <tag> <0|2|h> <argv...>: runs impl on argv and checks it as
# the checks above say.
agree() {
  local impl=$1 tag=$2 want=$3 rc
  shift 3
  if [ "$want" = h ]; then
    agree "$impl" "$tag" 0h "$@"
    [ -s "$work/$impl.$tag.out" ] && return 0
    echo "peerbench: $impl prints no help on: $*"
    return 1
  fi
  cmd "$impl"
  "${c[@]}" "$@" >"$work/$impl.$tag.out" 2>"$work/$impl.$tag.err" </dev/null &&
    rc=0 || rc=$?
  if [ "$rc" != "${want%h}" ]; then
    echo "peerbench: $impl exits $rc, not ${want%h}, on: ${*:1:12}"
    head -n 5 "$work/$impl.$tag.err"
    return 1
  fi
  if [ "$want" = 0 ] && ! cmp -s "$work/$impl.$tag.out" "$work/bend.$tag.out"; then
    echo "peerbench: $impl stdout differs from bend on: ${*:1:12}"
    diff "$work/bend.$tag.out" "$work/$impl.$tag.out" | cut -c 1-160 | head -n 4 || true
    return 1
  fi
  if [ "$want" = 2 ] && [ -s "$work/$impl.$tag.out" ]; then
    echo "peerbench: $impl prints to stdout on error argv: ${*:1:12}"
    return 1
  fi
}

status=0
for impl in "${impls[@]}"; do
  n=0 ok=1
  while read -r want line; do
    read -r -a argv <<<"$line"
    agree "$impl" "c$n" "$want" ${argv[@]+"${argv[@]}"} || ok=0
    n=$((n + 1))
  done <<<"$checks"
  agree "$impl" mid 0 "${mid[@]}" || ok=0
  agree "$impl" large 0 "${large[@]}" || ok=0
  if [ "$ok" = 1 ]; then
    echo "peerbench: $impl agrees on $((n + 2)) argvs"
  else
    status=1
  fi
done
[ "$status" = 0 ] || { echo "peerbench: implementations disagree" >&2; exit 1; }
[ "$check_only" = 0 ] || exit 0

# ---- Time ----

waited=0
while above && [ "$waited" -lt 120 ]; do sleep 5; waited=$((waited + 5)); done
if above; then
  echo "peerbench: load $(load) is still above $limit after the builds; refusing to time" >&2
  exit 3
fi

if [ "$(uname)" = Darwin ]; then
  timer=(/usr/bin/time -l) rss_re='^ *([0-9]+) +maximum resident set size' rss_k=1
else
  timer=(/usr/bin/time -v) rss_re='^.*Maximum resident set size \(kbytes\): ([0-9]+)' rss_k=1024
fi
cases=(one typical help roothelp typo badnum mid large)
# argv_of <case>: sets argv to the case's argv and want to its exit code.
argv_of() {
  case $1 in
    one) argv=(build a.c) want=0 ;;
    typical) argv=(build -vv -o out.bin -I src -I lib -j 4 -f json a.c b.c) want=0 ;;
    help) argv=(build --help) want=0 ;;
    roothelp) argv=(--help) want=0 ;;
    typo) argv=(build --ouput x a.c) want=2 ;;
    badnum) argv=(build -j x a) want=2 ;;
    mid) argv=("${mid[@]}") want=0 ;;
    large) argv=("${large[@]}") want=0 ;;
  esac
}

# run <impl> <case> <record>: one timed run; appends "ms rss" to
# impl.case.t when record is 1.
run() {
  local t0 t1 rc rss
  cmd "$1"
  argv_of "$2"
  [ "$1" != true ] || want=0
  t0=$EPOCHREALTIME
  "${timer[@]}" -o "$work/time" "${c[@]}" "${argv[@]}" >"$work/run.out" 2>"$work/run.err" \
    </dev/null && rc=0 || rc=$?
  t1=$EPOCHREALTIME
  if [ "$rc" != "$want" ]; then
    echo "peerbench: $1 $2 exited $rc, not $want" >&2
    cat "$work/run.err" >&2
    return 1
  fi
  rss=$(LC_ALL=C sed -nE "s/$rss_re/\\1/p" "$work/time" | tail -n 1)
  [[ $rss =~ ^[0-9]+$ ]] || { echo "peerbench: $1 $2 has no peak RSS" >&2; return 1; }
  [ "$3" = 1 ] || return 0
  awk -v a="$t0" -v b="$t1" -v r="$rss" -v k="$rss_k" \
    'BEGIN { printf "%.3f %d\n", (b - a) * 1000, r * k }' >>"$work/$1.$2.t"
}

# true runs only in the timing: it prints nothing, so it can't agree.
timed=("${impls[@]}" true)
for impl in "${timed[@]}"; do
  for case in "${cases[@]}"; do run "$impl" "$case" 0; done
done
count=${#timed[@]}
for ((i = 0; i < runs; i++)); do
  for case in "${cases[@]}"; do
    for ((j = 0; j < count; j++)); do
      run "${timed[(i + j) % count]}" "$case" 1
    done
  done
done

median() { cut -d' ' -f1 "$1" | sort -n | awk '{ v[NR] = $1 } END { print v[int((NR + 1) / 2)] }'; }
# peak <file>: the largest RSS among a case's runs, in MB.
peak() { cut -d' ' -f2 "$1" | sort -n | tail -n 1 | awk '{ printf "%.1f", $1 / 1048576 }'; }
# name_of <impl>: sets name to the impl's row label in Markdown.
name_of() {
  case $1 in
    bend) name='bend-cli, native' ;;
    bend-1t) name='bend-cli, native, 1 thread' ;;
    bend-js) name='bend-cli, JS on Bun' ;;
    clap) name='clap (Rust)' ;;
    cobra) name='cobra (Go)' ;;
    argparse) name='argparse (Python)' ;;
    commander) name='commander (JS on Bun)' ;;
    true) name="\`/usr/bin/true\`" ;;
  esac
}

if [ "$markdown" = 1 ]; then
  echo "| | one input | typical | \`build --help\` | \`--help\` | typo | bad number |" \
    "mid | large | RSS, typical | RSS, large |"
  echo '|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|'
  for impl in "${timed[@]}"; do
    name_of "$impl"
    printf '| %s |' "$name"
    for case in "${cases[@]}"; do printf ' %.1f |' "$(median "$work/$impl.$case.t")"; done
    printf ' %s MB | %s MB |\n' "$(peak "$work/$impl.typical.t")" "$(peak "$work/$impl.large.t")"
  done
  exit 0
fi
echo "peerbench: median of $runs runs (ms); mid and large are build with $mid_size and" \
  "$size \`-I dK\` pairs and as many inputs; peak RSS (MB) on typical and large;" \
  "load limit $limit, $ncpu CPUs"
printf '%-10s' ''
printf ' %9s' "${cases[@]}" 'RSS typ' 'RSS large'
echo
for impl in "${timed[@]}"; do
  printf '%-10s' "$impl"
  for case in "${cases[@]}"; do printf ' %9s' "$(median "$work/$impl.$case.t")"; done
  printf ' %9s %9s\n' "$(peak "$work/$impl.typical.t")" "$(peak "$work/$impl.large.t")"
done
