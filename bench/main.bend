# Purpose: the CLI benchmark (§14.4, G6). It builds a spec of 60 commands
# and 300 args and a corpus of 1,024 argvs of up to 20 tokens, runs Cli.eval
# on each argv and renders the long help page of every command. Both phases
# split their work in halves across cores, and each half builds its own spec.
# Expected output: on stdout, the spec's problem count and each phase's
# tallies and checksum, the same at every thread count; on stderr, each
# phase's time. It exits 1 if an argv hits a bug, as every argv does when the
# spec has a problem.
# Run: bend bench/main.bend -o build/bench, then build/bench --threads 1 and
#   build/bench

import Base
import ../cli.bend as Cli

# ---- Spec ----

def groups() -> List<&2, String>:
  ["build", "deploy", "query", "store", "user"]

def leaves() -> List<&2, String>:
  ["add", "list", "show", "edit", "remove", "sync", "check", "clean", "fetch",
    "merge"]

def flats() -> List<&2, String>:
  ["init", "status", "login", "logout"]

def leaf_args() -> List<&2, Cli.Item>:
  [
    Cli.arg("-a, --all", "Include hidden entries", []),
    Cli.arg("-o, --output <FILE>", "Write the result to FILE",
      [Cli.as_file()]),
    Cli.arg("-n, --count <N>", "Show at most N entries",
      [Cli.as_u32(), Cli.default("10")]),
    Cli.arg("--format <FMT>", "Output format",
      [Cli.one_of(["text", "json", "yaml"]), Cli.default("text")]),
    Cli.arg("<INPUT>...", "Files to read", [Cli.as_file()]),
  ]

# A leaf command; path is its words after the root, for its example.
def leaf(+name: String, path: String) -> Cli.Item:
  Cli.sub(name, String.concat(["Run ", name, " on each INPUT\n\n",
      "Reads each INPUT in order and prints one line per entry. With ",
      "--format json, each line is one JSON object."]),
    List.append(&2, Cli.Item, leaf_args(), [
      Cli.example(String.concat(["bench ", path, " -a in.txt"]),
        "Include the hidden entries of in.txt"),
    ]))

def leaf_list(names: List<&2, String>, +group: String) -> List<&2, Cli.Item>:
  match names:
    case Nil{}: []
    case +name <> rest:
      leaf(name, String.concat([group, " ", name])) <> leaf_list(rest, group)

def group_args() -> List<&2, Cli.Item>:
  [
    Cli.arg("--[no-]cache", "Reuse earlier results", []),
    Cli.arg("-j, --jobs <N>", "Run N jobs at once",
      [Cli.as_u32(), Cli.default("4")]),
    Cli.arg("--profile <NAME>", "Settings profile",
      [Cli.one_of(["dev", "release", "test"]), Cli.default("dev")]),
    Cli.arg("--tag <TAG>...", "Only items with TAG", []),
    Cli.arg("-k, --keep-going", "Continue after a failure", []),
  ]

def group_list(names: List<&2, String>) -> List<&2, Cli.Item>:
  match names:
    case Nil{}: []
    case +name <> rest:
      Cli.sub(name, String.append("Commands for ", name),
        List.append(&2, Cli.Item, group_args(), leaf_list(leaves(), name)))
        <> group_list(rest)

def flat_list(names: List<&2, String>) -> List<&2, Cli.Item>:
  match names:
    case Nil{}: []
    case +name <> rest: leaf(name, name) <> flat_list(rest)

# 1 root, 5 groups, 50 leaves under them and 4 under the root: 60 commands,
# with 5 args each.
def cli() -> Cli.Cmd:
  Cli.cmd("bench", "A large synthetic CLI\n\nFor timing Cli.eval and help.",
    List.concat(&2, Cli.Item, [
      [
        Cli.version("1.0.0"),
        Cli.color(),
        Cli.arg("-v, --verbose...", "More output; repeat for more",
          [Cli.global()]),
        Cli.arg("-q, --quiet", "Less output", [Cli.global()]),
        Cli.arg("-C <DIR>", "Run as if started in DIR",
          [Cli.global(), Cli.as_dir()]),
        Cli.arg("--config <FILE>", "Read settings from FILE",
          [Cli.global(), Cli.as_file(), Cli.env("BENCH_CONFIG")]),
      ],
      group_list(groups()),
      flat_list(flats()),
    ]))

# ---- Decoder ----

type Job is Data:
  Job{path: List<&2, String>, all: Bool, output: Maybe<&2, String>,
    count: U32, format: String, inputs: List<&2, String>}

def job(+m: Cli.Matches) -> Cli.Dec(Job):
  do Cli.Dec<Job>:
    all : Bool <- Cli.flag(m, "all")
    output : Maybe<&2, String> <- Cli.str_opt(m, "output")
    count : U32 <- Cli.u32(m, "count")
    format : String <- Cli.str(m, "format")
    inputs : List<&2, String> <- Cli.strs(m, "input")
    return Job{Cli.path(m), all, output, count, format, inputs}

def leaf_keys(names: List<&2, String>, +group: String) -> List<&2, String>:
  match names:
    case Nil{}: []
    case name <> rest:
      String.concat([group, " ", name]) <> leaf_keys(rest, group)

def group_keys(names: List<&2, String>) -> List<&2, String>:
  match names:
    case Nil{}: []
    case name <> rest:
      List.append(&2, String, leaf_keys(leaves(), name), group_keys(rest))

# Every leaf's path, the route table's keys.
def keys() -> List<&2, String>:
  List.append(&2, String, group_keys(groups()), flats())

def routes(keys: List<&2, String>) ->
    List<(String & (@+m: Cli.Matches -> Cli.Dec(Job)))>:
  match keys:
    case Nil{}: Nil{}
    case key <> rest: (key, job) <> routes(rest)

type Run is Data:
  Run{verbose: Nat, quiet: Bool, dir: Maybe<&2, String>,
    config: Maybe<&2, String>, job: Job}

def decode(+m: Cli.Matches) -> Cli.Dec(Run):
  do Cli.Dec<Run>:
    verbose : Nat <- Cli.count(m, "verbose")
    quiet : Bool <- Cli.flag(m, "quiet")
    dir : Maybe<&2, String> <- Cli.str_opt(m, "C")
    config : Maybe<&2, String> <- Cli.str_opt(m, "config")
    job : Job <- Cli.route(Job, m, routes(keys()))
    return Run{verbose, quiet, dir, config, job}

# ---- Corpus ----

# Murmur3's 32-bit finalizer, in three steps.
def mix3(+h: U32) -> U32:
  (h .^. (h >> 16n) : U32)

def mix2(+h: U32) -> U32:
  mix3(((h .^. (h >> 13n)) * 3266489909 : U32))

def mix(+h: U32) -> U32:
  mix2(((h .^. (h >> 16n)) * 2246822507 : U32))

# Decision k of argv i.
def roll(i: U32, k: U32) -> U32:
  mix((i * 2654435769 + k * 40503 : U32))

def or_empty(found: Maybe<&2, String>) -> String:
  match found:
    case None{}: ""
    case Some{s}: s

# xs's element at r modulo n, xs's length.
def pick(xs: List<&2, String>, r: U32, n: U32) -> String:
  or_empty(List.get(&2, String, xs, U32.to_nat((r % n : U32))))

def or_none(found: Maybe<&2, List<&2, String>>) -> List<&2, String>:
  match found:
    case None{}: []
    case Some{xs}: xs

# options's element at r modulo 4, its length.
def one(options: List<&2, List<&2, String>>, r: U32) -> List<&2, String>:
  or_none(List.get(&2, List<&2, String>, options, U32.to_nat((r % 4 : U32))))

def global_opts(r: U32) -> List<&2, String>:
  one([[], ["-v"], ["-vv", "-C", "/srv/app"], ["--config=bench.toml", "-q"]],
    r)

def group_opts(r: U32) -> List<&2, String>:
  one([[], ["--no-cache"], ["-j", "8"],
    ["--profile=release", "--tag", "nightly", "-k"]], r)

def output_opts(r: U32) -> List<&2, String>:
  one([[], ["-a"], ["-o", "out.txt"], ["--output=out.json", "-a"]], r)

def count_opts(r: U32) -> List<&2, String>:
  one([[], ["-n", "25"], ["--format", "json"], ["-n50", "--format=yaml"]], r)

def inputs(r: U32) -> List<&2, String>:
  one([["a.txt"], ["a.txt", "b.txt"], ["a.txt", "b.txt", "c.txt"],
    ["a.txt", "b.txt", "c.txt", "d.txt"]], r)

# An argv's kind is a roll modulo 32: 0 misspells the command, 1 to 3 add a
# misspelled option, a bad number or a bad choice, 4 drops the inputs, 5 and
# 6 ask for long and short help, 7 stops after the group, and the rest are
# valid.
def bad_opts(+kind: U32) -> List<&2, String>:
  Bool.pick(List<&2, String>, (kind < 4 : U32),
    one([[], ["--formt", "json"], ["-n", "many"], ["--format", "xml"]], kind),
    [])

def help_opts(+kind: U32) -> List<&2, String>:
  Bool.pick(List<&2, String>, U32.is_eq(kind, 5), ["--help"],
    Bool.pick(List<&2, String>, U32.is_eq(kind, 6), ["-h"], []))

# name less its second character.
def typo(+name: String) -> String:
  String.append(String.take(name, 1n), String.drop(name, 2n))

def word(kind: U32, +name: String) -> String:
  Bool.pick(String, U32.is_eq(kind, 0), typo(name), name)

# A leaf's tokens after its name: options, the kind's changes and inputs,
# which come between the options or after them.
def leaf_tail(+i: U32, +kind: U32) -> List<&2, String>:
  +files = Bool.pick(List<&2, String>, U32.is_eq(kind, 4), [],
    inputs(roll(i, 7)))
  +counts = count_opts(roll(i, 6))
  List.concat(&2, String, [output_opts(roll(i, 5)), bad_opts(kind),
    Bool.pick(List<&2, String>, U32.is_eq((roll(i, 8) % 2 : U32), 0),
      List.append(&2, String, files, counts),
      List.append(&2, String, counts, files)),
    help_opts(kind)])

def leaf_part(stop: Bool, +i: U32, +kind: U32) -> List<&2, String>:
  match stop:
    case True{}: []
    case False{}:
      word(kind, pick(leaves(), roll(i, 4), 10)) <> leaf_tail(i, kind)

def grouped(+i: U32, +kind: U32) -> List<&2, String>:
  List.concat(&2, String, [[pick(groups(), roll(i, 2), 5)],
    group_opts(roll(i, 3)), leaf_part(U32.is_eq(kind, 7), i, kind)])

def flat(+i: U32, +kind: U32) -> List<&2, String>:
  word(kind, pick(flats(), roll(i, 4), 4)) <> leaf_tail(i, kind)

def shape(top: Bool, i: U32, kind: U32) -> List<&2, String>:
  match top:
    case True{}: flat(i, kind)
    case False{}: grouped(i, kind)

# Argv i: up to 3 global tokens; a group and up to 4 of its options, unless
# the leaf is top-level; then the leaf's name and up to 11 more: at most 20.
def argv(+i: U32) -> List<&2, String>:
  List.append(&2, String, global_opts(roll(i, 1)),
    shape(U32.is_eq((roll(i, 9) % 6 : U32), 5), i,
      (roll(i, 0) % 32 : U32)))

# Argvs i to i + n - 1.
def argvs(n: Nat, +i: U32) -> List<&2, List<&2, String>>:
  match n:
    case 0n: []
    case 1n+p: argv(i) <> argvs(p, (i + 1 : U32))

type Tree is Data:
  Leaf{items: List<&2, List<&2, String>>}
  Node{left: Tree, right: Tree}

# items, n long, halved d times.
def split(+d: Nat, +items: List<&2, List<&2, String>>, +n: Nat) -> Tree:
  match d:
    case 0n: Leaf{items}
    case 1n+p:
      +half = Nat.div(n, 2n)
      Node{split(p, List.take(&2, List<&2, String>, items, half), half),
        split(p, List.drop(&2, List<&2, String>, items, half),
          Nat.sub(n, half))}

# ---- Eval ----

# FNV-1a over s's code points, from h.
def fnv(s: String, h: U32) -> U32:
  match s:
    case SNil{}: h
    case SCon{c, t}: fnv(t, ((h .^. Char.to_u32(c)) * 16777619 : U32))

def bit(b: Bool) -> String:
  match b:
    case True{}: "1"
    case False{}: "0"

def opt(m: Maybe<&2, String>) -> String:
  match m:
    case None{}: "-"
    case Some{s}: s

def job_text(j: Job) -> String:
  match j:
    case Job{path, all, output, count, format, inputs}:
      String.concat([String.join(path, " "), " all=", bit(all), " output=",
        opt(output), " count=", U32.show(count), " format=", format,
        " inputs=", String.join(inputs, ",")])

def run_text(r: Run) -> String:
  match r:
    case Run{verbose, quiet, dir, config, job}:
      String.concat(["verbose=", Nat.show(verbose), " quiet=", bit(quiet),
        " dir=", opt(dir), " config=", opt(config), " ", job_text(job)])

def term_text(t: Cli.Term) -> String:
  match t:
    case Cli.Term{out_color, err_color, width}:
      String.concat([bit(out_color), bit(err_color), Nat.show(width)])

# Decoded runs, exits with 0 (help or version), with 2 (usage errors) and
# with any other code (bugs), and the sum of each one's hash.
type Tally is Data:
  Tally{ran: U32, shown: U32, usage: U32, bug: U32, sum: U32}

def one_if(b: Bool) -> U32:
  match b:
    case True{}: 1
    case False{}: 0

def went(t: Tally, h: U32) -> Tally:
  match t:
    case Tally{ran, shown, usage, bug, sum}:
      Tally{(ran + 1 : U32), shown, usage, bug, (sum + h : U32)}

def exited(t: Tally, +code: U32, h: U32) -> Tally:
  match t:
    case Tally{ran, shown, usage, bug, sum}:
      Tally{ran, (shown + one_if(U32.is_eq(code, 0)) : U32),
        (usage + one_if(U32.is_eq(code, 2)) : U32),
        (bug + one_if((code > 2 : U32)) : U32), (sum + h : U32)}

def tallied(s: Cli.Step<Run>, t: Tally) -> Tally:
  match s:
    case Cli.Go{r, term}:
      went(t, fnv(term_text(term), fnv(run_text(r), 2166136261)))
    case Cli.Exit{+code, out, err}:
      exited(t, code, fnv(err, fnv(out, code)))

# t with each argv in argvs evaluated against c and h.
def evaluated(argvs: List<&2, List<&2, String>>, +c: Cli.Cmd, +h: Cli.Host,
    t: Tally) -> Tally:
  match argvs:
    case Nil{}: t
    case a <> rest:
      evaluated(rest, c, h, tallied(Cli.eval(~Run, ~decode, c, h, a), t))

def tallies(a: Tally, b: Tally) -> Tally:
  match a b:
    case Tally{r1, s1, u1, b1, h1} Tally{r2, s2, u2, b2, h2}:
      Tally{(r1 + r2 : U32), (s1 + s2 : U32), (u1 + u2 : U32),
        (b1 + b2 : U32), (h1 + h2 : U32)}

def evals(t: Tree) -> Tally:
  match t:
    case Leaf{argvs}:
      evaluated(argvs, cli(), Cli.host(80n), Tally{0, 0, 0, 0, 0})
    case Node{l, r}:
      a b = evals(l) evals(r)
      tallies(a, b)

# ---- Help ----

def leaf_paths(names: List<&2, String>, +group: String) ->
    List<&2, List<&2, String>>:
  match names:
    case Nil{}: []
    case name <> rest: [group, name] <> leaf_paths(rest, group)

def group_paths(names: List<&2, String>) -> List<&2, List<&2, String>>:
  match names:
    case Nil{}: []
    case +name <> rest:
      [name] <> List.append(&2, List<&2, String>, leaf_paths(leaves(), name),
        group_paths(rest))

def flat_paths(names: List<&2, String>) -> List<&2, List<&2, String>>:
  match names:
    case Nil{}: []
    case name <> rest: [name] <> flat_paths(rest)

# Every command's path: the root's, then each group's and its leaves', then
# the top-level leaves'.
def paths() -> List<&2, List<&2, String>>:
  [] <> List.append(&2, List<&2, String>, group_paths(groups()),
    flat_paths(flats()))

# Pages rendered, their code points, and the sum of each one's hash.
type Pages is Data:
  Pages{count: U32, chars: Nat, sum: U32}

def paged(p: Pages, +text: String) -> Pages:
  match p:
    case Pages{count, chars, sum}:
      Pages{(count + 1 : U32), Nat.add(chars, String.length(text)),
        (sum + fnv(text, 2166136261) : U32)}

# p with the long help page of each path in paths, for c and h.
def rendered(paths: List<&2, List<&2, String>>, +c: Cli.Cmd, +h: Cli.Host,
    p: Pages) -> Pages:
  match paths:
    case Nil{}: p
    case path <> rest:
      rendered(rest, c, h, paged(p, Cli.help(c, path, True{}, h)))

def pages_sum(a: Pages, b: Pages) -> Pages:
  match a b:
    case Pages{n1, c1, h1} Pages{n2, c2, h2}:
      Pages{(n1 + n2 : U32), Nat.add(c1, c2), (h1 + h2 : U32)}

def pages(t: Tree) -> Pages:
  match t:
    case Leaf{paths}:
      rendered(paths, cli(), Cli.host(80n), Pages{0, 0n, 0})
    case Node{l, r}:
      a b = pages(l) pages(r)
      pages_sum(a, b)

# ---- Main ----

def tally_text(t: Tally) -> String:
  match t:
    case Tally{ran, shown, usage, bug, sum}:
      String.concat(["eval: ", U32.show(ran), " decoded, ", U32.show(shown),
        " help, ", U32.show(usage), " usage errors, ", U32.show(bug),
        " bugs; checksum ", U32.show(sum)])

def pages_text(p: Pages) -> String:
  match p:
    case Pages{count, chars, sum}:
      String.concat(["help: ", U32.show(count), " pages, ", Nat.show(chars),
        " chars; checksum ", U32.show(sum)])

def bugs(t: Tally) -> U32:
  match t:
    case Tally{ran, shown, usage, bug, sum}: bug

# "<label>: <ms> ms", then the mean in microseconds over n of unit.
def timed(label: String, +ms: Nat, n: Nat, unit: String) -> String:
  String.concat([label, ": ", Nat.show(ms), " ms, ",
    Nat.show(Nat.div(Nat.mul(ms, 1000n), n)), " us per ", unit])

def verdict(clean: Bool) -> IO(Unit):
  match clean:
    case True{}: IO.pure(Unit, Unit{})
    case False{}: IO.die(Unit, 1, "bench: an argv hit a bug")

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    corpus : Tree = split(4n, argvs(1024n, 0), 1024n)
    +t1 : Nat <- IO.now()
    +tally : Tally = evals(corpus)
    +t2 : Nat <- IO.now()
    help : Pages = pages(split(3n, paths(), 60n))
    t3 : Nat <- IO.now()
    IO.print(String.concat(["spec: ",
      Nat.show(List.length(&2, Cli.Problem, Cli.problems(cli()))),
      " problems"]))
    IO.print(tally_text(tally))
    IO.print(pages_text(help))
    IO.print_err(String.concat(["corpus: ", Nat.show(Nat.sub(t1, t0)), " ms"]))
    IO.print_err(timed("eval", Nat.sub(t2, t1), 1024n, "argv"))
    IO.print_err(timed("help", Nat.sub(t3, t2), 60n, "page"))
    verdict(U32.is_eq(bugs(tally), 0))
