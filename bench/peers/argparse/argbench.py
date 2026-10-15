"""The argbench command (examples/argbench/app.bend) in argparse: it prints
the line the Bend app prints for each argv tools/peerbench.sh checks.

argparse reads an option between inputs (`a.c -v b.c`) as the end of
INPUT..., so the checked argvs put options first.
"""

import argparse


def u32(s):
    if not (s.isascii() and s.isdigit()) or int(s) > 4294967295:
        raise argparse.ArgumentTypeError(
            "expected a whole number from 0 to 4294967295")
    return int(s)


def parser():
    # allow_abbrev=False: bend-cli matches option names exactly.
    p = argparse.ArgumentParser(prog="argbench", allow_abbrev=False,
                                description="Print the line an argv decodes to")
    subs = p.add_subparsers(dest="command", required=True, metavar="<COMMAND>")
    b = subs.add_parser("build", help="Build inputs", description="Build inputs",
                        allow_abbrev=False)
    b.add_argument("-v", "--verbose", action="count", default=0,
                   help="More output; repeat for more")
    b.add_argument("-q", "--quiet", action="store_true", help="Less output")
    b.add_argument("-o", "--output", metavar="FILE", default="out",
                   help="Write the result to FILE")
    b.add_argument("-I", "--include", metavar="DIR", action="append",
                   default=[], help="Search DIR for inputs")
    b.add_argument("-j", "--jobs", metavar="N", type=u32, default=1,
                   help="Run N jobs at once")
    b.add_argument("-f", "--format", metavar="FMT",
                   choices=["text", "json", "csv"], default="text",
                   help="Output format")
    b.add_argument("inputs", metavar="INPUT", nargs="+", help="Files to build")
    c = subs.add_parser("check", help="Check inputs", description="Check inputs",
                        allow_abbrev=False)
    c.add_argument("-s", "--strict", action="store_true",
                   help="Treat warnings as errors")
    c.add_argument("inputs", metavar="INPUT", nargs="+", help="Files to check")
    return p


def word(b):
    return "true" if b else "false"


def main():
    a = parser().parse_args()
    if a.command == "build":
        print(f"build verbose={a.verbose} quiet={word(a.quiet)} "
              f"output={a.output} include={','.join(a.include)} "
              f"jobs={a.jobs} format={a.format} inputs={','.join(a.inputs)}")
    else:
        print(f"check strict={word(a.strict)} inputs={','.join(a.inputs)}")


main()
