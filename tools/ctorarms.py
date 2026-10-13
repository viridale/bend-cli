#!/usr/bin/env python3
"""Purpose: print the arms of a proof's match on a value of a Bend type, one
  `case` per constructor, for PROOF.bend.
Expected output: for each constructor of TYPE in FILE, in declaration order
  and less each --skip, `    case ROW:` with $P replaced by the constructor's
  pattern (fields bound to x0, x1, ...), then BODY with $H replaced by the
  same pattern. A one-line BODY follows the case on its line; a BODY with
  \\n (backslash n) breaks gets one line per part, indented under the case.
Run: python3 tools/ctorarms.py [--prefix ALIAS.] [--skip CTOR]... FILE TYPE ROW BODY

A `case _:` arm leaves its head refined away from the constructors named
above it, and the checker does not reduce such a head, so a proof that walks
a list of TYPE names every constructor. The arms written by hand, such as the
one that does the work, go in the match as well and are named by --skip.
"""
import argparse
from pathlib import Path
import re
import subprocess
import sys


BEND_TOOLS_PIN = '2.0.36'


def warn_bend_version():
    try:
        subprocess.run(
            ['bash', str(Path(__file__).resolve().with_name('.bend-version.sh')),
             BEND_TOOLS_PIN, Path(__file__).name],
            check=False,
        )
    except OSError as exc:
        print(f'ctorarms.py: version check unavailable: {exc}', file=sys.stderr)


def top_level_fields(text):
    """Counts the comma-separated fields of a constructor's braces."""
    depth, fields, seen = 0, 0, False
    for ch in text:
        if ch in '<({[':
            depth += 1
        elif ch in '>)}]':
            depth -= 1
        elif ch == ',' and depth == 0:
            fields += 1
        if not ch.isspace():
            seen = True
    return fields + 1 if seen else 0


def constructors(source, name):
    """Yields (constructor, arity) of `type NAME ...:` in declaration order."""
    lines = source.split('\n')
    head = re.compile(r'^type\s+' + re.escape(name) + r'\b.*:\s*$')
    start = next((i for i, l in enumerate(lines) if head.match(l)), None)
    if start is None:
        return None
    body = []
    for line in lines[start + 1:]:
        if line.strip() and not line[0].isspace():
            break
        body.append(line.split('#', 1)[0])
    text, out = '\n'.join(body), []
    i = 0
    while i < len(text):
        m = re.compile(r'\s*(\w+)\s*\{').match(text, i)
        if not m:
            if text[i:].strip():
                raise ValueError(f'cannot read a constructor at: {text[i:].strip()[:40]}')
            break
        depth, j = 1, m.end()
        while depth:
            if j == len(text):
                raise ValueError(f'unclosed fields of {m.group(1)}')
            depth += {'{': 1, '}': -1}.get(text[j], 0)
            j += 1
        out.append((m.group(1), top_level_fields(text[m.end():j - 1])))
        i = j
    return out


def main():
    warn_bend_version()
    parser = argparse.ArgumentParser(
        description='Generate one proof match arm per constructor of a Bend type.')
    parser.add_argument('--prefix', default='',
                        help='qualifier for constructor names, such as Cli.')
    parser.add_argument('--skip', action='append', default=[], metavar='CTOR',
                        help='a constructor whose arm is written by hand')
    parser.add_argument('file', metavar='FILE')
    parser.add_argument('type', metavar='TYPE')
    parser.add_argument('row', metavar='ROW')
    parser.add_argument('body', metavar='BODY')
    args = parser.parse_args()
    if '$P' not in args.row:
        parser.error('ROW must contain $P')
    try:
        source = Path(args.file).read_text()
    except OSError as exc:
        parser.error(f'cannot read FILE: {exc}')
    try:
        ctors = constructors(source, args.type)
    except ValueError as exc:
        parser.error(f'type {args.type}: {exc}')
    if not ctors:
        parser.error(f'no type {args.type} with constructors in {args.file}')
    names = [c for c, _ in ctors]
    for s in args.skip:
        if s not in names:
            parser.error(f'--skip {s} is not a constructor of {args.type}')
    lines = args.body.split('\\n')
    for ctor, arity in ctors:
        if ctor in args.skip:
            continue
        pat = '%s%s{%s}' % (args.prefix, ctor,
                            ', '.join('x%d' % k for k in range(arity)))
        case = '    case %s:' % args.row.replace('$P', pat)
        body = [l.replace('$H', pat) for l in lines]
        if len(body) == 1:
            print(case + ' ' + body[0])
        else:
            print(case)
            for l in body:
                print('      ' + l)


if __name__ == '__main__':
    main()
