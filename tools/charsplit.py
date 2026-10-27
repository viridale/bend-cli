#!/usr/bin/env python3
"""Purpose: print the arms of `match c:` for a char view in PROOF.bend.
Expected output: one `case` per leaf of a split of c's 32 bits, LSB first,
  just far enough to tell each code from every other char. The arm of the
  i-th code (from 0) proves `{Chr{code} == c : Char}` as Inr^i(Inl{{==}}); every
  other leaf gives OTHER as Inr^n(OTHER), for n codes.
Run: python3 tools/charsplit.py OTHER CODE...

The checker reduces a match on a char only where the char's bits are
constructors. A `case _:` arm leaves a bit it has ruled out one value of as
a variable, so the view spells out every leaf instead.
"""
import argparse
from pathlib import Path
import subprocess
import sys


BEND_TOOLS_PIN = '2.0.39'


def warn_bend_version():
    try:
        subprocess.run(
            ['bash', str(Path(__file__).resolve().with_name('.bend-version.sh')),
             BEND_TOOLS_PIN, Path(__file__).name],
            check=False,
        )
    except OSError as exc:
        print(f'charsplit.py: version check unavailable: {exc}', file=sys.stderr)


def bit(c, i):
    return 'True{}' if (c >> i) & 1 else 'False{}'


def pattern(bits, rest):
    out = rest
    for b in reversed(bits):
        out = 'WCon{' + b + ', ' + out + '}'
    return 'Chr{U32{' + out + '}}'


def leaves(codes, bits=()):
    """Yields (pattern, code or None) for each leaf of the split."""
    i = len(bits)
    if i == 32:
        yield pattern(bits, 'WNil{}'), codes[0]
        return
    for b in ('True{}', 'False{}'):
        sub = [c for c in codes if bit(c, i) == b]
        if sub:
            yield from leaves(sub, bits + (b,))
        else:
            yield pattern(bits + (b,), '_'), None


def main():
    warn_bend_version()
    parser = argparse.ArgumentParser(description='Generate exhaustive Char proof match arms.')
    parser.add_argument('other', metavar='OTHER')
    parser.add_argument('codes', metavar='CODE', type=int, nargs='+')
    args = parser.parse_args()
    other, codes = args.other, args.codes
    if any(c < 0 or c >= 1 << 32 for c in codes):
        parser.error('CODE must be in the range 0..4294967295')
    if len(set(codes)) != len(codes):
        parser.error('CODE values must be unique')
    n = len(codes)
    for p, c in leaves(codes):
        if c is None:
            body = 'Inr{' * n + other + '}' * n
        else:
            i = codes.index(c)
            body = 'Inr{' * i + 'Inl{{==}}' + '}' * i
        print(f'    case {p}:\n      {body}')


if __name__ == '__main__':
    main()
