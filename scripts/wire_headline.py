#!/usr/bin/env python3
"""Replace the `sorry` of a headline theorem by a reference to its generated certificate.

usage: scripts/wire_headline.py <s> <n>
"""
import re
import sys

NAMES = {0: 'zero', 1: 'one', 2: 'two', 3: 'three', 4: 'four', 5: 'five', 6: 'six'}


def main():
    s, n = int(sys.argv[1]), int(sys.argv[2])
    k = 1 + s + 2 * n
    path = f'Solution/Atoms{k}/Symm{s}Nsymm{n}.lean'
    src = open(path).read()
    thm = f'encard_ofSymmNsymm_{NAMES[s]}_{NAMES[n]}'
    assert thm in src, (thm, path)
    imp = f'import Solution.Atoms{k}.S{s}N{n}.Group'
    if imp not in src:
        anchor = 'public import Cslib.Foundations.RelationAlgebra.IntegralAtomStructure'
        src = src.replace(anchor, anchor + '\n' + imp)
    src = re.sub(r'(theorem ' + thm + r' : \(ofSymmNsymm \d+ \d+\)\.encard = \d+ :=) by\n  sorry',
                 r'\1\n  mod_cast RACert.S%dN%d.count' % (s, n), src)
    assert 'sorry' not in src
    open(path, 'w').write(src)


main()
