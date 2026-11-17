"""charpoly-charp: the manual fold that removes the bundle field `charPolyIndepOfEllAlgClosed`.

Usage: python3 scratch/charpoly-charp/fold_edit.py --tree <repository root>   (edits the tree in place)

Edits (all under ZInQKernel/OneProof/H/; each asserted to match exactly once per listed occurrence):
1. TailK: `gluePieces_of_open4` calls `G0AssembleMod.linkedTateData_of_local_homFree t.t6 (tateModuleFree_of_t5' t.t5)`
   (ZInQKernel/Contrib/OneProof/CommonTraceHomFree.lean, imported) instead of
   `G0AssembleMod.linkedTateData_of_local t.t7`. This was the only reader of a T7 field on the route.
2. The T7 field `t7 : PkgI3.CharPolyIndepOfEll` is deleted from `TextbookLeaves`, `OpenTextbookLeaves` (LPrefix),
   `OpenTextbookLeaves2` (TailE), `OpenTextbookLeaves3` (TailI), `OpenTextbookLeaves4` (TailK), with its
   pass-through lines `t7 := t.t7`, and the two producers `t7 := t7_of_algClosed5 t.charPolyIndepOfEllAlgClosed`
   (TailN, TailO).
3. TailZ35: `r16 := R16Split.r16_of_printedC n.r16CoreY t.uniformizationLeafAll t.mumfordTorsionAlgClosed`
   (ZInQKernel/Contrib/OneProof/R16PrintedC.lean, imported) instead of `r16_of_printed ... t.charPolyIndepOfEllAlgClosed`.
4. The field `charPolyIndepOfEllAlgClosed` is deleted from `OpenTextbookLeaves5`..`13` (TailN, TailO, TailX, TailZ4,
   TailZ9, TailZ11, TailZ32, TailZ42, TailZ44) with its pass-through lines.
"""
import argparse
import os

H = 'ZInQKernel/OneProof/H/'

T7F = '  t7 : PkgI3.CharPolyIndepOfEll\n'
T7A = '  t7 := t.t7\n'
CPF = '  charPolyIndepOfEllAlgClosed : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed\n'
CPDOC = '  /-- av-b1, LEAF: Mumford §19 Thm 4 (consequence) over an algebraically closed field. -/\n'
CPP = '  t7 := t7_of_algClosed5 t.charPolyIndepOfEllAlgClosed\n'
CPAt = '  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed\n'
CPAn = '  charPolyIndepOfEllAlgClosed := n.charPolyIndepOfEllAlgClosed\n'

# (file, [(old, new, count)])
EDITS = [
    ('LPrefix', [(T7F, '', 2), (T7A, '', 1)]),
    ('TailE', [(T7F, '', 1), (T7A, '', 1)]),
    ('TailI', [(T7F, '', 1), (T7A, '', 1)]),
    ('TailK', [(T7F, '', 1), (T7A, '', 1),
               ('(G0AssembleMod.linkedTateData_of_local t.t7\n',
                "(G0AssembleMod.linkedTateData_of_local_homFree t.t6 (tateModuleFree_of_t5' t.t5)\n", 1),
               ('import ZInQKernel.OneProof.H.TailJ\n',
                'import ZInQKernel.OneProof.H.TailJ\nimport ZInQKernel.Contrib.OneProof.CommonTraceHomFree\n', 1)]),
    ('TailN', [(CPDOC + CPF, '', 1), (CPP, '', 1)]),
    ('TailO', [(CPDOC + CPF, '', 1), (CPP, '', 1)]),
    ('TailX', [(CPF, '', 1), (CPAt, '', 1)]),
    ('TailZ4', [(CPF, '', 1), (CPAt, '', 1)]),
    ('TailZ9', [(CPF, '', 1), (CPAt, '', 1)]),
    ('TailZ11', [(CPF, '', 1), (CPAt, '', 1)]),
    ('TailZ32', [(CPF, '', 1), (CPAn, '', 1)]),
    ('TailZ42', [(CPF, '', 1), (CPAn, '', 1)]),
    ('TailZ44', [(CPF, '', 1), (CPAn, '', 1)]),
    ('TailZ35', [('  r16 := _root_.R16Split.r16_of_printed n.r16CoreY t.mumfordTorsionAlgClosed '
                  't.charPolyIndepOfEllAlgClosed\n',
                  '  r16 := _root_.R16Split.r16_of_printedC n.r16CoreY t.uniformizationLeafAll '
                  't.mumfordTorsionAlgClosed\n', 1),
                 ('import ZInQKernel.Contrib.OneProof.R16Split\n',
                  'import ZInQKernel.Contrib.OneProof.R16Split\nimport ZInQKernel.Contrib.OneProof.R16PrintedC\n',
                  1)]),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tree', required=True)
    ap.add_argument('--check', action='store_true', help='only check that every pattern matches')
    a = ap.parse_args()
    for f, eds in EDITS:
        p = os.path.join(a.tree, H, f + '.lean')
        s = open(p).read()
        for old, new, n in eds:
            c = s.count(old)
            assert c == n, (f, old[:60], c, n)
            s = s.replace(old, new)
        if not a.check:
            open(p, 'w').write(s)
        print('ok', f)


if __name__ == '__main__':
    main()
