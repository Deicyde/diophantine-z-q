exec(open('/home/jackmccarthy/dzq-wt/pi0-prune/scratch/pi0-prune/tools/common.py').read())
OUT = '/home/jackmccarthy/dzq-wt/pi0-prune/ZInQKernel/Contrib/OneProof/Pi0Prune/Upper.lean'
HEADER = r'''import ZInQKernel.Contrib.OneProof.Pi0Prune.Old

/-!
# pi0-prune (3/3): the stack `sixContactMin_of_open17` … `_open29` without the two fields

The added-leaf bundles `OpenAddedLeaves12` (TailZ22) … `17` (TailZ34) copied without the fields
`deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` (suffix `P`), their maps copied without the two
assignments, and the stack theorems copied with the weak row (suffix `W`). The only changed term is
`x6Rows_of_open14W`, which calls `QMSplit.Moduli.x6Rows_of_leavesW` (no Deligne `π₀`, no `GeomConnOfAlgClosure`).
No `sorry`; standard axioms only.
-/

set_option linter.all false
set_option autoImplicit false
set_option maxHeartbeats 1000000
'''
def S(a, b, **kw):
    return (a, b, kw) if kw else (a, b)
DF = [r'^  deligneComponentsX6PrintedAb :', r'^  geomConnOfAlgClosure :']
X6SUB = ('''{ deligneX6P := (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsX6Printed_iff_ab_gl hR).mpr
        l.deligneComponentsX6PrintedAb
      geomConn := l.geomConnOfAlgClosure
      t5 :=''', '{ t5 :=')
SEGMENTS = [
  ('TailZ22.lean', [S(232, 258, drop=DF, note='structure without the two fields, docstring omitted')]),
  ('TailZ23.lean', [S(709, 721, subs=[X6SUB], note='the two leaves dropped'), S(737, 757), S(759, 767), S(769, 807),
                    S(809, 815)]),
  ('TailZ24.lean', [S(769, 810, drop=DF, note='structure without the two fields, docstring omitted'),
                    S(814, 830, drop=DF, note='two assignments dropped'), S(832, 837)]),
  ('TailZ25.lean', [S(136, 138)]),
  ('TailZ26.lean', [S(132, 170, drop=DF, note='structure without the two fields, docstring omitted'),
                    S(172, 190, drop=DF, note='two assignments dropped'), S(192, 194)]),
  ('TailZ27.lean', [S(124, 126)]),
  ('TailZ28.lean', [S(123, 125)]),
  ('TailZ29.lean', [S(120, 122)]),
  ('TailZ30.lean', [S(14, 51, drop=DF, note='structure without the two fields, docstring omitted'),
                    S(53, 70, drop=DF, note='two assignments dropped'), S(72, 75)]),
  ('TailZ31.lean', [S(14, 48, drop=DF, note='structure without the two fields, docstring omitted'),
                    S(50, 66, drop=DF, note='two assignments dropped'), S(68, 70)]),
  ('TailZ32.lean', [S(44, 46)]),
  ('TailZ33.lean', [S(121, 123)]),
  ('TailZ34.lean', [S(117, 152, drop=DF, note='structure without the two fields, docstring omitted'),
                    S(154, 169, drop=DF, note='two assignments dropped'), S(171, 173)]),
  ('TailZ35.lean', [S(115, 117)]),
]
FOOTER = ''
