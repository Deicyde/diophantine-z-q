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
  ('TailZ22.lean', [('OpenAddedLeaves12', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'structure without the two fields, docstring omitted', 'nodoc': True})]),
  ('TailZ23.lean', [('x6Rows_of_open14', {'subs': [('{ deligneX6P := (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsX6Printed_iff_ab_gl hR).mpr\n        l.deligneComponentsX6PrintedAb\n      geomConn := l.geomConnOfAlgClosure\n      t5 :=', '{ t5 :=')], 'note': 'the two leaves dropped'}), ('addedLeaves9_of_open14', {}), ('ss1_ss3_of14', {}), ('researchLeaves9_of_open14', {}), ('sixContactMin_of_open17', {})]),
  ('TailZ24.lean', [('OpenAddedLeaves13', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'structure without the two fields, docstring omitted', 'nodoc': True}), ('addedLeaves12_of_open13', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'two assignments dropped'}), ('sixContactMin_of_open18', {})]),
  ('TailZ25.lean', [('sixContactMin_of_open19', {})]),
  ('TailZ26.lean', [('OpenAddedLeaves14', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'structure without the two fields, docstring omitted', 'nodoc': True}), ('openAddedLeaves13_of_OpenAddedLeaves14', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'two assignments dropped'}), ('sixContactMin_of_open20', {})]),
  ('TailZ27.lean', [('sixContactMin_of_open21', {})]),
  ('TailZ28.lean', [('sixContactMin_of_open22', {})]),
  ('TailZ29.lean', [('sixContactMin_of_open23', {})]),
  ('TailZ30.lean', [('OpenAddedLeaves15', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'structure without the two fields, docstring omitted', 'nodoc': True}), ('openAddedLeaves14_of_OpenAddedLeaves15', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'two assignments dropped'}), ('sixContactMin_of_open24', {})]),
  ('TailZ31.lean', [('OpenAddedLeaves16', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'structure without the two fields, docstring omitted', 'nodoc': True}), ('openAddedLeaves15_of_OpenAddedLeaves16', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'two assignments dropped'}), ('sixContactMin_of_open25', {})]),
  ('TailZ32.lean', [('sixContactMin_of_open26', {})]),
  ('TailZ33.lean', [('sixContactMin_of_open27', {})]),
  ('TailZ34.lean', [('OpenAddedLeaves17', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'structure without the two fields, docstring omitted', 'nodoc': True}), ('openAddedLeaves16_of_OpenAddedLeaves17', {'drop': ['^  deligneComponentsX6PrintedAb :', '^  geomConnOfAlgClosure :'], 'note': 'two assignments dropped'}), ('sixContactMin_of_open28', {})]),
  ('TailZ35.lean', [('sixContactMin_of_open29', {})]),
]

FOOTER = ''
