# rv-qm-polar's repairs (docs/research/rv-qm-polar.md §4, item 2) applied to the docstrings of
# QML3, R1fp, R5fp, R5fpCount and QMLeaves in ZInQKernel/HDecomp/QM/ (docstrings only).
import sys
D = 'ZInQKernel/HDecomp/QM/'
LP = ('Lemma P (rv-qm-polar §0): for a fixed `μ` (N5\'s `2j+ij`), the type-`μ` principal\n'
      'polarization of `(A, ι)` exists and is unique in characteristic 0, also at CM points;\n'
      'VERIFIED as an argument, lattice cores compiled (`RvQMPolar.eq_pm_E0_of_principal`,\n'
      '`RvQMPolar.type_eq_mu_mul`, `RvQMPolar.lemmaP_lattice` in `QM/Polar.lean`), published\n'
      'locators UNVERIFIED')
REP = {
 'Structures.lean': [(
  '(No polarization:\n'
  'for this datum a principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` exists and\n'
  'is unique, bp-qmmoduli §2.2, whose lattice core is `BPQM.eq_pm_E0_of_principal`.) -/',
  '(No polarization:\n'
  'by ' + LP + '. Without fixing `μ` it is\n'
  'not unique.) -/')],
 'Leaves.lean': [(
  '`M3 K` drops `λ` (bp-qmmoduli §2.2: for this\n'
  'datum `λ` exists and is unique in characteristic 0; SPECULATIVE until reviewed, lattice core\n'
  'proved as `BPQM.eq_pm_E0_of_principal`; not needed on Buzzard\'s route)',
  '`M3 K` drops `λ` (' + LP + ';\nnot needed on Buzzard\'s route)'), (
  'On the Shimura–Deligne route the leaf is "published\n'
  'theorem + bp-qmmoduli §2.2" (existence and uniqueness of `λ` for `(A, ι)`), and §2.2 is\n'
  'SPECULATIVE (unreviewed; uniqueness checked by the leaf-qm-fp review, existence over `ℂ` by class\n'
  'number one and the sign argument, unformalized).',
  'On the Shimura–Deligne route the leaf is "published\n'
  'theorem + Lemma P": the published moduli theorems are for the type-`μ` PEL problem; the λ-free\n'
  'leaves are their consequences via Lemma P (see above) and do not depend on the choice of `μ`.'), (
  'which uses bp-qmmoduli §2.2\n'
  '(the polarization exists and is unique; SPECULATIVE, see `R1fp`);',
  'which uses Lemma P\n'
  '(rv-qm-polar §0: for a fixed `μ` the type-`μ` polarization exists and is unique; see `R1fp`);'), (
  'points of `X₆(ℚ̄)` are classes of QM pairs (bp-qmmoduli\n'
  '§2.2, SPECULATIVE).',
  'points of `X₆(ℚ̄)` are classes of QM pairs (Lemma P,\n'
  'rv-qm-polar §0; see `R1fp`).'), (
  'rests on the published theorems **plus**\n'
  'bp-qmmoduli §2.2 (the polarization of a QM pair `(A, ι)` exists and is unique; SPECULATIVE until\n'
  'reviewed), because `QML3`/`QMPair` omit `λ`. Polarizations cannot be stated in Lean today\n'
  '(no dual abelian variety), so §2.2 cannot be carried as a separate Lean hypothesis.',
  'rests on the published theorems **plus**\n'
  + LP + ', because `QML3`/`QMPair` omit `λ`. The published moduli theorems are for the\n'
  'type-`μ` PEL problem; the λ-free leaves are their consequences via Lemma P and do not depend\n'
  'on the choice of `μ`. Polarizations cannot be stated in Lean today (no dual abelian variety),\n'
  'so Lemma P cannot be carried as a separate Lean hypothesis.')]}
for f, reps in REP.items():
    s = open(D + f).read()
    for a, b in reps:
        assert s.count(a) == 1, (f, a[:40])
        s = s.replace(a, b)
    open(D + f, 'w').write(s)
print('ok')
