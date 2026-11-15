"""yu-prune step 1 (plumbing): the consumers of `PkgI3.QMDichotomyYu` take `HDec.QMLattice.YuB6Alg` instead.

* `HDec.QMLattice.YuB6Alg` (a `def ... : Prop`) moves from ZInQKernel/Contrib/OneProof/QMLattice.lean to TailA
  (before `namespace G0FibreSimple`), unchanged, so the consumers in TailA-TailK can name it; plus the bridge
  `G0FibreSimple.yuB6Alg_of_qmDichotomyYu : PkgI3.QMDichotomyYu → YuB6Alg` for the off-chain readers of `.t27`.
* binders `(t27|hT27|h27 : PkgI3.QMDichotomyYu)` become `(hYu : QMLattice.YuB6Alg)` (the declaration's other uses
  of the binder are renamed); the four application lines use `hYu k A hA q` (scratch/gt-qm/Reroute.lean).
* `fibreSimple_of_leaves`, `gluePieces_of_open4` and `sixContactMin_of_open4` ... `_open23` take `hYu`;
  `sixContactMin_of_open24` (TailZ30, after QMLattice) supplies `QMLattice.yuB6Alg_of' t.uniformizationLeafAll
  t.gagaMorphism t.mumfordTorsionAlgClosed`.
* off-chain readers of a bundle's `t27` pass `G0FibreSimple.yuB6Alg_of_qmDichotomyYu t.t27`.
"""
import re
H = 'ZInQKernel/OneProof/H/'
files = {}
def get(f):
    if f not in files: files[f] = open(f).read()
    return files[f]
def put(f, s): files[f] = s
def sub1(f, old, new, count=1):
    s = get(f)
    n = s.count(old)
    assert n == count, (f, old[:80], n)
    put(f, s.replace(old, new))

decl_start = re.compile(r'^(theorem|def|lemma|structure|example|/--|#print|end |namespace |open |section)')
def span(s, name):
    """line range [i, j) of `theorem NAME`: up to the next blank line."""
    L = s.split('\n')
    hits = [i for i, l in enumerate(L) if re.match(r'^theorem ' + re.escape(name) + r'[\s(]', l)]
    assert len(hits) == 1, (name, hits)
    i = hits[0]; j = i + 1
    while j < len(L) and L[j].strip() != '' and not decl_start.match(L[j]): j += 1
    return L, i, j
def rebind(f, name, old_binder):
    """replace the binder `(X : PkgI3.QMDichotomyYu)` by `(hYu : QMLattice.YuB6Alg)`, rename X in the decl."""
    s = get(f); L, i, j = span(s, name)
    body = '\n'.join(L[i:j])
    assert body.count(f'({old_binder} : PkgI3.QMDichotomyYu)') == 1, (name, old_binder)
    body = body.replace(f'({old_binder} : PkgI3.QMDichotomyYu)', '(hYu : QMLattice.YuB6Alg)')
    body = re.sub(r"(?<![\w'.])" + old_binder + r"(?![\w'])", 'hYu', body)
    L[i:j] = body.split('\n'); put(f, '\n'.join(L))
def edit_decl(f, name, pairs):
    s = get(f); L, i, j = span(s, name)
    body = '\n'.join(L[i:j])
    for old, new in pairs:
        assert body.count(old) == 1, (name, old, body.count(old))
        body = body.replace(old, new)
    L[i:j] = body.split('\n'); put(f, '\n'.join(L))

# --- QMLattice: the def moves out
QML = 'ZInQKernel/Contrib/OneProof/QMLattice.lean'
q = get(QML)
a = q.index('/-- **Yu\'s theorem (Thm 1.1) at `B = (2, −3)`')
b = q.index('/-- **Yu\'s dichotomy at `B = (2, −3)` for QM by `𝒪`')
moved = q[a:b]
assert moved.count('def YuB6Alg : Prop :=') == 1
put(QML, q[:a] + '-- `YuB6Alg` is declared in `ZInQKernel/OneProof/H/TailA.lean` (moved there by yu-prune, unchanged, so that\n'
    '-- the chain\'s four consumers of Yu\'s theorem can take it as their hypothesis).\n\n' + q[b:])

# --- TailA
A = H + 'TailA.lean'
sub1(A, 'noncomputable section\n\nnamespace G0FibreSimple\n',
     'noncomputable section\n\nnamespace QMLattice\n\nopen scoped Quaternion\n\n' + moved.rstrip() + '\n\nend QMLattice\n\n'
     'namespace G0FibreSimple\n')
sub1(A, '''theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩
''', '''theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩

/-- (yu-prune) `QMLattice.YuB6Alg` from T27 (`PkgI3.QMDichotomyYu`): take `(a, b) = (2, −3)` and the embedding of
the QM structure. Used only by off-chain readers of the old bundles' `t27`. -/
theorem yuB6Alg_of_qmDichotomyYu (h : PkgI3.QMDichotomyYu) : QMLattice.YuB6Alg := by
  intro k _ _ _ _ A hA q
  exact PkgI3.qmDichotomy_B6 h k A hA B6_isUnit (qm_embeds_end0 q)
''')
rebind(A, 'fibreSimple_of_pieces', 't27')
edit_decl(A, 'fibreSimple_of_pieces', [('have hY := PkgI3.qmDichotomy_B6 hYu LeafQM.AV.Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q)',
                                        'have hY := hYu LeafQM.AV.Qbar P.A P.surface P.q')])
rebind(A, "fibreSimple_of_pieces'", 't27')
rebind(A, "fibreSimple_of_pieces''", 't27')
edit_decl(A, 'fibreSimple_of_leaves', [('(t : HSyn.TextbookLeaves) (hMul : MulIsogeny)',
                                        '(t : HSyn.TextbookLeaves) (hYu : QMLattice.YuB6Alg) (hMul : MulIsogeny)'),
                                       ('t.t6 t.t27 hMul', 't.t6 hYu hMul')])

# --- TailC
C = H + 'TailC.lean'
rebind(C, 'comIntOrQuadOrder_of', 't27')
edit_decl(C, 'comIntOrQuadOrder_of', [('rcases PkgI3.qmDichotomy_B6 hYu Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q) with',
                                       'rcases hYu Qbar P.A P.surface P.q with')])
for n in ['fibreComTrivialFull_of_leaves', 'comIntOrQuadOrder_of_leaves', "fibreComTrivialFull_of_leaves'",
          "fibreComTrivialFull_of_leaves''", 'endEqOFibre_of', "kernelFieldExists_of_split''", 'kernelFieldExists_of_final',
          "kernelFieldExists_of_final'", 'kernelFieldExists_of_rigidity']:
    rebind(C, n, 't27')
edit_decl(C, 'endEqOFibre_of', [('''have hY := PkgI3.qmDichotomy_B6 hYu Qbar P.A P.surface G0FibreSimple.B6_isUnit
    (G0FibreSimple.qm_embeds_end0 P.q)''', 'have hY := hYu Qbar P.A P.surface P.q')])

# --- TailF
F = H + 'TailF.lean'
for n in ['G0ModField.KernelField.kernelFieldExists_of_five', 'kernelFieldExists_of_semilinear', 'kernelFieldExists_of_twist',
          'kernelFieldExists_of_descent', 'kernelFieldExists_of_kerUnitOpen', "kernelFieldExists_of_kerUnitOpen'",
          'kernelFieldExists_of_mulIsogeny']:
    rebind(F, n, 't27')
rebind(F, 'qmEndRank_of', 'hT27')
edit_decl(F, 'qmEndRank_of', [('''  rcases hYu Ω A'' hdimA'' 2 (-3) PkgI3.quatIndefinite_two_neg_three quatB6_isUnit
      (quatEmbed A'' φ'') with he | ⟨d, hd, he⟩''', '''  haveI : Algebra.IsAlgebraic ℚ Ω := by
    haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
    exact Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  rcases hYu Ω A'' hdimA'' ⟨φ'', (HSyn.LinkedTate.endBC_injective A' Ω).comp hφ⟩ with he | ⟨d, hd, he⟩''')])
rebind(F, 'qmEndRank_of_leaves', 'hT27')

# --- TailI
I = H + 'TailI.lean'
rebind(I, 'qmEndRank_of_leaves3', 'hT27')
rebind(I, 'linkedTateLocal_of_leaves3', 'h27')
BR = 'G0FibreSimple.yuB6Alg_of_qmDichotomyYu'
edit_decl(I, 'gluePieces_of_open3', [('hMob t.t27 t.t6', f'hMob ({BR} t.t27) t.t6'),
                                     ('fibreSimple_of_leaves t3 mulIsogeny_proved', f'fibreSimple_of_leaves t3 ({BR} t3.t27) mulIsogeny_proved'),
                                     ('t.t5 t.t27\n', f't.t5 ({BR} t.t27)\n'),
                                     ('t.t6 t.t27)))', f't.t6 ({BR} t.t27))))')])
# --- TailE (off chain)
E = H + 'TailE.lean'
edit_decl(E, 'gluePieces_of_open2', [('hMob t.t27 t.t6', f'hMob ({BR} t.t27) t.t6'),
                                     ('fibreSimple_of_leaves t3 mulIsogeny_proved', f'fibreSimple_of_leaves t3 ({BR} t3.t27) mulIsogeny_proved'),
                                     ('t.t5 t.t27\n', f't.t5 ({BR} t.t27)\n')])
# --- TailD (off chain)
D = H + 'TailD.lean'
edit_decl(D, 'fibreComTrivial_of_gp3', [('(mobiusGlue_of_gp3 t gp) t.t27 t.t6', f'(mobiusGlue_of_gp3 t gp) ({BR} t.t27) t.t6')])
edit_decl(D, 'fibreSimple_of_gp3', [('G0FibreSimple.fibreSimple_of_leaves t\n', f'G0FibreSimple.fibreSimple_of_leaves t ({BR} t.t27)\n')])
edit_decl(D, 'gluePieces_of_gluePieces3', [('t.t5 t.t27\n', f't.t5 ({BR} t.t27)\n')])

# --- TailK (on chain)
K = H + 'TailK.lean'
edit_decl(K, 'gluePieces_of_open4', [('(l : OpenAddedLeaves4) (g : OpenGlue4) : GluePieces :=',
                                      '(l : OpenAddedLeaves4) (g : OpenGlue4) (hYu : QMLattice.YuB6Alg) : GluePieces :='),
                                     ('hMob t.t27 t.t6', 'hMob hYu t.t6'),
                                     ('fibreSimple_of_leaves t3 mulIsogeny_proved', 'fibreSimple_of_leaves t3 hYu mulIsogeny_proved'),
                                     ('t.t5 t.t27\n', 't.t5 hYu\n'),
                                     ('t.t6 t.t27)))', 't.t6 hYu)))')])
edit_decl(K, 'sixContactMin_of_open4', [('(h20 : G0Split.R20Lower) : ZInQ.SixContactMin :=',
                                         '(h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :='),
                                        ('(gluePieces_of_open4 r t l g) h20', '(gluePieces_of_open4 r t l g hYu) h20')])

# --- threading open6 ... open23; open24 supplies it
chain = [('TailO', 6), ('TailX', 7), ('TailZ4', 8), ('TailZ9', 9), ('TailZ11', 10), ('TailZ13', 11), ('TailZ15', 12),
         ('TailZ17', 13), ('TailZ18', 14), ('TailZ19', 15), ('TailZ22', 16), ('TailZ23', 17), ('TailZ24', 18),
         ('TailZ25', 19), ('TailZ26', 20), ('TailZ27', 21), ('TailZ28', 22), ('TailZ29', 23), ('TailZ30', 24)]
for mod, n in chain:
    f = H + mod + '.lean'
    s = get(f); L, i, j = span(s, f'sixContactMin_of_open{n}')
    body = '\n'.join(L[i:j])
    if n != 24:
        assert body.count(') : ZInQ.SixContactMin :=') == 1, n
        body = body.replace(') : ZInQ.SixContactMin :=', ') (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=')
        body = body.rstrip() + ' hYu'
    else:
        body = body.rstrip() + '\n    (QMLattice.yuB6Alg_of\' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed)'
    L[i:j] = body.split('\n'); put(f, '\n'.join(L))
# the example after open6
sub1(H + 'TailO.lean', '''(_ : HDec.HSyn.OpenGlue6) (_ : HDec.HSyn.G0Split.R20Lower),
    _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6''', '''(_ : HDec.HSyn.OpenGlue6) (_ : HDec.HSyn.G0Split.R20Lower)
    (_ : HDec.QMLattice.YuB6Alg), _root_.ZInQ.SixContactMin :=
  HDec.HSyn.sixContactMin_of_open6''')

for f, s in files.items():
    open(f, 'w').write(s)
print('edited', len(files), 'files')
