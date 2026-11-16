"""pi0-fold step 1: carry the weak row `LeafAdopt.R1R2fpRepW` (R1R2fpRep without R1pi0Props) through the chain.
Every edit is an exact replacement asserted to occur once (line-anchored where given)."""
import re
H = 'ZInQKernel/OneProof/H/'
files = {}
def get(f):
    if f not in files: files[f] = open(H + f + '.lean').read()
    return files[f]
def rep(f, a, b, n=1):
    t = get(f)
    assert t.count(a) == n, (f, a, t.count(a))
    files[f] = t.replace(a, b)
def switch_line(f, lineno, expect):
    """replace LeafAdopt.R1R2fpRep (whole word) by LeafAdopt.R1R2fpRepW on one line."""
    ls = get(f).split('\n')
    l = ls[lineno - 1]
    assert expect in l, (f, lineno, l)
    new = re.sub(r'LeafAdopt\.R1R2fpRep(?![\w\'])', 'LeafAdopt.R1R2fpRepW', l)
    assert new != l, (f, lineno, l)
    ls[lineno - 1] = new
    files[f] = '\n'.join(ls)

# --- line switches (binders and fields; producers' conclusions are kept strong) ---
SW = [
 ('LPrefix', 11610, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('LPrefix', 13644, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('TailC', 8342, 'theorem fibreQMPeriod_of_named_rep (h : LeafAdopt.R1R2fpRep)'),
 ('TailC', 8449, 'theorem fibreQMPeriod_main_rep (h : LeafAdopt.R1R2fpRep)'),
 ('TailD', 42, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('TailD', 468, '  r1bFamily : ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailD', 473, '  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailE', 6460, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('TailE', 6462, '  r1b : ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailE', 6555, '  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailI', 78, 'theorem propTSAll_of_pieces3 (hR : LeafAdopt.R1R2fpRep)'),
 ('TailI', 183, '  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailK', 73, 'theorem periodMapGlue_of_leaves4 (h : LeafAdopt.R1R2fpRep)'),
 ('TailN', 38, 'theorem heckeVertWitness_of_leaves5 (hL : VertWitness.ShimuraGoodReduction) (h : LeafAdopt.R1R2fpRep)'),
 ('TailN', 67, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('TailN', 69, '  r1b : ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailO', 1179, '    (hRep : LeafAdopt.R1R2fpRep) (Q : QML3 ℂ)'),
 ('TailO', 1304, '    (hRep : LeafAdopt.R1R2fpRep) : CMDescends := by'),
 ('TailU', 1967, '    ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailU', 1991, 'theorem x6ConicModel_of (hR : LeafAdopt.R1R2fpRep)'),
 ('TailU', 2274, '    ∀ h : LeafAdopt.R1R2fpRep,'),
 ('TailX', 74, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('TailZ15', 26, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('TailZ20', 371, "theorem x6ConicModel_of_canonical' (hR : LeafAdopt.R1R2fpRep)"),
 ('TailZ20', 1030, 'theorem pairsLift_of_rep (h : LeafAdopt.R1R2fpRep)'),
 ('TailZ20', 1064, 'theorem coarseFactor_of_rep (hR : LeafAdopt.R1R2fpRep)'),
 ('TailZ20', 1085, "theorem coarseFactor_of_rep' (hR : LeafAdopt.R1R2fpRep)"),
 ('TailZ20', 1912, 'theorem x6ConicModel_of_elkies (hR : LeafAdopt.R1R2fpRep)'),
 ('TailZ20', 1923, 'theorem x6ConicModel_of_elkies_t5 (hR : LeafAdopt.R1R2fpRep)'),
 ('TailZ4', 67, '  r1r2 : LeafAdopt.R1R2fpRep'),
 ('TailZ5', 260, 'theorem r1rec_of_rep (h : LeafAdopt.R1R2fpRep)'),
 ('TailZ5', 269, 'theorem r5fp_of_rep (h : LeafAdopt.R1R2fpRep)'),
 ('TailZ9', 26, '  r1r2 : LeafAdopt.R1R2fpRep'),
]
for f, n, e in SW: switch_line(f, n, e)

# --- LPrefix: the weak row, its implication, and the destructurer on the weak row ---
rep('LPrefix', '''      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

''', '''      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

/-- **`R1R2fpRep` without its last clause `R1pi0Props X`** (pi0-fold, from pi0-prune). On the single proof the clause
(`X₆` geometrically connected) was produced from the two added leaves `deligneComponentsX6PrintedAb` and
`geomConnOfAlgClosure` and read by no consumer; the chain carries this weak row instead (`R1R2fpRepW_of_rep`). -/
def R1R2fpRepW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- The row `R1R2fpRep` implies its weak form (pi0-fold). -/
theorem R1R2fpRepW_of_rep (h : R1R2fpRep) : R1R2fpRepW := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩

''')
rep('LPrefix', '''of leaf-qm-fp (`conj_iso_of_rational`, `cm_of_val`, `residue_unramified_over_branch`,
`exists_fibre_object`, `leaves_on_one_witness`, ...) applies to it. -/
theorem R1R2fp_of_rep (h : R1R2fpRep) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h''',
'''of leaf-qm-fp (`conj_iso_of_rational`, `cm_of_val`, `residue_unramified_over_branch`,
`exists_fibre_object`, `leaves_on_one_witness`, ...) applies to it. pi0-fold: stated on the weak row `R1R2fpRepW`
(the clause `R1pi0Props` was never used here). -/
theorem R1R2fp_of_rep (h : R1R2fpRepW) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩ := h''')

# --- TailO: cmDescends_of on the weak row (cmDescends_ofW); the strong form kept for st-qbar's GapST.cmDescends_of ---
rep('TailO', '''/-- **`CMDescends` from `STQM`, `T11b_Rigidity`, `TorsionDescends` and `R1R2fpRep` (proved).** -/
theorem cmDescends_of (hST : STQM)''', '''/-- **`CMDescends` from `STQM`, `T11b_Rigidity`, `TorsionDescends` and the weak row `R1R2fpRepW` (proved;
pi0-fold: `cmDescends_of` with the weak row, same proof).** -/
theorem cmDescends_ofW (hST : STQM)''')
rep('TailO', '''    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_ofNat]⟩,
      hiso⟩

end Glue2''', '''    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_ofNat]⟩,
      hiso⟩

/-- **`CMDescends` from `STQM`, `T11b_Rigidity`, `TorsionDescends` and `R1R2fpRep` (proved).** pi0-fold: through
`cmDescends_ofW`; kept for st-qbar's `GapST.cmDescends_of`. -/
theorem cmDescends_of (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (hTD : TorsionDescends)
    (hRep : LeafAdopt.R1R2fpRep) : CMDescends :=
  cmDescends_ofW hST hR hTD (LeafAdopt.R1R2fpRepW_of_rep hRep)

end Glue2''')
rep('TailO', '''  G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of l.stQM (t11b_of_exists5 t.t11bExists)''',
    '''  G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_ofW l.stQM (t11b_of_exists5 t.t11bExists)''')

# --- TailX: stQM from the weak row ---
rep('TailX', 'import ZInQKernel.Contrib.OneProof.STQM\n', 'import ZInQKernel.Contrib.OneProof.STQM\nimport ZInQKernel.Contrib.OneProof.Pi0FoldSTQM\n')
rep('TailX', '  stQM := _root_.GapST.stQM_of r.r1r2 l.y3Connected', '  stQM := _root_.GapST.stQM_ofW r.r1r2 l.y3Connected')

# --- destructuring patterns one conjunct shorter ---
rep('TailZ5', '  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, -, -, hrec, -, -, -⟩ := h', '  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, -, -, hrec, -, -⟩ := h')
rep('TailZ5', '  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, -, h5, -⟩ := h', '  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, -, h5⟩ := h')
rep('TailZ20', '  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, hs, -, -⟩ := h', '  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, hs, -⟩ := h')

# --- TailZ21: the strong producer feeds the switched consumer; the weak producers ---
rep('TailZ21', '  x6ConicModel_of_elkies_t5 (r1r2_of_published hD hE hT hB hR hG) (elkiesConicX6_of_equations hC) hT',
    '  x6ConicModel_of_elkies_t5 (LeafAdopt.R1R2fpRepW_of_rep (r1r2_of_published hD hE hT hB hR hG))\n'
    '    (elkiesConicX6_of_equations hC) hT')
prod = open('scratch/pi0-fold/producers.lean').read()
rep('TailZ21', '''      L.elkiesEq⟩

end HDec.QMSplit.Moduli''', '''      L.elkiesEq⟩

''' + prod + '''
end HDec.QMSplit.Moduli''')

# --- TailZ23: the two X6 rows from the weak producers (the two added leaves are no longer read) ---
rep('TailZ23', '''/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open13`). -/
theorem x6Rows_of_open14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    LeafAdopt.R1R2fpRep ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw
  QMSplit.Moduli.x6Rows_of_leaves
    { deligneX6P := (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsX6Printed_iff_ab_gl hR).mpr
        l.deligneComponentsX6PrintedAb
      geomConn := l.geomConnOfAlgClosure
      t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed''',
'''/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open13`). pi0-fold: the weak row
`R1R2fpRepW` from `x6Rows_of_leavesW`, whose base witness is González–Rotger's (`GonzalezRotgerX6`); the added leaves
`deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` are no longer read. -/
theorem x6Rows_of_open14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw
  QMSplit.Moduli.x6Rows_of_leavesW
    { t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed''')

for f, t in files.items():
    open(H + f + '.lean', 'w').write(t)
print('edited', sorted(files))

# --- fix-ups found by the build (applied by hand, recorded here) ---
# TailZ17 researchLeaves10_of_open11: r1r2 := LeafAdopt.R1R2fpRepW_of_rep ((r1R2fpRep_iff_ab ...).mpr r.r1r2Ab)
