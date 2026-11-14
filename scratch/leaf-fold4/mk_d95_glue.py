#!/usr/bin/env python3
"""leaf-fold4 (run once on the hand-written d95 draft): gluePieces_of_open4 = d90's gluePieces_of_open3 with
the listed replacements; tatePairingZl_of_leaves4 / detTate_of_leaves4 (DivisiblePoints dropped); the
DivisiblePoints field, addedLeaves3_of_open4 and glue3_of_open4 removed. Run from scratch/leaf-fold4."""
d90=open('partsF/d90_fold3.lean').read()
i=d90.index('theorem gluePieces_of_open3'); j=d90.index('heightCopies := G0HeightCopies.heightCopiesAgree }')
body=d90[i:j+len('heightCopies := G0HeightCopies.heightCopiesAgree }')]
R=[('theorem gluePieces_of_open3 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves3)\n    (l : OpenAddedLeaves3) (g : OpenGlue3) : GluePieces :=',
    'theorem gluePieces_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)\n    (l : OpenAddedLeaves4) (g : OpenGlue4) : GluePieces :='),
   ('textbookLeaves2_of_open3 t','textbookLeaves2_of_open3 (textbookLeaves3_of_open4 t)'),
   ('(g.periodMapGlue r.r1r2)','(periodMapGlue_of_leaves4 r.r1r2 t.t5 t.homLatticeCorr l.cmDescends)'),
   ('g.hauptmodulUnique l.qmDenZeroCM3','hauptmodulUnique_proved4\n        (qmDenZeroCM3_of_leaves4 r.r4 l.gammaStarGen l.valenceBoundGammaStar)'),
   ('g.chartProper g.chartQuasiFinite','chartProper_proved4 chartQuasiFinite_proved4'),
   ('t.t5 t.t26 t.t35',"t.t5 (tateModuleFree_of_t5' t.t5) t.t35"),
   ('G0Galois.detTate_of_leaves l.t09SymmIsogenyExists l.isogenyQuasiInverse\n            l.divisiblePoints t.t26,',
    "detTate_of_leaves4 l.t09SymmIsogenyExists l.isogenyQuasiInverse t.t5\n            (tateModuleFree_of_t5' t.t5),"),
   ("linkedTateLocal_of_leaves3 r.r6 t.t5 t.t26 g.abVarSpreadsOut l.properSmoothGenConnected",
    "linkedTateLocal_of_leaves3 r.r6 t.t5 (tateModuleFree_of_t5' t.t5)\n            (abVarSpreadsOut_of_ega4 l.egaIV_8_8_2_ii l.egaIV_8_10_5_xii l.egaIV_17_7_8_ii)\n            (properSmoothGenConnected_of_zariski4 l.zariskiConnectedness)"),
]
for a,b in R:
    assert body.count(a)==1,(a,body.count(a)); body=body.replace(a,b)
import re
assert not re.search(r'(?<![\w.])g\.(?!heckeVertWitness)', body), 'g.'
for bad in ['t.t26','l.divisiblePoints','l.properSmoothGenConnected','l.qmDenZeroCM3']: assert bad not in body, bad
doc='''/-- **Leaves.lean's `GluePieces` from leaf-fold4's open statements** (leaf-fold3's `gluePieces_of_open3`,
verbatim but for: the fields closed by leaf-fold4 replaced by their theorems above; T26 from T5
(`tateModuleFree_of_t5'`); `DetTate` from `detTate_of_leaves4`, i.e. without the leaf `DivisiblePoints`). -/
'''
det='''open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj in
/-- **`TatePairingZl` without `DivisiblePoints`** (leaf-fold3's `G0Galois.tatePairingZl_of_leaves`, verbatim
but for the surjectivity of `T_ℓ A → A(K̄)[ℓᵏ]`, which comes from T5 through t5-torsion's
`T5Torsion.TateFree.tate_surj_of_torsionStructure` (module `LF4T5`, kernel objects; `toAbVarK4 A` has the
same scheme) instead of `WeilPairing.tate_surj (hD …)`). -/
theorem tatePairingZl_of_leaves4 (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hT5 : PkgI2.TorsionStructure.{0}) :
    G0Galois.TatePairingZl := by
  intro K _ _ A ℓ _
  haveI : NeZero (ℓ : K) := ⟨by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨S⟩ := h9 K A
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  obtain ⟨g, hg⟩ := WeilPairing.exists_tmu_gen K ℓ
  refine ⟨(WeilPairing.tatePairing S.D S.lam (NeZero.ne _)).compr₂ (WeilPairing.tmuCoordLin hg),
    ?_, ?_, ?_⟩
  · intro x hx
    exact WeilPairing.tatePairing_left_ker S.D S.lam hd hψ (NeZero.ne _)
      (fun k t ht => _root_.T5Torsion.TateFree.tate_surj_of_torsionStructure
        (torsionStructureK_of4 hT5) K (toAbVarK4 A) ℓ (NeZero.ne _) k t ht) x
      fun y => WeilPairing.tmuCoordLin_injective hg (by rw [map_zero]; exact hx y)
  · intro x
    simp only [LinearMap.compr₂_apply]
    rw [WeilPairing.tatePairing_self S.D S.lam S.symm (NeZero.ne _) x, map_zero]
  · intro σ x y
    simp only [LinearMap.compr₂_apply]
    have h := congrArg (WeilPairing.tmuCoordLin hg)
      (WeilPairing.tatePairing_cyclotomic S.D S.lam σ x y)
    rw [map_smul, smul_eq_mul] at h
    exact h

/-- **`DetTate` from T9 (restated), `IsogenyQuasiInverse`, T5 and T26** (leaf-fold3's
`G0Galois.detTate_of_leaves` with `tatePairingZl_of_leaves4`). -/
theorem detTate_of_leaves4 (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hT5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) : G0Galois.DetTate :=
  G0Galois.detTate_of_zl (tatePairingZl_of_leaves4 h9 hQ hT5) hT

'''
s=open('partsF/d95_fold4.lean').read()
s=s.replace('  divisiblePoints : WeilPairing.DivisiblePoints\n','',1)
i=s.index("/-- leaf-fold3's added-leaf bundle from leaf-fold4's. -/"); j=s.index('/-- **G0 with only the open leaves')
s=s[:i]+det+doc+body+'\n\n'+s[j:]
a='''  sixContactMin_of_open3 r (textbookLeaves3_of_open4 t) (addedLeaves3_of_open4 r l)
    (glue3_of_open4 t l g)'''
assert a in s
s=s.replace(a,'''  sixContactMin_of_leavesR3 (researchLeaves3_of_open2 r)
    (textbookLeaves_of_open2 (textbookLeaves2_of_open3 (textbookLeaves3_of_open4 t)))
    (gluePieces_of_open4 r t l g)''')
s=s.replace('#print axioms HSyn.addedLeaves3_of_open4\n#print axioms HSyn.glue3_of_open4\n','#print axioms HSyn.tatePairingZl_of_leaves4\n#print axioms HSyn.detTate_of_leaves4\n#print axioms HSyn.gluePieces_of_open4\n')
s=s.replace("* `OpenAddedLeaves4`: 21 leaves;","* `OpenAddedLeaves4`: 20 leaves (`DivisiblePoints` no longer needed);")
open('partsF/d95_fold4.lean','w').write(s)
print('ok')
