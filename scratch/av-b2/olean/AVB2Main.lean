import TailI
import ZInQKernel.Contrib.AVB2.SerreLemma

/-!
# av-b2: group B fields of leaf-fold3 — T9, `DivisiblePoints`, `SerreRigidity3`

Task av-b2, 2026-11-13. Compiled on top of leaf-fold3's olean chain (`import TailI`); every Prop
named here is the chain's own definition (no copy), so Lean checks the statements.

* `t9_of_leaves3`: `LeafPush.T09_WeilPairing` (field `t9`) from the fields `t09SymmIsogenyExists`
  and `isogenyQuasiInverse` (weil-pairing's `oldT9_of_symmIsogeny`; `OldT9.T09_WeilPairing` is the
  verbatim copy of `LeafPush.T09_WeilPairing` at universe `0`).
* `divisiblePoints_of_posChar`: `WeilPairing.DivisiblePoints` from `MulIsogenyPosChar` (multiplication
  by `n ≠ 0` is an isogeny in positive characteristic; the characteristic-0 case is g9-abvarbc's
  proved `MulIsogeny`).
* `serreRigidity3_of_T35`: `HeckeRest.SerreRigidity3` from T35 (`UniformizationExists`, field `t35`)
  and `HomLatticeCorr` (field `homLatticeCorr`), both already fields; with the proved `MulIsogeny`.
-/

noncomputable section

namespace HDec

namespace AVB2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## 1. T9 -/

/-- **T9 is glue** given the two `OpenAddedLeaves3` fields `t09SymmIsogenyExists` and
`isogenyQuasiInverse` (proof: weil-pairing's `oldT9_of_symmIsogeny`). -/
theorem t9_of_leaves3 (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) : LeafPush.T09_WeilPairing.{0} :=
  WeilPairing.oldT9_of_symmIsogeny h9 hQ

/-! ## 2. `DivisiblePoints` -/

/-- **Leaf (positive-characteristic half of "`[n]` is an isogeny").** Over a field `k` of positive
characteristic, multiplication by `n ≠ 0` on an abelian variety is finite and surjective.
Published: Mumford, *Abelian varieties*, §4, Application 2 (`n_X` is an isogeny of degree
`n^{2g}`, over an algebraically closed field) and §6; Milne, *Abelian varieties* (Cornell–Silverman
1986), Thm 8.2, over any field (locators UNVERIFIED). The degree is dropped, so a consequence of the
published statement. The characteristic-0 half is g9-abvarbc's proved `MulIsogeny`. -/
def MulIsogenyPosChar : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 → ringChar k ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

/-- `[n]` is an isogeny in every characteristic. -/
theorem mulIsogenyAll (hP : MulIsogenyPosChar) (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ)
    (hn : n ≠ 0) : PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom) := by
  by_cases h : ringChar k = 0
  · haveI : CharP k 0 := ringChar.eq_iff.1 h
    haveI : CharZero k := CharP.charP_to_charZero k
    exact HSyn.mulIsogeny_proved k A n hn
  · exact hP k A n hn h

/-- **Lifting `K̄`-points through a finite surjective `K`-endomorphism** (the fibre is a nonempty
finite `K̄`-scheme; its closed points are `K̄`-points). -/
theorem exists_lift_pt {K : Type} [Field K] (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    (hf : PkgI3.AbVar.IsIsogenyMor f) (z : A.Pt (AlgebraicClosure K)) :
    ∃ w : A.Pt (AlgebraicClosure K), w ≫ f = z := by
  obtain ⟨hfin, hsurj⟩ := hf
  let zl : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ A.X.left := z.left
  let s : pullback f.left zl ⟶ Spec (CommRingCat.of (AlgebraicClosure K)) := pullback.snd f.left zl
  haveI : IsFinite s := by dsimp [s]; infer_instance
  haveI : Surjective s := by dsimp [s]; infer_instance
  haveI : CompactSpace ((pullback f.left zl : Scheme) : Type) := QuasiCompact.compactSpace_of_compactSpace s
  haveI : Nonempty ((pullback f.left zl : Scheme) : Type) := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))) := inferInstance
    exact ⟨(s.surjective y).choose⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := ((pullback f.left zl : Scheme) : Type))
    isClosed_univ Set.univ_nonempty
  let pt := pointOfClosedPoint s x hx
  have hpt : pt ≫ s = 𝟙 _ := pointOfClosedPoint_comp s x hx
  have hz : zl ≫ A.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := Over.w z
  have hw : f.left ≫ A.X.hom = A.X.hom := Over.w f
  refine ⟨Over.homMk (pt ≫ pullback.fst f.left zl) ?_, ?_⟩
  · change (pt ≫ pullback.fst f.left zl) ≫ A.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    rw [Category.assoc, ← hw, pullback.condition_assoc, hz, ← Category.assoc]
    change (pt ≫ s) ≫ _ = _
    rw [hpt, Category.id_comp]
  · apply Over.OverMorphism.ext
    change (pt ≫ pullback.fst f.left zl) ≫ f.left = zl
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (pt ≫ s) ≫ _ = _
    rw [hpt, Category.id_comp]

/-- **`DivisiblePoints` from `MulIsogenyPosChar`** (characteristic 0: g9-abvarbc's `MulIsogeny`). -/
theorem divisiblePoints_of_posChar (hP : MulIsogenyPosChar) : WeilPairing.DivisiblePoints := by
  intro K _ A n hn z
  have hiso := mulIsogenyAll hP K A (n : ℤ) (by exact_mod_cast hn.ne')
  obtain ⟨w, hw⟩ := exists_lift_pt A _ hiso (Additive.toMul z)
  refine ⟨Additive.ofMul w, ?_⟩
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_ofMul, ← ZInQ.Contrib.AbVarBC.comp_natCast_hom A w n, hw]

/-! ## 3. `SerreRigidity3` -/

/-- `Spec σ : Spec ℂ → Spec K` as a morphism of `K`-schemes. -/
def sC {K : Type} [Field K] (σ : K →+* ℂ) :
    ZInQ.LeafPush2.cptObj σ ⟶ PkgI3.AbVar.ptObj (K := K) K :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ)) (by
    simp only [ZInQ.LeafPush2.cptObj, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- Precomposition with `Spec σ` is injective on `K`-points. -/
theorem sC_cancel {K : Type} [Field K] (σ : K →+* ℂ) {Y : Over (Spec (CommRingCat.of K))}
    {a b : PkgI3.AbVar.ptObj (K := K) K ⟶ Y} (h : sC σ ≫ a = sC σ ≫ b) : a = b := by
  haveI := ZInQ.Contrib.AbVarBC.epi_spec_map_field σ
  apply Over.OverMorphism.ext
  have h2 := congrArg CommaMorphism.left h
  simp only [Over.comp_left] at h2
  exact (cancel_epi (Spec.map (CommRingCat.ofHom σ))).1 h2

/-- **Torsion of `A(ℂ)_σ` comes from `A(K)`** for `K` algebraically closed of characteristic `0`
(`[N]` is finite by `MulIsogeny`; points of a finite `K`-scheme, g9-abvarbc's
`exists_lift_of_isFinite`). -/
theorem cpt_torsion_descends {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (A : PkgI3.AbVar K) (σ : K →+* ℂ) (N : ℕ) (hN : 0 < N) (x : ZInQ.LeafPush2.CPts A σ)
    (hx : x ^ N = 1) : ∃ y : A.Pt K, sC σ ≫ y = x := by
  letI : Algebra K ℂ := σ.toAlgebra
  have hfinN : IsFinite ((((N : ℕ) : ℤ) : PkgI3.AbVar.End A).hom.left) :=
    (HSyn.mulIsogeny_proved K A (N : ℤ) (by exact_mod_cast hN.ne')).1
  let fN : A.X.left ⟶ A.X.left := ((N : ℤ) : PkgI3.AbVar.End A).hom.left
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have h1 : x ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom = 1 := by
    rw [ZInQ.Contrib.AbVarBC.comp_natCast_hom, hx]
  have hq0 : x.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K ℂ)) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  haveI : IsFinite fN := hfinN
  let z : Spec (CommRingCat.of ℂ) ⟶ pullback fN e :=
    pullback.lift x.left (Spec.map (CommRingCat.ofHom (algebraMap K ℂ))) hq0
  obtain ⟨p0, hp0, hp0g⟩ := ZInQ.Contrib.AbVarBC.exists_lift_of_isFinite (Algebra.ofId K ℂ)
    (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ A.X.hom = pullback.snd fN e := by
    have hw : fN ≫ A.X.hom = A.X.hom := Over.w ((N : ℤ) : PkgI3.AbVar.End A).hom
    have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  refine ⟨Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ A.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl), ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((Algebra.ofId K ℂ : K →ₐ[K] ℂ) : K →+* ℂ)) ≫
    p0 ≫ pullback.fst fN e = x.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

/-- **Morphisms of abelian varieties over an algebraically closed `K` agreeing on `K`-points are
equal** (hom-unify's `hom_ext_of_cpts` with `K` for `ℂ`). -/
theorem hom_ext_of_pts {K : Type} [Field K] [IsAlgClosed K] {A B : PkgI3.AbVar K}
    (f f' : A.X ⟶ B.X) (h : ∀ p : A.Pt K, p ≫ f = p ≫ f') : f = f' := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  apply Over.OverMorphism.ext
  have hw : f.left ≫ B.X.hom = f'.left ≫ B.X.hom := by rw [Over.w f, Over.w f']
  have : LocallyOfFiniteType (f.left ≫ B.X.hom) := by rw [Over.w f]; infer_instance
  refine ext_of_apply_eq B.X.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx => ?_) hw
  let p0 := pointOfClosedPoint A.X.hom x hx
  let p : A.Pt K := Over.homMk p0 (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id,
      Spec.map_id]
    exact pointOfClosedPoint_comp A.X.hom x hx)
  have hp : p0 ≫ f.left = p0 ≫ f'.left := congrArg CommaMorphism.left (h p)
  have key : (p0 ≫ f.left) (A.X.hom x) = (p0 ≫ f'.left) (A.X.hom x) := by rw [hp]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, pointOfClosedPoint_apply] at key
  exact key

/-- **`SerreRigidity3` from T35 and `HomLatticeCorr`** (with the proved `MulIsogeny`). Embed
`ℚ̄ ↪ ℂ`; `A(ℂ) = ℂ^g/Λ` (T35); `φ` acts by a `ℂ`-linear `M` (HomLatticeCorr, clause 1); `M`
preserves `Λ`, `M^m − 1` maps `ℂ^g` into `Λ`, and `M ≡ 1 (mod 3Λ)` because `3`-torsion of `A(ℂ)`
comes from `A(ℚ̄)`, where `φ` fixes it; Serre's lemma (`lattice_serre`) gives `M = 1`, so `φ`
fixes `A(ℂ)`, hence `A(ℚ̄)`, hence `φ = 1`. -/
theorem serreRigidity3_of_T35 (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HomUnify.HomLatticeCorr) : HeckeRest.SerreRigidity3 := by
  intro A φ hφ hfix
  obtain ⟨m, hm, hφm⟩ := hφ
  let σ : AlgebraicClosure ℚ →+* ℂ :=
    ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : AlgebraicClosure ℚ →+* ℂ)
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hdisc, hΛ, hΦ⟩ := hU (AlgebraicClosure ℚ) A σ g hg
  obtain ⟨M, hM⟩ := hC.1 (AlgebraicClosure ℚ) A A σ g g Λ Λ Φ Φ hg hg hΦ hΦ φ
  obtain ⟨hadd, hker, hsurj, -, -⟩ := hΦ
  have hdiff : ∀ a b, Φ a = Φ b → a - b ∈ Λ := by
    intro a b hab
    rw [← hker]
    have h := hadd (a - b) b
    rw [sub_add_cancel, hab] at h
    exact mul_eq_right.1 h.symm
  have hMΛ : ∀ z ∈ Λ, M z ∈ Λ := by
    intro z hz
    rw [← hker, hM z, (hker z).2 hz, MonObj.one_comp]
  have hpowM : ∀ (k : ℕ) (z : Fin g → ℂ), Φ ((M ^ k) z) = Φ z ≫ (φ ^ k).hom := by
    intro k
    induction k with
    | zero =>
      intro z
      rw [pow_zero, pow_zero, Module.End.one_apply]
      exact (Category.comp_id _).symm
    | succ k ih =>
      intro z
      rw [pow_succ, Module.End.mul_apply, ih, hM z, pow_succ]
      exact Category.assoc _ _ _
  have hfin : ∀ z, (M ^ m) z - z ∈ Λ := by
    intro z
    refine hdiff _ _ ?_
    rw [hpowM, hφm]
    exact Category.comp_id _
  have h3 : ∀ z ∈ Λ, (3⁻¹ : ℂ) • (M z - z) ∈ Λ := by
    intro z hz
    set u : Fin g → ℂ := (3⁻¹ : ℂ) • z with hu
    have huz : u + u + u = z := by
      rw [hu, ← add_smul, ← add_smul]
      norm_num
    have hu3 : Φ u ^ 3 = 1 := by
      rw [pow_succ, pow_succ, pow_one, ← hadd, ← hadd, huz]
      exact (hker z).2 hz
    obtain ⟨y, hy⟩ := cpt_torsion_descends A σ 3 (by norm_num) (Φ u) hu3
    have hy3 : y ^ 3 = 1 := by
      apply sC_cancel σ
      rw [MonObj.comp_pow, hy, hu3, MonObj.comp_one]
    have hfu : Φ u ≫ φ.hom = Φ u := by
      rw [← hy, Category.assoc, hfix y hy3]
    have := hdiff (M u) u (by rw [hM u, hfu])
    rwa [hu, map_smul, ← smul_sub] at this
  haveI := hdisc
  have hM1 : M = 1 := ZInQ.Contrib.AVB2.lattice_serre Λ hΛ M hMΛ h3 hm hfin
  have hC1 : ∀ x : ZInQ.LeafPush2.CPts A σ, x ≫ φ.hom = x := by
    intro x
    obtain ⟨z, rfl⟩ := hsurj x
    rw [← hM z, hM1, Module.End.one_apply]
  have hK1 : ∀ y : A.Pt (AlgebraicClosure ℚ), y ≫ φ.hom = y ≫ 𝟙 _ := by
    intro y
    apply sC_cancel σ
    rw [← Category.assoc, hC1, Category.comp_id]
  have hφ1 : φ.hom = 𝟙 _ := hom_ext_of_pts φ.hom (𝟙 _) hK1
  exact PkgI3.AbVar.Hom.ext' hφ1

end AVB2

/-! ## 4. The fold: `sixContactMin_of_open3` with the three fields discharged -/

namespace HSyn

/-- `OpenTextbookLeaves3` without `t9` (T9 is glue from `t09SymmIsogenyExists` and
`isogenyQuasiInverse`, `AVB2.t9_of_leaves3`). Field types copied from leaf-fold3's
`partsF/d90_fold3.lean`. -/
structure OpenTextbookLeavesB2 : Prop where
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t10 : T10Etale.T10_TateDuality
  homLatticeCorr : HomUnify.HomLatticeCorr
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  t38 : X1Belyi.CurveOfFunctionFieldQ
  t40 : X1Belyi.X1RationalCusp
  t41 : ZInQ.H5Neron.NeronModelExists

/-- `OpenAddedLeaves3` without `serreRigidity3` (from T35 and `HomLatticeCorr`,
`AVB2.serreRigidity3_of_T35`) and with `divisiblePoints` replaced by `mulIsogenyPosChar`
(`AVB2.divisiblePoints_of_posChar`). -/
structure OpenAddedLeavesB2 : Prop where
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmHauptmodul : PkgI1.QMHauptmodul
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3
  senTwist : G0Galois.SenTwist
  finiteImageHT : G0Galois.FiniteImageHT
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  mulIsogenyPosChar : AVB2.MulIsogenyPosChar
  x6ConicModel : X6Kummer.X6ConicModel
  y3Connected : TSHecke.Y3Connected
  qmAutCard : HeckeRest.QMAutCard
  alFixedPoints : HeckeRest.ALFixedPoints
  properSmoothGenConnected : FrobPiecesNeron.ProperSmoothGenConnected

theorem textbookLeaves3_of_B2 (t : OpenTextbookLeavesB2) (l : OpenAddedLeavesB2) :
    OpenTextbookLeaves3 where
  t3 := t.t3
  t4 := t.t4
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := AVB2.t9_of_leaves3 l.t09SymmIsogenyExists l.isogenyQuasiInverse
  t10 := t.t10
  homLatticeCorr := t.homLatticeCorr
  t11b := t.t11b
  t23 := t.t23
  t24 := t.t24
  t26 := t.t26
  t27 := t.t27
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  t38 := t.t38
  t40 := t.t40
  t41 := t.t41

theorem addedLeaves3_of_B2 (t : OpenTextbookLeavesB2) (l : OpenAddedLeavesB2) :
    OpenAddedLeaves3 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := l.qmHauptmodul
  qmClassNumberOne := l.qmClassNumberOne
  qmDenZeroCM3 := l.qmDenZeroCM3
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  divisiblePoints := AVB2.divisiblePoints_of_posChar l.mulIsogenyPosChar
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := AVB2.serreRigidity3_of_T35 t.t35 t.homLatticeCorr
  alFixedPoints := l.alFixedPoints
  properSmoothGenConnected := l.properSmoothGenConnected

/-- **`SixContactMin` from 66 named Props** (leaf-fold3's 68 with `t9` and `serreRigidity3`
discharged and `divisiblePoints` replaced by `mulIsogenyPosChar`). -/
theorem sixContactMin_of_openB2 (r : OpenResearchLeaves2) (t : OpenTextbookLeavesB2)
    (l : OpenAddedLeavesB2) (g : OpenGlue3) : _root_.ZInQ.SixContactMin :=
  sixContactMin_of_open3 r (textbookLeaves3_of_B2 t l) (addedLeaves3_of_B2 t l) g

end HSyn

end HDec

#print axioms HDec.AVB2.t9_of_leaves3
#print axioms HDec.AVB2.divisiblePoints_of_posChar
#print axioms HDec.AVB2.serreRigidity3_of_T35
#print axioms HDec.HSyn.sixContactMin_of_openB2
