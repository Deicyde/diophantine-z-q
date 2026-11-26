import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.LatticeQuotient
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.ChartCoordinates
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.PairCoordinates
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.QuotientInvariant
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

/-! # The pinned pair at a parameter with transcendental j-value

The rational pair reading and the actual Vélu quotient invariant commute with every embedding of
algebraically closed fields. At a parameter τ whose j-value is transcendental, the complex point of
the pinned rational open at τ is the image of a geometric point over the generic j-line under an
embedding of the algebraic closure of `ℚ(j)` sending `j` to `j(τ)`. The descended Vélu invariant
then gives the quotient invariant `j(Nτ)` of the pinned pair, and the actual pair classes agree. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open LeafModCurves ModelGeneric ModelGeneric2 ModelTorsion RC.ModelInvariants UpperHalfPlane
open WeierstrassCurve.Affine
open ZInQ.Manuscript.RC

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

section Naturality

variable {K₁ K₂ : Type} [Field K₁] [Algebra ℚ K₁] [DecidableEq K₁] [IsAlgClosed K₁] [CharZero K₁]
  [Field K₂] [Algebra ℚ K₂] [DecidableEq K₂] [IsAlgClosed K₂] [CharZero K₂]

omit [IsAlgClosed K₂] [CharZero K₁] [CharZero K₂] in
/-- The actual Vélu quotient invariant of a specialized short curve with a marked cyclic subgroup
commutes with an embedding of the specialization fields. -/
private theorem shortQuotientJ_comp (c : ShortBase ℚ →ₐ[ℚ] K₁) (σ : K₁ →ₐ[ℚ] K₂) {x y : K₁}
    (h : ((shortFamily ℚ).map c.toRingHom).toAffine.Nonsingular x y)
    (h' : ((shortFamily ℚ).map (σ.comp c).toRingHom).toAffine.Nonsingular (σ x) (σ y)) (N : ℕ) :
    ((shortFamily ℚ).map (σ.comp c).toRingHom).cyclicQuotientJ
        (AddSubgroup.zmultiples (Point.some (σ x) (σ y) h')) N =
      σ (((shortFamily ℚ).map c.toRingHom).cyclicQuotientJ
        (AddSubgroup.zmultiples (Point.some x y h)) N) := by
  letI : Algebra (ShortBase ℚ) K₁ := c.toRingHom.toAlgebra
  letI : Algebra (ShortBase ℚ) K₂ := (σ.comp c).toRingHom.toAlgebra
  let σ' : K₁ →ₐ[ShortBase ℚ] K₂ := { toRingHom := σ.toRingHom, commutes' := fun _ => rfl }
  have key := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed (shortFamily ℚ) σ'
    (AddSubgroup.zmultiples (Point.some x y h :
      ((shortFamily ℚ).baseChange K₁).toAffine.Point)) N
  rw [AddMonoidHom.map_zmultiples, Point.map_some] at key
  exact key

/-- **Naturality of the pinned pair reading.** The quotient invariant of the rational pair reading
commutes with every embedding of algebraically closed fields of characteristic zero. -/
theorem pairQuotientJ_rationalPoints_comp {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (σ : K₁ →ₐ[ℚ] K₂)
    (y : Y0RationalAlgebra h₂ →ₐ[ℚ] K₁) :
    pairQuotientJ (rationalPoints h₂ (σ.comp y)) = σ (pairQuotientJ (rationalPoints h₂ y)) := by
  obtain _ | _ | n := N
  · omega
  · omega
  let hn := rationalLevel_isUnit (N := n + 2)
  let gr := rationalGrading h₂
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  have hδ : (↑(shortExactOrderDiscriminantUnit (R := ℚ) hn) : rationalCover (n + 2)) ∈
      gr 12 := shortExactOrderDiscriminantUnit_mem (R := ℚ) hn
  obtain ⟨f, rfl⟩ := degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ)
    (k := K₁) gr (by decide) hδ y
  change pairQuotientJ ((rationalPointReading h₂).val ((σ.comp f).comp (Y0RationalInclusion h₂))) =
    σ (pairQuotientJ ((rationalPointReading h₂).val (f.comp (Y0RationalInclusion h₂))))
  rw [(rationalPointReading h₂).property, (rationalPointReading h₂).property, pairQuotientJ_mk,
    pairQuotientJ_mk]
  obtain ⟨hf, hfP⟩ := shortExactOrderPoints_affine hn f
  obtain ⟨hg, hgP⟩ := shortExactOrderPoints_affine hn (σ.comp f)
  change ((shortFamily ℚ).map (shortExactOrderPoints hn (σ.comp f)).1.toRingHom).cyclicQuotientJ
      (AddSubgroup.zmultiples (shortExactOrderPoints hn (σ.comp f)).2.1) (n + 2) =
    σ (((shortFamily ℚ).map (shortExactOrderPoints hn f).1.toRingHom).cyclicQuotientJ
      (AddSubgroup.zmultiples (shortExactOrderPoints hn f).2.1) (n + 2))
  rw [hgP, hfP]
  exact shortQuotientJ_comp (shortExactOrderPoints hn f).1 σ hf hg (n + 2)

end Naturality

open Polynomial in
/-- **Specialization at a transcendental j-value.** At a complex point of the pinned rational
quotient whose j-value is transcendental, the actual quotient invariant of the pinned pair equals
the value of the regular Vélu coordinate. The point factors through the generic j-fibre by an
embedding of the algebraic closure of `ℚ(j)` sending `j` to that value. -/
theorem pairQuotientJ_rationalPoints_of_transcendental {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)
    (x : Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ) (ht : Transcendental ℚ (x (Y0RationalJ h₂))) :
    pairQuotientJ (rationalPoints h₂ x) = x (rationalQuotientCoordinate h₂).val := by
  let t := x (Y0RationalJ h₂)
  have hinj : Function.Injective (Polynomial.aeval (R := ℚ) t) := transcendental_iff_injective.mp ht
  let ι : Qj →+* ℂ := IsFractionRing.lift (A := Polynomial ℚ) (K := Qj)
    (g := (Polynomial.aeval (R := ℚ) t).toRingHom) hinj
  letI : Algebra Qj ℂ := ι.toAlgebra
  haveI : Module.IsTorsionFree Qj ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr ι.injective
  haveI : Module.IsTorsionFree Qj Kbar :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap Qj Kbar).injective
  let σ : Kbar →ₐ[Qj] ℂ := IsAlgClosed.lift
  let P := Polynomial ℚ
  let B := Y0RationalAlgebra h₂
  letI : Algebra P B := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Algebra P ℂ := (ι.comp (algebraMap P Qj)).toAlgebra
  haveI : IsScalarTower P Qj ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hιP : ∀ p : P, ι (algebraMap P Qj p) = Polynomial.aeval t p := fun p =>
    IsFractionRing.lift_algebraMap hinj p
  let xP : B →ₐ[P] ℂ :=
    { x.toRingHom with
      commutes' := fun p => by
        change x (Polynomial.aeval (Y0RationalJ h₂) p) = ι (algebraMap P Qj p)
        rw [hιP, Polynomial.aeval_algHom_apply] }
  let x' : Y0RationalGenericJ h₂ →ₐ[Qj] ℂ := AlgHom.liftEquiv P Qj B ℂ xP
  have hx' : ∀ b, x' (Y0RationalGenericJInclusion h₂ b) = x b := fun b => by
    change (AlgHom.liftEquiv P Qj B ℂ xP) (1 ⊗ₜ b) = x b
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl
  have hfac : ∀ z : Y0RationalGenericJ h₂, x' z ∈ σ.range := by
    intro z
    haveI := Y0RationalGenericJ_finite h₂
    have hint : _root_.IsIntegral Qj z :=
      (Algebra.IsIntegral.of_finite Qj (Y0RationalGenericJ h₂)).isIntegral z
    let p := minpoly Qj z
    have hp0 : p ≠ 0 := minpoly.ne_zero hint
    have hroot : (p.map ι).IsRoot (x' z) := by
      rw [IsRoot, eval_map]
      change aeval (x' z) p = 0
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    let q := p.map (algebraMap Qj Kbar)
    have hcard : q.roots.card = q.natDegree := IsAlgClosed.card_roots_eq_natDegree
    have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
      (f := σ.toRingHom) σ.toRingHom.injective hcard
    have hq : q.map σ.toRingHom = p.map ι := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext fun c => σ.commutes c
    have hmem : x' z ∈ (p.map ι).roots :=
      (mem_roots ((Polynomial.map_ne_zero_iff ι.injective).mpr hp0)).mpr hroot
    rw [← hq, ← hmap, Multiset.mem_map] at hmem
    obtain ⟨r, -, hr⟩ := hmem
    exact ⟨r, hr⟩
  let e := AlgEquiv.ofInjective σ σ.toRingHom.injective
  let x'' : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar := e.symm.toAlgHom.comp (x'.codRestrict σ.range hfac)
  have hσx'' : ∀ z, σ (x'' z) = x' z := fun z => by
    have h := congrArg Subtype.val (e.apply_symm_apply (x'.codRestrict σ.range hfac z))
    rw [AlgEquiv.ofInjective_apply] at h
    exact h
  let σℚ : Kbar →ₐ[ℚ] ℂ :=
    { σ.toRingHom with
      commutes' := fun q => RingHom.congr_fun
        (Subsingleton.elim (σ.toRingHom.comp (algebraMap ℚ Kbar)) (algebraMap ℚ ℂ)) q }
  let y := (genericJPointsOnRational h₂ x'').val
  have hy : σℚ.comp y = x := by
    ext b
    change σ ((genericJPointsOnRational h₂ x'').val b) = x b
    rw [genericJPointsOnRational_apply, hσx'', hx']
  rw [← hy, pairQuotientJ_rationalPoints_comp h₂ σℚ y, ← genericQuotientValue_pairClass,
    ← Y0RationalGenericQuotientJ_eval]
  change σ (x'' (Y0RationalGenericQuotientJ h₂)) = σ (y (rationalQuotientCoordinate h₂).val)
  rw [show y (rationalQuotientCoordinate h₂).val =
      x'' (Y0RationalGenericJInclusion h₂ (rationalQuotientCoordinate h₂).val) from
    genericJPointsOnRational_apply h₂ x'' _, (rationalQuotientCoordinate h₂).property]

/-- **The pair class at a parameter with transcendental j-value.** -/
theorem rationalPoints_rationalPointAtParameter_of_transcendental {N : ℕ} [NeZero N]
    (h₂ : 2 ≤ N) (τ : ℍ) (ht : Transcendental ℚ (X0Model.analyticJ τ)) :
    rationalPoints h₂ (ModelGeneric3.rationalPointAtParameter h₂ τ) =
      ModelGeneric3.analyticCyclicPair (N := N) τ := by
  have hj : ModelGeneric3.rationalPointAtParameter h₂ τ (Y0RationalJ h₂) = X0Model.analyticJ τ := by
    rw [← rationalPoints_j, ModelGeneric3.rationalPointAtParameter_pairJ]
  apply ModelGeneric3.complexPairClass_eq_of_transcendental_coordinates
  · rw [ModelGeneric3.rationalPointAtParameter_pairJ]; exact ht
  · rw [ModelGeneric3.rationalPointAtParameter_pairJ, ModelGeneric3.analyticCyclicPair_j]
  · rw [pairQuotientJ_rationalPoints_of_transcendental h₂ _ (hj ▸ ht),
      ModelGeneric3.rationalPointAtParameter_quotientCoordinate, pairQuotientJ_analyticCyclicPair]

#print axioms pairQuotientJ_rationalPoints_comp
#print axioms pairQuotientJ_rationalPoints_of_transcendental
#print axioms rationalPoints_rationalPointAtParameter_of_transcendental

end WeierstrassCurve.ModelLevels.ModelGeneric4
