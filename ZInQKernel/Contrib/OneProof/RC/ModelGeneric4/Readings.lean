import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.Surjectivity

/-! # The actual pair-class readings on both generic models and their comparison

Level side: a complex point of the pinned rational quotient `Y0Rational h₂` is a ring map from its
coordinate ring; its reading is the actual class `rationalPoints h₂` (the reading of the pinned
level points). Branch side: a complex point of the finite chart of `X0Branch.model N` is the analytic
point of a parameter τ (item 2); its reading is the class of `(ℂ/(ℤτ + ℤ), ⟨1/N⟩)`, which does not
depend on the chosen parameter. The two readings agree along `rationalOpenIsoOverQ h₂`. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open AlgebraicGeometry CategoryTheory ModelGeneric ModelGeneric2 UpperHalfPlane
open ZInQ.Manuscript.RC

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The coordinate-ring map of a complex point of the pinned rational quotient. -/
noncomputable def levelPoint (x : RationalCurveComplexPoints (Y0Rational h₂)) :
    Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ :=
  (Spec.preimage x.left).hom.toRatAlgHom

/-- **Level-side pair reading.** The actual class of the pinned rational quotient at a complex
point: the reading `rationalPoints h₂` (which is the reading of the pinned level points after
every detector base change, `detectorFibrePoints_eq_rationalPoints`). -/
noncomputable def levelPairClass (x : RationalCurveComplexPoints (Y0Rational h₂)) :
    PairClasses ℂ N :=
  rationalPoints h₂ (levelPoint h₂ x)

/-- A parameter of a complex point of the finite chart (item 2). -/
noncomputable def branchParameter (y : RationalCurveComplexPoints (branchFiniteOverQ N)) : ℍ :=
  (exists_complexPoint_eq h₂ y).choose

theorem branchParameter_spec (y : RationalCurveComplexPoints (branchFiniteOverQ N)) :
    y.left ≫ (X0Model3.finiteChart N).ι = X0Model.complexPoint N (branchParameter h₂ y) :=
  (exists_complexPoint_eq h₂ y).choose_spec

/-- **Branch-side pair reading.** The class of `(ℂ/(ℤτ + ℤ), ⟨1/N⟩)` for a parameter τ of the
complex point. -/
noncomputable def branchPairClass (y : RationalCurveComplexPoints (branchFiniteOverQ N)) :
    PairClasses ℂ N :=
  ModelGeneric3.analyticCyclicPair (N := N) (branchParameter h₂ y)

/-- A complex point of the pinned quotient whose image in the compact curve is the analytic point
of τ is the inverse evaluation at τ. -/
theorem levelPoint_eq_of_openImmersion (x : RationalCurveComplexPoints (Y0Rational h₂)) (τ : ℍ)
    (hx : x.left ≫ rationalOpenImmersion h₂ = X0Model.complexPoint N τ) :
    levelPoint h₂ x = ModelGeneric3.rationalPointAtParameter h₂ τ := by
  haveI := rationalOpenImmersion_isOpen h₂
  rw [← ModelGeneric3.rationalPointAtParameter_openImmersion h₂ τ] at hx
  have hx' := (cancel_mono (rationalOpenImmersion h₂)).mp hx
  have hpre : Spec.preimage x.left =
      CommRingCat.ofHom (ModelGeneric3.rationalPointAtParameter h₂ τ).toRingHom := by
    rw [hx', Spec.preimage_map]
  ext a
  change (Spec.preimage x.left).hom a = _
  rw [hpre]
  rfl

/-- The branch reading does not depend on the chosen parameter. -/
theorem branchPairClass_eq (y : RationalCurveComplexPoints (branchFiniteOverQ N)) (τ : ℍ)
    (hτ : y.left ≫ (X0Model3.finiteChart N).ι = X0Model.complexPoint N τ) :
    branchPairClass h₂ y = ModelGeneric3.analyticCyclicPair (N := N) τ := by
  let x := y ≫ (rationalOpenIsoOverQ h₂).inv
  have hy : y = x ≫ (rationalOpenIsoOverQ h₂).hom := by simp [x]
  have himm (σ : ℍ) (h : y.left ≫ (X0Model3.finiteChart N).ι = X0Model.complexPoint N σ) :
      x.left ≫ rationalOpenImmersion h₂ = X0Model.complexPoint N σ := by
    rw [← h, hy, Over.comp_left, Category.assoc, ← rationalOpenIso_hom_comp h₂]
    rfl
  have h1 := levelPoint_eq_of_openImmersion h₂ x _ (himm _ (branchParameter_spec h₂ y))
  have h2 := levelPoint_eq_of_openImmersion h₂ x τ (himm τ hτ)
  rw [branchPairClass, ← rationalPoints_rationalPointAtParameter h₂, ← h1, h2,
    rationalPoints_rationalPointAtParameter h₂]

/-- **The pair-class conjunct** of `GenericFibreComparison` for `e = rationalOpenIsoOverQ h₂`,
with the actual readings on both sides. -/
theorem pairClass_conjunct (x : RationalCurveComplexPoints (Y0Rational h₂)) :
    branchPairClass h₂ (x ≫ (rationalOpenIsoOverQ h₂).hom) = levelPairClass h₂ x := by
  let τ := branchParameter h₂ (x ≫ (rationalOpenIsoOverQ h₂).hom)
  have hτ := branchParameter_spec h₂ (x ≫ (rationalOpenIsoOverQ h₂).hom)
  have hx : x.left ≫ rationalOpenImmersion h₂ = X0Model.complexPoint N τ := by
    rw [← hτ, Over.comp_left, Category.assoc, ← rationalOpenIso_hom_comp h₂]
    rfl
  rw [levelPairClass, levelPoint_eq_of_openImmersion h₂ x τ hx,
    rationalPoints_rationalPointAtParameter h₂]
  rfl

#print axioms levelPairClass
#print axioms branchPairClass
#print axioms levelPoint_eq_of_openImmersion
#print axioms branchPairClass_eq
#print axioms pairClass_conjunct

end WeierstrassCurve.ModelLevels.ModelGeneric4
