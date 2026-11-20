import ZInQKernel.Contrib.OneProof.RC.EvenJoin.Scoped
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-! The local coefficient compositum is separate from the cut-out number
fields. Its norm extends the one chosen at the base coefficient place. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget IsDedekindDomain NumberField Wiring
open ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53
open scoped NNReal WithZero

private def valuationAbsoluteValue {K : Type*} [Field K] (w : Valuation K ℝ≥0) :
    AbsoluteValue K ℝ where
  toFun x := w x
  map_mul' x y := by simp
  nonneg' x := (w x).coe_nonneg
  eq_zero' x := by simp
  add_le' x y := by
    have h := w.map_add x y
    exact_mod_cast h.trans (max_le_add_of_nonneg (zero_le : 0 ≤ w x) (zero_le : 0 ≤ w y))

private theorem spectralNorm_eq_valuation_of_algHom
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
    {K M : Type*} [Field K] [Field M] [Algebra k K] [Algebra k M]
    [FiniteDimensional k K] (j : K →ₐ[k] M) (w : Valuation K ℝ≥0)
    (hw : ∀ x : k, w (algebraMap k K x) = ‖x‖₊) (x : K) :
    spectralNorm k M (j x) = (w x : ℝ) := by
  let : Algebra K M := j.toRingHom.toAlgebra
  have : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  change spectralNorm k M (algebraMap K M x) = valuationAbsoluteValue w x
  rw [← spectralNorm.eq_of_tower (K := k) (L := M) x]
  exact (spectralNorm_unique_field_norm_ext (f := valuationAbsoluteValue w)
    (fun y => congrArg NNReal.toReal (hw y)) x).symm

/-- Embed two finite extensions of the fixed complete field into their
compositum in an algebraic closure. Its spectral norm restricts to the
specified normalized valuations on both extensions. -/
theorem finite_valued_compositum
    (k : Type*) [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra k K₁] [Algebra k K₂]
    [FiniteDimensional k K₁] [FiniteDimensional k K₂]
    (w₁ : Valuation K₁ ℝ≥0) (w₂ : Valuation K₂ ℝ≥0)
    (h₁ : ∀ x : k, w₁ (algebraMap k K₁ x) = ‖x‖₊)
    (h₂ : ∀ x : k, w₂ (algebraMap k K₂ x) = ‖x‖₊) :
    ∃ M : IntermediateField k (AlgebraicClosure k), FiniteDimensional k M ∧
      ∃ (j₁ : K₁ →ₐ[k] M) (j₂ : K₂ →ₐ[k] M),
        (∀ x, spectralNorm k M (j₁ x) = (w₁ x : ℝ)) ∧
        (∀ x, spectralNorm k M (j₂ x) = (w₂ x : ℝ)) := by
  let f₁ : K₁ →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let f₂ : K₂ →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  have : FiniteDimensional k f₁.fieldRange := FiniteDimensional.of_surjective
    f₁.equivFieldRange.toLinearMap f₁.equivFieldRange.surjective
  have : FiniteDimensional k f₂.fieldRange := FiniteDimensional.of_surjective
    f₂.equivFieldRange.toLinearMap f₂.equivFieldRange.surjective
  let M := f₁.fieldRange ⊔ f₂.fieldRange
  have : FiniteDimensional k M := by
    change FiniteDimensional k (↑(f₁.fieldRange ⊔ f₂.fieldRange) : Type _)
    infer_instance
  let j₁ : K₁ →ₐ[k] M :=
    (IntermediateField.inclusion le_sup_left).comp f₁.rangeRestrict
  let j₂ : K₂ →ₐ[k] M :=
    (IntermediateField.inclusion le_sup_right).comp f₂.rangeRestrict
  exact ⟨M, inferInstance, j₁, j₂, spectralNorm_eq_valuation_of_algHom j₁ w₁ h₁,
    spectralNorm_eq_valuation_of_algHom j₂ w₂ h₂⟩

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {B : ℕ} [NeZero (conductor W.S)]
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

/-- The two actual model fields embed over the fixed place, with their
chosen valuations preserved. No scalar extension of a form is needed. -/
theorem fixed_place_joint_extension {X Y : Model P hS B}
    (E : FixedPlaceExtension v X) (E' : FixedPlaceExtension v Y) :
    letI := E.fieldMap.toAlgebra
    letI := E'.fieldMap.toAlgebra
    ∃ M : IntermediateField (FixedField v) (AlgebraicClosure (FixedField v)),
      FiniteDimensional (FixedField v) M ∧
      ∃ (j : X.K →ₐ[FixedField v] M) (j' : Y.K →ₐ[FixedField v] M),
        (∀ x, spectralNorm (FixedField v) M (j x) = (E.val x : ℝ)) ∧
        (∀ x, spectralNorm (FixedField v) M (j' x) = (E'.val x : ℝ)) := by
  let := E.fieldMap.toAlgebra
  let := E'.fieldMap.toAlgebra
  have := E.finite
  have := E'.finite
  let : NontriviallyNormedField (FixedField v) := Valued.toNontriviallyNormedField _ ℤᵐ⁰
  exact finite_valued_compositum (FixedField v) X.K Y.K E.val E'.val E.normalized E'.normalized

end ZInQ.Manuscript.RC.EvenJoin
