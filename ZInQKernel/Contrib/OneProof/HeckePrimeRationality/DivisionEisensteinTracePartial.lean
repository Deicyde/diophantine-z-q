import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinLevelMaps

/-!
# Normalized trace on upward division-Eisenstein images

The trace is the actual finite-index modular-form trace, not a new Eisenstein
projection. It is a left inverse to level restriction and therefore descends
scaled series generators and upward series-span images. Arbitrary upper-level
series-span invariants are not identified with lower-level series-span elements
by this result.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLevelMaps

open EisensteinWeightTwo

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The actual trace index for the mapped principal congruence groups. -/
def traceIndex (N M : ℕ) : ℕ := (ΓP M).relIndex (ΓP N)

/-- Positivity of the finite trace index is proved, not a normalization premise. -/
theorem traceIndex_ne_zero (N M : ℕ) (hM : 0 < M) : traceIndex N M ≠ 0 := by
  let : NeZero M := ⟨hM.ne'⟩
  exact Subgroup.relIndex_ne_zero

/-- The normalized actual finite Γ(N)/Γ(M) trace, on all actual modular forms. -/
def normalizedTrace (N M : ℕ) (hM : 0 < M) :
    _root_.ModularForm (ΓP M) 2 →ₗ[ℂ] _root_.ModularForm (ΓP N) 2 := by
  let : NeZero M := ⟨hM.ne'⟩
  exact ((traceIndex N M : ℂ)⁻¹) • _root_.ModularForm.traceₗ (ΓP N)

/-- Literal comparison with the established trace constructor. -/
theorem normalizedTrace_apply (N M : ℕ) [NeZero M] (hM : 0 < M)
    (f : _root_.ModularForm (ΓP M) 2) :
    normalizedTrace N M hM f = ((traceIndex N M : ℂ)⁻¹) • _root_.ModularForm.trace (ΓP N) f := by
  let : NeZero M := ⟨hM.ne'⟩
  rfl

/-- The normalized trace is a left inverse to actual divisible-level restriction. -/
theorem normalizedTrace_restriction {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M)
    (f : _root_.ModularForm (ΓP N) 2) :
    normalizedTrace N M hM (restriction N M hNM f) = f := by
  let : NeZero M := ⟨hM.ne'⟩
  have hidx : (traceIndex N M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (traceIndex_ne_zero N M hM)
  change (traceIndex N M : ℂ)⁻¹ •
    _root_.ModularForm.traceₗ (ΓP N) (_root_.ModularForm.restrict (principal_group_le hNM) f) = f
  rw [_root_.ModularForm.traceₗ_restrict]
  change (traceIndex N M : ℂ)⁻¹ • ((traceIndex N M : ℂ) • f) = f
  rw [smul_smul, inv_mul_cancel₀ hidx, one_smul]

/-- Tracing an upward image of a genuine series-span member returns that member. -/
theorem normalizedTrace_upward_seriesSpan {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    {f : _root_.ModularForm (ΓP N) 2} (hf : f ∈ seriesSpan N hN) :
    normalizedTrace N M hM (restriction N M hNM f) ∈ seriesSpan N hN := by
  rw [normalizedTrace_restriction hM hNM f]
  exact hf

/-- The actual trace sends a scaled upper series generator to the lower series generator. -/
theorem normalizedTrace_scaled_generator {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M) (a : Fin 2 → ℤ) :
    normalizedTrace N M hM (divisionEisensteinMF M hM (fun i => ((M / N : ℕ) : ℤ) * a i)) =
      divisionEisensteinMF N hN a := by
  rw [← restriction_generator hN hM hNM a, normalizedTrace_restriction hM hNM]

/-- Genuine downward series-span closure for the scaled-generator subspace only. -/
theorem normalizedTrace_mem_lower_of_scaled_span {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    {f : _root_.ModularForm (ΓP M) 2}
    (hf : f ∈ Submodule.span ℂ (Set.range (fun a : Fin 2 → ℤ =>
      divisionEisensteinMF M hM (fun i => ((M / N : ℕ) : ℤ) * a i)))) :
    normalizedTrace N M hM f ∈ seriesSpan N hN := by
  have hle : Submodule.span ℂ (Set.range (fun a : Fin 2 → ℤ =>
      divisionEisensteinMF M hM (fun i => ((M / N : ℕ) : ℤ) * a i))) ≤
      (seriesSpan N hN).comap (normalizedTrace N M hM) := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, rfl⟩
    change normalizedTrace N M hM (divisionEisensteinMF M hM
      (fun i => ((M / N : ℕ) : ℤ) * a i)) ∈ seriesSpan N hN
    rw [normalizedTrace_scaled_generator hN hM hNM a]
    exact generator_mem_seriesSpan N hN a
  exact hle hf

/-- Any genuinely invariant upper-level form descends as an actual modular
form. This conclusion intentionally says nothing about the lower series span. -/
theorem actual_form_descent_of_invariant {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    (f : _root_.ModularForm (ΓP M) 2)
    (hf : ∀ γ ∈ (ΓP N), ⇑f ∣[(2 : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm (ΓP N) 2, restriction N M hNM g = f := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hc : ∀ c, IsCusp c (ΓP N) → IsCusp c (ΓP M) :=
    Subgroup.IsArithmetic.isCusp_of_isCusp
  exact (_root_.ModularForm.mem_range_restrictₗ_iff
    (principal_group_le hNM) hc f).mpr hf

/-- An invariant upper-level form is recovered by restriction of the normalized
trace, without identifying its lower form as an Eisenstein-span member. -/
theorem restriction_normalizedTrace_of_invariant {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    (f : _root_.ModularForm (ΓP M) 2)
    (hf : ∀ γ ∈ (ΓP N), ⇑f ∣[(2 : ℤ)] γ = ⇑f) :
    restriction N M hNM (normalizedTrace N M hM f) = f := by
  obtain ⟨g, rfl⟩ := actual_form_descent_of_invariant hN hM hNM f hf
  rw [normalizedTrace_restriction hM hNM g]

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLevelMaps
