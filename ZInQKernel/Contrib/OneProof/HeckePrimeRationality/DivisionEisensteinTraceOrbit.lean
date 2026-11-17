import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTracePartial

/-!
# Finite trace orbits of genuine division Eisenstein series

The restriction of a trace to its upper level is a finite sum of actual series
generators. This proves preservation of the upper series span under the trace
projector. It does not identify the resulting lower form with the lower series
span; that genuinely downward statement requires a separate orbit reduction.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators Matrix MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLevelMaps

open EisensteinWeightTwo

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Every quotient summand of the trace of a series generator is the underlying
function of an actual upper-level series generator. -/
theorem quotient_summand_generator {N M : ℕ} (hM : 0 < M)
    (a : Fin 2 → ℤ) (q : (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) :
    ∃ b : Fin 2 → ℤ, SlashInvariantForm.quotientFunc (divisionEisensteinMF M hM a) q =
      ⇑(divisionEisensteinMF M hM b) := by
  induction q using QuotientGroup.induction_on' with
  | H g =>
    obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp g.property
    refine ⟨a ᵥ* (γ⁻¹).1, ?_⟩
    rw [SlashInvariantForm.quotientFunc_mk]
    have hginv : g.val⁻¹ = mapGL ℝ (γ⁻¹) := by
      rw [← he, map_inv]
    rw [hginv]
    change (fun τ : ℍ => divisionEisenstein M (a 0) (a 1) τ) ∣[(2 : ℤ)] mapGL ℝ (γ⁻¹) =
      (fun τ : ℍ => divisionEisenstein M ((a ᵥ* (γ⁻¹).1) 0) ((a ᵥ* (γ⁻¹).1) 1) τ)
    exact divisionEisenstein_slash M hM a (γ⁻¹)

/-- A traced series generator is an explicit finite orbit sum when restricted
back to its upper level. This statement has no lower-span conclusion. -/
theorem restriction_trace_generator_orbit {N M : ℕ} [NeZero M] (hM : 0 < M) (hNM : N ∣ M)
    (a : Fin 2 → ℤ) :
    ∃ B : ((ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) → (Fin 2 → ℤ),
      restriction N M hNM (normalizedTrace N M hM (divisionEisensteinMF M hM a)) =
        ((traceIndex N M : ℂ)⁻¹) •
          (let _ := Fintype.ofFinite ((ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N));
            ∑ q, divisionEisensteinMF M hM (B q)) := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  choose B hB using (fun q : Q => quotient_summand_generator hM a q)
  refine ⟨B, ?_⟩
  apply DFunLike.coe_injective
  change ⇑(_root_.ModularForm.restrict (principal_group_le hNM)
    (normalizedTrace N M hM (divisionEisensteinMF M hM a))) = _
  rw [_root_.ModularForm.coe_restrict, normalizedTrace_apply N M hM,
    FunLike.coe_smul, _root_.ModularForm.coe_trace, FunLike.coe_smul, FunLike.coe_sum]
  apply congrArg (fun f : ℍ → ℂ => (traceIndex N M : ℂ)⁻¹ • f)
  apply Finset.sum_congr rfl
  intro q _
  exact hB q

/-- The restricted trace of every genuine series generator belongs to the
upper-level series span. -/
theorem restriction_trace_generator_mem_upper {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M)
    (a : Fin 2 → ℤ) :
    restriction N M hNM (normalizedTrace N M hM (divisionEisensteinMF M hM a)) ∈ seriesSpan M hM := by
  let : NeZero M := ⟨hM.ne'⟩
  obtain ⟨B, he⟩ := restriction_trace_generator_orbit hM hNM a
  rw [he]
  apply Submodule.smul_mem
  let : Fintype ((ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) := Fintype.ofFinite _
  apply Submodule.sum_mem
  intro q _
  exact generator_mem_seriesSpan M hM (B q)

/-- The actual trace projector preserves the upper series span after restriction.
No arbitrary lower series-span descent is asserted. -/
theorem restriction_trace_mem_upper_seriesSpan {N M : ℕ}
    (hM : 0 < M) (hNM : N ∣ M) {f : _root_.ModularForm (ΓP M) 2}
    (hf : f ∈ seriesSpan M hM) :
    restriction N M hNM (normalizedTrace N M hM f) ∈ seriesSpan M hM := by
  let T := (restriction N M hNM).comp (normalizedTrace N M hM)
  have hle : seriesSpan M hM ≤ (seriesSpan M hM).comap T := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, rfl⟩
    exact restriction_trace_generator_mem_upper hM hNM a
  exact hle hf

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLevelMaps
