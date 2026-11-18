import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightSeriesDistribution
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTraceInvariance

/-!
# Variable-weight trace covariance and invariant modular descent

Right multiplication permutes the genuine principal trace quotient. The
all-weight class-series covariance then gives trace constancy on integral
principal-group label moves. No lower series-span preservation is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
open DivisionEisensteinLevelMaps (principal_group_le)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

theorem normalizedTraceK_series_SL (N M : ℕ) (hM3 : 3 ≤ M) (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) :
    normalizedTraceK N M k (by omega) (seriesForm M hM3 k hk (a ᵥ* γ.1)) =
      normalizedTraceK N M k (by omega) (seriesForm M hM3 k hk a) := by
  classical
  let : NeZero M := ⟨by omega⟩
  let _ := DivisionEisensteinLowerClosure.mapped_principal_subgroup_normal N M
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  let g : (ΓP N) := ⟨mapGL ℝ γ,Subgroup.mem_map.mpr ⟨γ,hγ,rfl⟩⟩
  have hs : ⇑(seriesForm M hM3 k hk (a ᵥ* γ.1)) =
      (⇑(seriesForm M hM3 k hk a) : ℍ → ℂ) ∣[(k : ℤ)] mapGL ℝ γ :=
    (seriesForm_slash M hM3 k hk a γ).symm
  have he (q : Q) : SlashInvariantForm.quotientFunc (seriesForm M hM3 k hk (a ᵥ* γ.1)) q =
      SlashInvariantForm.quotientFunc (seriesForm M hM3 k hk a) (MulOpposite.op g⁻¹ • q) := by
    induction q using QuotientGroup.induction_on' with
    | H r =>
      rw [MulAction.Quotient.smul_coe, SlashInvariantForm.quotientFunc_mk,
        SlashInvariantForm.quotientFunc_mk,hs,← SlashAction.slash_mul]
      simp only [MulOpposite.smul_eq_mul_unop,MulOpposite.unop_op,Subgroup.coe_mul,
        Subgroup.coe_inv,_root_.mul_inv_rev,inv_inv,g]
  rw [normalizedTraceK_apply,normalizedTraceK_apply]
  apply congrArg (fun F : _root_.ModularForm (ΓP N) (k : ℤ) =>
    (DivisionEisensteinLevelMaps.traceIndex N M : ℂ)⁻¹ • F)
  apply DFunLike.coe_injective
  rw [_root_.ModularForm.coe_trace,_root_.ModularForm.coe_trace]
  simp_rw [he]
  exact Equiv.sum_comp (MulAction.toPerm (MulOpposite.op g⁻¹))
    (SlashInvariantForm.quotientFunc (seriesForm M hM3 k hk a))

/-- A genuinely invariant upper form descends as a modular form at weight k. -/
theorem actual_descentK {N M k : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    (f : _root_.ModularForm (ΓP M) (k : ℤ))
    (hf : ∀ γ ∈ (ΓP N), ⇑f ∣[(k : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm (ΓP N) (k : ℤ), restrictionK N M k hNM g = f := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero M := ⟨hM.ne'⟩
  have hc : ∀ c, IsCusp c (ΓP N) → IsCusp c (ΓP M) := Subgroup.IsArithmetic.isCusp_of_isCusp
  exact (_root_.ModularForm.mem_range_restrictₗ_iff (principal_group_le hNM) hc f).mpr hf

theorem restrictionK_trace_invariant {N M k : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    (f : _root_.ModularForm (ΓP M) (k : ℤ))
    (hf : ∀ γ ∈ (ΓP N), ⇑f ∣[(k : ℤ)] γ = ⇑f) :
    restrictionK N M k hNM (normalizedTraceK N M k hM f) = f := by
  obtain ⟨g,rfl⟩ := actual_descentK hN hM hNM f hf
  rw [normalizedTraceK_restriction hM hNM g]

/-- Actual upper-span preservation, separately proved by the quotient summands. -/
theorem restrictionK_trace_mem_upper {N M k : ℕ} (hN3 : 3 ≤ N) (hM3 : 3 ≤ M)
    (hk : 3 ≤ k) (hNM : N ∣ M) {f : _root_.ModularForm (ΓP M) (k : ℤ)}
    (hf : f ∈ seriesSpanK M hM3 k hk) :
    restrictionK N M k hNM (normalizedTraceK N M k (by omega) f) ∈ seriesSpanK M hM3 k hk := by
  classical
  let : NeZero M := ⟨by omega⟩
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  have hgen (a : Fin 2 → ℤ) :
      restrictionK N M k hNM (normalizedTraceK N M k (by omega) (seriesForm M hM3 k hk a)) ∈
        seriesSpanK M hM3 k hk := by
    have hq (q : Q) : ∃ b : Fin 2 → ℤ,
        SlashInvariantForm.quotientFunc (seriesForm M hM3 k hk a) q = ⇑(seriesForm M hM3 k hk b) := by
      induction q using QuotientGroup.induction_on' with
      | H g =>
        obtain ⟨γ,hγ,he⟩ := Subgroup.mem_map.mp g.property
        refine ⟨a ᵥ* (γ⁻¹).1,?_⟩
        rw [SlashInvariantForm.quotientFunc_mk]
        have hg : g.val⁻¹ = mapGL ℝ (γ⁻¹) := by rw [← he,map_inv]
        rw [hg]
        exact seriesForm_slash M hM3 k hk a (γ⁻¹)
    choose b hb using hq
    have he : restrictionK N M k hNM (normalizedTraceK N M k (by omega) (seriesForm M hM3 k hk a)) =
        ((DivisionEisensteinLevelMaps.traceIndex N M : ℂ)⁻¹) • ∑ q : Q, seriesForm M hM3 k hk (b q) := by
      apply DFunLike.coe_injective
      change ⇑(_root_.ModularForm.restrict (principal_group_le hNM)
        (normalizedTraceK N M k (by omega) (seriesForm M hM3 k hk a))) = _
      rw [_root_.ModularForm.coe_restrict,normalizedTraceK_apply,FunLike.coe_smul,
        _root_.ModularForm.coe_trace,FunLike.coe_smul,FunLike.coe_sum]
      apply congrArg (fun F : ℍ → ℂ => (DivisionEisensteinLevelMaps.traceIndex N M : ℂ)⁻¹ • F)
      apply Finset.sum_congr rfl
      intro q _
      exact hb q
    rw [he]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro q _
    exact generator_mem_seriesSpanK M hM3 k hk (b q)
  let T := (restrictionK N M k hNM).comp (normalizedTraceK N M k (by omega))
  have hle : seriesSpanK M hM3 k hk ≤ (seriesSpanK M hM3 k hk).comap T := by
    apply Submodule.span_le.mpr
    rintro F ⟨a,rfl⟩
    exact hgen a
  exact hle hf

end ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
