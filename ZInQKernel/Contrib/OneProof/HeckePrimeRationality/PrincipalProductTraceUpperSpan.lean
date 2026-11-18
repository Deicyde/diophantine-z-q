import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimePrincipalProductTraceSpan
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RepeatedPrimeProductTrace

/-!
# Upper principal-product span preservation by actual trace

Each quotient summand of the actual trace of an admissible product is another
admissible product at the upper level, by integral slash covariance. This
proves upper-span preservation after restriction and does not assert lower
membership or spanning of the whole modular-form space.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalProductTrace

open AllLevelProducts TorsionQuadraticGenerators DivisionEisensteinLevelMaps
open ThetaFiveTorsion (act)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Every actual quotient trace summand is a genuine Good product generator. -/
theorem quotient_product_generator (N M : ℕ) (hM : 0 < M) (v : Fin 2 → ℤ × ℤ)
    (hv : ∀ i, AllLevelForms.Good M (v i))
    (q : (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) :
    ∃ w : Fin 2 → ℤ × ℤ, ∃ hw : ∀ i, AllLevelForms.Good M (w i),
      SlashInvariantForm.quotientFunc (productForm M hM 2 v hv) q = ⇑(productForm M hM 2 w hw) := by
  induction q using QuotientGroup.induction_on' with
  | H g =>
    obtain ⟨γ,hγ,he⟩ := Subgroup.mem_map.mp g.property
    refine ⟨fun i => act (v i) (γ⁻¹), good_act_tuple hv (γ⁻¹), ?_⟩
    rw [SlashInvariantForm.quotientFunc_mk]
    have hginv : g.val⁻¹ = mapGL ℝ (γ⁻¹) := by rw [← he, map_inv]
    rw [hginv]
    exact productForm_slash hM 2 v hv (γ⁻¹)

/-- The restricted trace of every product generator remains in the upper
product span by its genuine finite quotient orbit, not by an assumed closure. -/
theorem restriction_trace_generator_mem_upper {N M : ℕ}
    (hM : 0 < M) (hNM : N ∣ M) (v : Fin 2 → ℤ × ℤ)
    (hv : ∀ i, AllLevelForms.Good M (v i)) :
    restriction N M hNM (normalizedTrace N M hM (productForm M hM 2 v hv)) ∈ productSpan M hM := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  choose w hw hq using (fun q : Q => quotient_product_generator N M hM v hv q)
  have he : restriction N M hNM (normalizedTrace N M hM (productForm M hM 2 v hv)) =
      ((traceIndex N M : ℂ)⁻¹) • ∑ q : Q, productForm M hM 2 (w q) (hw q) := by
    apply DFunLike.coe_injective
    change ⇑(_root_.ModularForm.restrict (principal_group_le hNM)
      (normalizedTrace N M hM (productForm M hM 2 v hv))) = _
    rw [_root_.ModularForm.coe_restrict, normalizedTrace_apply,
      FunLike.coe_smul, _root_.ModularForm.coe_trace, FunLike.coe_smul, FunLike.coe_sum]
    apply congrArg (fun f : ℍ → ℂ => (traceIndex N M : ℂ)⁻¹ • f)
    apply Finset.sum_congr rfl
    intro q _
    exact hq q
  rw [he]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro q _
  exact Submodule.subset_span ⟨w q,hw q,rfl⟩

/-- Actual trace followed by restriction preserves every upper product-span
member. No lower product-span conclusion is used to prove this lemma. -/
theorem restriction_trace_mem_upper {N M : ℕ}
    (hM : 0 < M) (hNM : N ∣ M) {f : _root_.ModularForm (ΓP M) 2}
    (hf : f ∈ productSpan M hM) :
    restriction N M hNM (normalizedTrace N M hM f) ∈ productSpan M hM := by
  let T := (restriction N M hNM).comp (normalizedTrace N M hM)
  have hle : productSpan M hM ≤ (productSpan M hM).comap T := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    exact restriction_trace_generator_mem_upper hM hNM v hv
  exact hle hf

/-- The verified repeated-prime generator theorem extends to every member of
its actual upper degree-two product span by linearity. -/
theorem trace_repeated_prime_span (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hpN : p ∣ N)
    {f : _root_.ModularForm (ΓP (p * N)) 2}
    (hf : f ∈ productSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) f ∈ productSpan N (by omega) := by
  have hle : productSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) ≤
      (productSpan N (by omega)).comap
        (normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))) := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    exact RepeatedPrimeProductTrace.trace_product_mem' p N h3 hpN v hv
  exact hle hf

/-- Actual product-span trace closure across every single prime extension. -/
theorem trace_prime_span (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N)
    {f : _root_.ModularForm (ΓP (p * N)) 2}
    (hf : f ∈ productSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) f ∈ productSpan N (by omega) := by
  rcases Nat.coprime_or_dvd_of_prime (Fact.out : p.Prime) N with hcop | hpN
  · exact CoprimeProductTrace.productSpan_trace_coprime_mem p N h3 hcop hf
  · exact trace_repeated_prime_span p N h3 hpN hf

end ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalProductTrace
