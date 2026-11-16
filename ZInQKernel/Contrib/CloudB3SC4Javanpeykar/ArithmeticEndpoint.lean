import ZInQKernel.OneProof.H.TailY

/-! # Arithmetic endpoint for the Javanpeykar upper bound

This file supplies only definition-level and scalar prerequisites. It does not
prove `ZInQ.HeightSplit.JavanpeykarBound` and adds no assumed published leaves.
The actual curve-theoretic Arakelov inputs remain to be formalized.

The scalar inputs are read from Ariyan Javanpeykar, *Polynomial bounds for
Arakelov invariants of Belyi curves*, Algebra & Number Theory 8:1 (2014):
Theorem 2.4.1, pp. 99-100; Theorem 4.5.2, pp. 122-123; and the use of
Proposition 3.5.1 in the proof of Theorem 1.1.1, Section 4.6, p. 123.
Here `h` and `w` are merely real numbers: this file does not construct the
canonical Arakelov height of a point or the Arakelov norm of its Wronskian.
-/

namespace ZInQ.Contrib.CloudB3SC4Javanpeykar

open NumberField ZInQ.DefFaltings ZInQ.HeightSplit

/-- A real group-model height cannot arise from an empty family of metrizations.
This uses only the actual infimum definition; it assumes no Neron-existence or
analytic-uniformization theorem. -/
theorem exists_metrization_of_real_height
    {K : Type} [Field K] {J : PkgI3.AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    (N : GroupModel J L) {x : ℝ} (hx : N.height = (x : EReal)) :
    ∃ (n : ℕ) (M : MetrizedModel J L n), M.model = N := by
  classical
  by_cases h : ∃ (n : ℕ) (M : MetrizedModel J L n), M.model = N
  · exact h
  · have ht : N.height = ⊤ := by
      apply le_antisymm le_top
      unfold GroupModel.height
      exact le_iInf fun n => le_iInf fun M => le_iInf fun hM =>
        False.elim (h ⟨n, M, hM⟩)
    exact False.elim (EReal.coe_ne_top x (hx.symm.trans ht))

/-- The stable-height hypothesis used in the Javanpeykar statement already
contains a semistable Neron model with at least one genuine metrization. -/
theorem stable_height_has_metrized_neron_model
    {K : Type} [Field K] {J : PkgI3.AbVar K} {x : ℝ}
    (hx : IsStableFaltingsHeight J x) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (N : GroupModel J L),
      N.IsNeronModel ∧ IsSemistable N ∧ N.height = (x : EReal) ∧
        ∃ (n : ℕ) (M : MetrizedModel J L n), M.model = N := by
  obtain ⟨L, hL, hNF, hKL, N, hN, hS, heq⟩ := hx
  exact ⟨L, hL, hNF, hKL, N, hN, hS, heq,
    exists_metrization_of_real_height N heq⟩

/-- A bounded metrization of the same model is sufficient for the upper bound
on its real infimum height. No uniqueness of the metrization is assumed. -/
theorem real_height_le_of_bounded_metrization
    {K : Type} [Field K] {J : PkgI3.AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L]
    (N : GroupModel J L) {n : ℕ} (M : MetrizedModel J L n)
    (hM : M.model = N) {x B : ℝ} (hx : N.height = (x : EReal))
    (hB : M.hodge.modelHeight ≤ B) : x ≤ B := by
  have hinf : N.height ≤ (M.hodge.modelHeight : EReal) := by
    unfold GroupModel.height
    exact iInf_le_of_le n (iInf_le_of_le M (iInf_le_of_le hM le_rfl))
  rw [hx] at hinf
  exact EReal.coe_le_coe_iff.mp (hinf.trans (EReal.coe_le_coe_iff.mpr hB))

/-- Exact scalar combination of the three inequalities used on the published
p. 123. The output constant is 12,756,061, before rounding up to 13 million. -/
theorem printed_constant_combination_sharp
    {g d : ℕ} {h w x : ℝ} (hg : 1 ≤ g)
    (hx : x ≤ ((g : ℝ) * ((g : ℝ) + 1) / 2) * h + w)
    (hh : h ≤ 6378033 * (d : ℝ) ^ 5 / (g : ℝ))
    (hw : w ≤ 6378028 * (g : ℝ) * (d : ℝ) ^ 5) :
    x ≤ 12756061 * (g : ℝ) * (d : ℝ) ^ 5 := by
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < (g : ℝ) := by linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ 5 := by positivity
  have hh' : (g : ℝ) * h ≤ 6378033 * (d : ℝ) ^ 5 := by
    simpa only [mul_comm] using (le_div_iff₀ hg0).mp hh
  have hprod := mul_le_mul_of_nonneg_right hh' (show (0 : ℝ) ≤ (g : ℝ) + 1 by linarith)
  have hdegree : (d : ℝ) ^ 5 ≤ (g : ℝ) * (d : ℝ) ^ 5 :=
    le_mul_of_one_le_left hd0 hg1
  nlinarith

/-- The published scalar combination fits the exact numerical function used
by the repository. This is an arithmetic helper, not a discharge theorem. -/
theorem printed_constant_combination
    {g d : ℕ} {h w x : ℝ} (hg : 1 ≤ g)
    (hx : x ≤ ((g : ℝ) * ((g : ℝ) + 1) / 2) * h + w)
    (hh : h ≤ 6378033 * (d : ℝ) ^ 5 / (g : ℝ))
    (hw : w ≤ 6378028 * (g : ℝ) * (d : ℝ) ^ 5) :
    x ≤ ZInQ.LeafPush2.javanpeykarBound g d := by
  have hs := printed_constant_combination_sharp hg hx hh hw
  have hnonneg : (0 : ℝ) ≤ (g : ℝ) * (d : ℝ) ^ 5 := by positivity
  unfold ZInQ.LeafPush2.javanpeykarBound
  norm_num
  nlinarith

end ZInQ.Contrib.CloudB3SC4Javanpeykar
