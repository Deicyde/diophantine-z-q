import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrincipalProductTraceUpperSpan

/-!
# Arbitrary divisible-level degree-two principal-product trace closure

Prime product-span trace closure and actual upper-span preservation imply
invariant product-span descent by strong induction on the upper level. Applied
to the restricted actual trace, that descent proves lower membership without
assuming trace transitivity or a full modular-form spanning theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalProductTrace

open TorsionQuadraticGenerators AllLevelProducts DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- An invariant actual upper product-span member descends across one prime
to an already proved member of the lower Good degree-two product span. -/
theorem invariant_product_descent_prime (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N)
    (f : _root_.ModularForm (ΓP (p * N)) 2)
    (hf : f ∈ productSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)))
    (hinv : ∀ γ ∈ (ΓP N), ⇑f ∣[(2 : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm (ΓP N) 2, g ∈ productSpan N (by omega) ∧
      restriction N (p * N) (dvd_mul_left N p) g = f := by
  exact ⟨normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) f,
    trace_prime_span p N h3 hf,
    restriction_normalizedTrace_of_invariant (by omega)
      (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) (dvd_mul_left N p) f hinv⟩

/-- Invariant product-span descent at every positive divisible level. The
lower form and its product-span membership are constructed before any use
of restriction injectivity. -/
theorem invariant_product_descent (M : ℕ) :
    ∀ (N : ℕ) (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
      (f : _root_.ModularForm (ΓP M) 2), f ∈ productSpan M hM →
      (∀ γ ∈ (ΓP N), ⇑f ∣[(2 : ℤ)] γ = ⇑f) →
      ∃ g : _root_.ModularForm (ΓP N) 2, g ∈ productSpan N (by omega) ∧ restriction N M hNM g = f := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro N h3 hM hNM f hf hinv
    have hN : 0 < N := by omega
    by_cases hEq : N = M
    · subst N
      exact ⟨f,hf,restriction_self M f⟩
    obtain ⟨t,ht⟩ := hNM
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1, mul_one] at ht
      exact hEq ht.symm
    obtain ⟨p,hp,hpt⟩ := Nat.exists_prime_and_dvd ht1
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨u,hu⟩ := hpt
    have hu0 : 0 < u := by
      by_contra hz
      have hz0 : u = 0 := Nat.eq_zero_of_not_pos hz
      rw [hu,hz0,mul_zero,mul_zero] at ht
      exact hM.ne' ht
    let K := N * u
    have hK : 0 < K := Nat.mul_pos hN hu0
    have he : M = p * K := by
      rw [ht,hu]
      dsimp [K]
      ring
    have hKM : K < M := by
      rw [he]
      have hp2 := hp.two_le
      nlinarith
    have hNK : N ∣ K := dvd_mul_right N u
    have hNKle : N ≤ K := Nat.le_of_dvd hK hNK
    have hK3 : 3 ≤ K := h3.trans hNKle
    cases he
    have hinvK : ∀ γ ∈ (ΓP K), ⇑f ∣[(2 : ℤ)] γ = ⇑f :=
      fun γ hγ => hinv γ (principal_group_le hNK hγ)
    obtain ⟨gK,hgK,heK⟩ := invariant_product_descent_prime p K hK3 f hf hinvK
    have hcoef : (gK : ℍ → ℂ) = (f : ℍ → ℂ) := by
      funext τ
      have h := congrArg (fun F : _root_.ModularForm (ΓP (p * K)) 2 => F τ) heK
      exact h
    have hinvN : ∀ γ ∈ (ΓP N), ⇑gK ∣[(2 : ℤ)] γ = ⇑gK := by
      intro γ hγ
      rw [hcoef]
      exact hinv γ hγ
    obtain ⟨g,hg,heG⟩ := ih K hKM N h3 hK hNK gK hgK hinvN
    refine ⟨g,hg,?_⟩
    calc restriction N (p * K) (dvd_trans hNK (dvd_mul_left K p)) g =
        restriction K (p * K) (dvd_mul_left K p) (restriction N K hNK g) :=
          (restriction_trans hNK (dvd_mul_left K p) g).symm
      _ = f := by rw [heG,heK]

/-- The actual normalized trace of every upper Good degree-two product-span
member lies in the lower product span at arbitrary positive divisible levels. -/
theorem trace_productSpan_all {N M : ℕ} (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    {f : _root_.ModularForm (ΓP M) 2} (hf : f ∈ productSpan M hM) :
    normalizedTrace N M hM f ∈ productSpan N (by omega) := by
  let T := normalizedTrace N M hM f
  have hUpper : restriction N M hNM T ∈ productSpan M hM :=
    restriction_trace_mem_upper hM hNM hf
  have hInv : ∀ γ ∈ (ΓP N), ⇑(restriction N M hNM T) ∣[(2 : ℤ)] γ = ⇑(restriction N M hNM T) :=
    fun γ hγ => T.slash_action_eq' γ hγ
  obtain ⟨g,hg,he⟩ := invariant_product_descent M N h3 hM hNM (restriction N M hNM T) hUpper hInv
  have hEq : g = T := restriction_injective N M hNM he
  rwa [hEq] at hg

/-- The all-level trace endpoint for an arbitrary actual Good degree-two generator. -/
theorem trace_productForm_all {N M : ℕ} (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    (v : Fin 2 → ℤ × ℤ) (hv : ∀ i, AllLevelForms.Good M (v i)) :
    normalizedTrace N M hM (productForm M hM 2 v hv) ∈ productSpan N (by omega) :=
  trace_productSpan_all h3 hM hNM (Submodule.subset_span ⟨v,hv,rfl⟩)

end ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalProductTrace
