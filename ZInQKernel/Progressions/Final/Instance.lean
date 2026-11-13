/-
Plan step 5 (effective Dirichlet): the catalogue bound CAT₈ at `W = 4 · 324#`, from
`effective_dirichlet`. The modulus is never evaluated: only `2^16 ≤ W` is used, from
`13# = 30030`.
-/
import ZInQKernel.Progressions.Final.Effective
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Syntax.Constants.PrimorialLiteral

namespace ZInQ

/-- `2^16 ≤ W = 4 · 324#`, from `13# ≤ 324#`. -/
theorem two_pow_sixteen_le_catalogueModulus : 2 ^ 16 ≤ catalogueModulus := by
  have h13 : primorial 13 = 30030 := by
    rw [← Syntax.primorialB_eq]
    decide +kernel
  have hmono := primorial_mono (show 13 ≤ 324 by norm_num)
  unfold catalogueModulus
  omega

/-- CAT₈ for any modulus `W ≥ 2^16` in place of `W = 4 · 324#`. -/
theorem catalogueBound8_of_two_pow_le {W : ℕ} (hW : 2 ^ 16 ≤ W) (r : ℕ) (hr : r < W)
    (hcop : Nat.Coprime r W) :
    22 ≤ ({p ∈ Finset.Ioo 324 (2 ^ W ^ 8) | p.Prime ∧ p % W = r}).card := by
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow two_ne_zero W
  refine (Progressions.effective_dirichlet hW hcop).trans (Finset.card_le_card fun p hp ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_Ioo] at hp ⊢
  refine ⟨⟨by omega, hp.1.2⟩, hp.2.1, ?_⟩
  have := hp.2.2
  rwa [Nat.mod_eq_of_lt hr] at this

/-- **The catalogue bound CAT₈** (formerly a hypothesis of the main theorem): every unit class
modulo `W = 4 · 324#` contains at least twenty-two primes in `(324, 2^(W⁸))`. -/
theorem catalogueBound8 : CatalogueBound8 :=
  catalogueBound8_of_two_pow_le two_pow_sixteen_le_catalogueModulus

end ZInQ
