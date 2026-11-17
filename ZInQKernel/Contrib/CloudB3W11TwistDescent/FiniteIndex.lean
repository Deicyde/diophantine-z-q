import Mathlib

/-!
# Finite-index descent for twisted invariant vanishing

Adapted from the generic `S42C4.eq_zero_of_forall_mem_smul_eq_of_finiteIndex`
argument in Anthropic's public `fermats-last-theorem` snapshot `6e837e75`,
`P2M/Sol/S_PadicComplex_eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul.lean`.
Released under Apache-2.0; see LICENSE and NOTICE in this directory.

This is only the finite-index norm-product argument. Whole-group twisted
vanishing is an explicit hypothesis here; this module supplies no arithmetic
input and does not by itself discharge either Tate target.
-/

namespace ZInQ.Contrib.CloudB3W11TwistDescent

/-- If every nonzero power of a fixed scalar character has no invariants under
`G`, the same holds under any finite-index subgroup. The twisted norm product
of a subgroup invariant over the cosets is a whole-group invariant. -/
theorem zero_of_finiteIndex_twistedInvariants
    {G : Type*} [Group G] {L : Type*} [Field L] [MulSemiringAction G L]
    (χ : G →* Lˣ)
    (hχ : ∀ (σ τ : G), σ • ((χ τ : Lˣ) : L) = ((χ τ : Lˣ) : L))
    (hvan : ∀ m : ℤ, m ≠ 0 → ∀ x : L,
      (∀ σ : G, σ • x = ((χ σ : Lˣ) : L) ^ m * x) → x = 0)
    (H : Subgroup G) [H.FiniteIndex] (k : ℤ) (hk : k ≠ 0) (c : L)
    (hc : ∀ h : G, h ∈ H → h • c = ((χ h : Lˣ) : L) ^ k * c) :
    c = 0 := by
  classical
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  have hsm : ∀ (σ : G) (x : L),
      σ • x = MulSemiringAction.toRingHom G L σ x := fun σ x => rfl
  have hχz : ∀ (σ τ : G) (z : ℤ),
      σ • (((χ τ : Lˣ) : L) ^ z) = ((χ τ : Lˣ) : L) ^ z := by
    intro σ τ z
    rw [hsm, map_zpow₀, ← hsm, hχ]
  let τ : G ⧸ H → G := fun q => q.out
  have hτ : ∀ q : G ⧸ H, (τ q : G ⧸ H) = q := fun q => q.out_eq
  let d : G ⧸ H → L := fun q => ((χ (τ q) : Lˣ) : L) ^ (-k) * (τ q • c)
  have hd : ∀ (σ : G) (q : G ⧸ H),
      σ • d q = ((χ σ : Lˣ) : L) ^ k * d (σ • q) := by
    intro σ q
    have hmem : (τ (σ • q))⁻¹ * (σ * τ q) ∈ H := by
      rw [← QuotientGroup.eq, hτ,
        show ((σ * τ q : G) : G ⧸ H) = σ • ((τ q : G) : G ⧸ H) from rfl, hτ]
    have hsplit : σ * τ q = τ (σ • q) * ((τ (σ • q))⁻¹ * (σ * τ q)) := by
      rw [mul_inv_cancel_left]
    have h1 : σ • (τ q • c) =
        ((((χ (τ (σ • q)))⁻¹ * (χ σ * χ (τ q))) ^ k : Lˣ) : L) *
          (τ (σ • q) • c) := by
      rw [← mul_smul, hsplit, mul_smul, hc _ hmem, smul_mul', hχz,
        map_mul, map_mul, map_inv, Units.val_zpow_eq_zpow_val]
    have key : (χ (τ q)) ^ (-k) *
        (((χ (τ (σ • q)))⁻¹ * (χ σ * χ (τ q))) ^ k) =
        (χ σ) ^ k * (χ (τ (σ • q))) ^ (-k) := by
      set a := χ (τ q)
      set b := χ (τ (σ • q))
      set s := χ σ
      rw [mul_zpow, mul_zpow, inv_zpow']
      rw [mul_comm (s ^ k) (a ^ k), ← mul_assoc, ← mul_assoc,
        mul_comm (a ^ (-k)) (b ^ (-k)), mul_assoc (b ^ (-k)),
        ← zpow_add, neg_add_cancel, zpow_zero, mul_one, mul_comm]
    have keyL : ((χ (τ q) : Lˣ) : L) ^ (-k) *
        ((((χ (τ (σ • q)))⁻¹ * (χ σ * χ (τ q))) ^ k : Lˣ) : L) =
        ((χ σ : Lˣ) : L) ^ k * ((χ (τ (σ • q)) : Lˣ) : L) ^ (-k) := by
      have h := congrArg (fun u : Lˣ => (u : L)) key
      simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using h
    show σ • (((χ (τ q) : Lˣ) : L) ^ (-k) * (τ q • c)) =
      ((χ σ : Lˣ) : L) ^ k *
        (((χ (τ (σ • q)) : Lˣ) : L) ^ (-k) * (τ (σ • q) • c))
    rw [smul_mul', hχz, h1, ← mul_assoc, keyL, mul_assoc]
  let P : L := ∏ q : G ⧸ H, d q
  have hP : ∀ σ : G,
      σ • P = ((χ σ : Lˣ) : L) ^ (k * (Fintype.card (G ⧸ H) : ℤ)) * P := by
    intro σ
    show σ • (∏ q : G ⧸ H, d q) = _ * ∏ q : G ⧸ H, d q
    rw [Finset.smul_prod']
    simp_rw [hd σ]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← zpow_natCast, ← zpow_mul]
    congr 1
    exact Equiv.prod_comp (MulAction.toPerm σ) d
  have hP0 : P = 0 := by
    refine hvan _ ?_ P hP
    exact mul_ne_zero hk (by exact_mod_cast Fintype.card_ne_zero)
  obtain ⟨q, -, hq⟩ := Finset.prod_eq_zero_iff.1 hP0
  have hq' : τ q • c = 0 := by
    rcases mul_eq_zero.1 hq with h | h
    · exact absurd h (zpow_ne_zero _ (χ (τ q)).ne_zero)
    · exact h
  have h := congrArg ((τ q)⁻¹ • ·) hq'
  simpa only [inv_smul_smul, smul_zero] using h

end ZInQ.Contrib.CloudB3W11TwistDescent
