import ZInQKernel.Contrib.LocalSquareRoot.Cyclotomic

/-!
# Prime-to-residue-characteristic roots and all-element action comparison

These are additive T31 arithmetic helpers over actual quotient rings and
finite fields.  Reduction is not assumed injective on the whole integer ring:
its injectivity on prime-to-characteristic roots is proved using the existing
finite Frobenius source.  The finite-cardinality comparison is a displayed
input, not a replacement for the unramified number-field bridge.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open ZInQ.Contrib.LocalSquareRoot

/-- Prime-to-characteristic primitive roots retain their exact order on reduction. -/
theorem primitiveRoot_quotient_of_degree_not_mem
    {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {m : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ m) (hm : (m : R) ∉ Q) :
    IsPrimitiveRoot (Ideal.Quotient.mk Q ζ) m := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], ?_⟩
  intro l hl
  have he : Ideal.Quotient.mk Q (ζ ^ l) = Ideal.Quotient.mk Q (1 : R) := by
    simpa only [map_pow, map_one] using hl
  have hp : (ζ ^ l) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm l m, pow_mul, hζ.pow_eq_one, one_pow]
  have hr : ζ ^ l = 1 := GlueSqrtLocal.eq_of_pow_eq_one_of_sub_mem Q hp (one_pow m)
    (Ideal.Quotient.eq.mp he) hm
  exact hζ.dvd_of_pow_eq_one l hr

/-- Every nonzero element of a field of cardinality `p^f` is a root at level
`p^n-1` whenever the actual residue degree `f` divides `n`. -/
theorem finiteField_pow_level_eq_one
    {K : Type*} [Field K] [Finite K] (p f n : ℕ) (hp : 1 ≤ p)
    (hcard : Nat.card K = p ^ f) (hfn : f ∣ n) (x : K) (hx : x ≠ 0) :
    x ^ (p ^ n - 1) = 1 := by
  let : Fintype K := Fintype.ofFinite K
  have hpows : ∀ t : ℕ, x ^ (Fintype.card K ^ t) = x := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, pow_mul, ih, FiniteField.pow_card]
  obtain ⟨t, ht⟩ := hfn
  have hpow : x ^ (p ^ n) = x := by
    rw [ht, pow_mul, ← hcard, Nat.card_eq_fintype_card]
    exact hpows t
  have hge : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
  apply mul_right_cancel₀ hx
  rw [← pow_succ, Nat.sub_add_cancel hge, one_mul]
  exact hpow

/-- Fixing one actual primitive level root fixes every element of an embedded
finite residue field whose degree divides the level. -/
theorem fixed_finiteField_image_of_primitive_level
    {K F : Type*} [Field K] [Finite K] [Field F]
    (ι : K →+* F) (σ : F ≃+* F) (p f n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (hcard : Nat.card K = p ^ f) (hfn : f ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ n - 1))
    (hσ : σ ζ = ζ) (x : K) : σ (ι x) = ι x := by
  let : NeZero (p ^ n - 1) := ⟨by
    have h := Nat.le_self_pow hn.ne' p
    omega⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hroot : (ι x) ^ (p ^ n - 1) = 1 := by
    rw [← map_pow, finiteField_pow_level_eq_one p f n (by omega) hcard hfn x hx, map_one]
  obtain ⟨k, _, hk⟩ := hζ.eq_pow_of_pow_eq_one hroot
  rw [← hk, map_pow, hσ]

end ZInQ.Contrib.UnramifiedCocycle
