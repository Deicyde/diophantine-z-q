import ZInQKernel.Contrib.UnramifiedCocycle.IntegralEmbedding

/-!
# Arithmetic of the exact contracted global prime

These are applications of pinned Mathlib number-field/inertia theorems to the
prime constructed by the actual `resp` embedding.  The canonical global action
is unchanged; no replacement for the producer's global group/action work is
introduced.  The residue degree comparison covers the entire global Galois
fundamental identity, including ramification index one.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2Q NumberField IsLocalRing
open ZInQ.Contrib.LocalSquareRoot

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
attribute [local instance] Ideal.Quotient.field

noncomputable def integerPrime (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p : ℤ)}

instance integerPrime_isPrime (p : Nat.Primes) : (integerPrime p).IsPrime := by
  exact (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp p.2)

theorem integerPrime_ne_bot (p : Nat.Primes) : integerPrime p ≠ ⊥ := by
  simp [integerPrime, p.2.ne_zero]

instance integerPrime_isMaximal (p : Nat.Primes) : (integerPrime p).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (integerPrime_ne_bot p)

theorem integerPrime_quotient_card (p : Nat.Primes) : Nat.card (ℤ ⧸ integerPrime p) = (p : ℕ) :=
  (Nat.card_congr (Int.quotientSpanNatEquivZMod (p : ℕ)).toEquiv).trans (Nat.card_zmod _)

variable (p : Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L] (n : ℕ) [NeZero n]
  (Q : Ideal (LocalIntegerRing p L n)) [Q.IsMaximal]
  [Q.LiesOver (maximalIdeal ℤ_[p])]

instance contractedPrime_liesOver : (contractedPrime p L n Q).LiesOver (integerPrime p) := by
  let P := contractedPrime p L n Q
  have hle : integerPrime p ≤ P.under ℤ := by
    change Ideal.span {(p : ℤ)} ≤ P.under ℤ
    apply Ideal.span_le.mpr
    intro x hx
    have hx' : x = (p : ℤ) := Set.mem_singleton_iff.mp hx
    subst x
    exact prime_mem_contractedPrime p L n Q
  have he : integerPrime p = P.under ℤ :=
    Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' hle
  exact (Ideal.liesOver_iff P (integerPrime p)).mpr he

instance contractedResidueField_finite : Finite (𝓞 L ⧸ contractedPrime p L n Q) := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  infer_instance

/-- The actual global residue field has the required `p^f` cardinality. -/
theorem contractedResidueField_card :
    Nat.card (𝓞 L ⧸ contractedPrime p L n Q) =
      (p : ℕ) ^ (contractedPrime p L n Q).inertiaDeg ℤ := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  let P := contractedPrime p L n Q
  have h := Ideal.cardQuot_pow_inertiaDeg (integerPrime p) P
  have h' : Nat.card (ℤ ⧸ integerPrime p) ^ P.inertiaDeg ℤ = Nat.card (𝓞 L ⧸ P) := by
    simpa only [Submodule.cardQuot_apply] using h
  calc
    Nat.card (𝓞 L ⧸ P) = Nat.card (ℤ ⧸ integerPrime p) ^ P.inertiaDeg ℤ := h'.symm
    _ = (p : ℕ) ^ P.inertiaDeg ℤ :=
      congrArg (fun k : ℕ => k ^ P.inertiaDeg ℤ) (integerPrime_quotient_card p)

variable [IsGalois ℚ L]

/-- The original unramified hypothesis applies to this SAME contracted prime. -/
theorem contractedPrime_ramification_one (hu : UnramifiedAt L p) :
    (contractedPrime p L n Q).ramificationIdx ℤ = 1 :=
  hu (contractedPrime p L n Q) inferInstance (prime_mem_contractedPrime p L n Q)

/-- The canonical global inertia of this exact prime is trivial. -/
theorem contractedPrime_inertia_eq_bot (hu : UnramifiedAt L p) :
    (contractedPrime p L n Q).inertia Gal(L/ℚ) = ⊥ := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  let : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ) ℤ (𝓞 L) ℚ L
  let P := contractedPrime p L n Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (integerPrime p) P
  have he := Ideal.ramificationIdxIn_eq_ramificationIdx (integerPrime p) P Gal(L/ℚ)
  exact Subgroup.card_eq_one.mp
    (hcard.trans (he.trans (contractedPrime_ramification_one p L n Q hu)))

/-- The original global fundamental identity retains every prime and both
multiplicative factors.  With `e=1`, the actual residue degree divides `[L:ℚ]`. -/
theorem contractedResidueDegree_dvd (hu : UnramifiedAt L p) :
    (contractedPrime p L n Q).inertiaDeg ℤ ∣ Module.finrank ℚ L := by
  let : NumberField L := NumberField.of_module_finite ℚ L
  let : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ) ℤ (𝓞 L) ℚ L
  let P := contractedPrime p L n Q
  let c := ((integerPrime p).primesOver (𝓞 L)).ncard
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (integerPrime p) (𝓞 L) Gal(L/ℚ)
  have he := Ideal.ramificationIdxIn_eq_ramificationIdx (integerPrime p) P Gal(L/ℚ)
  have hf := Ideal.inertiaDegIn_eq_inertiaDeg (integerPrime p) P Gal(L/ℚ)
  have hram := contractedPrime_ramification_one p L n Q hu
  refine ⟨c, ?_⟩
  calc
    Module.finrank ℚ L = Nat.card Gal(L/ℚ) := (IsGalois.card_aut_eq_finrank ℚ L).symm
    _ = c * ((integerPrime p).ramificationIdxIn (𝓞 L) *
        (integerPrime p).inertiaDegIn (𝓞 L)) := h.symm
    _ = c * (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by rw [he, hf]
    _ = P.inertiaDeg ℤ * c := by rw [hram, one_mul, Nat.mul_comm]

end ZInQ.Contrib.UnramifiedCocycle
