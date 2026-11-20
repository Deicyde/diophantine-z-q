import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Kato
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource
import ZInQKernel.Contrib.OneProof.RC.AppEK1.Coefficients

/-!
# Range of the Euler-system interface and the finite identity (E.1)

The finite norm and the weighted transfer have distinct jobs. The norm introduces the
Euler factors. Transitivity and semilinearity of the transfer then carry them to the
constituent coefficient ring. The abstract Euler-system interface only supplies the
norm on its stated range; it does not supply the transfer and its comparison.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppEK1

open _root_.ZInQ.Manuscript.RC.Even PrintsArith

/-- The odd squarefree support integer of the given family. -/
def supportProduct {N : ℕ} (fam : BinaryFamily N) : ℕ := ∏ q ∈ fam.support, q

/-- The positive odd part of the conductor attached to the given constituent. -/
abbrev oddConductor {N : ℕ} (fam : BinaryFamily N) (x : Fin fam.b → ZMod 2) : ℕ :=
  (fam.h x).natAbs

/-- Every member of the support is prime. -/
theorem prime_of_mem_support {N : ℕ} {fam : BinaryFamily N} {p : ℕ}
    (hp : p ∈ fam.support) : p.Prime := by
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hx

/-- Odd family parameters exclude two from the support. -/
theorem two_not_mem_support {N : ℕ} (fam : BinaryFamily N) : 2 ∉ fam.support := by
  intro hp
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hp
  have hd : (2 : ℤ) ∣ fam.h x := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hx)
  exact (Int.not_even_iff_odd.mpr (fam.odd x)) (even_iff_two_dvd.mpr hd)

/-- The family support product is nonzero, including for empty support. -/
theorem supportProduct_ne_zero {N : ℕ} (fam : BinaryFamily N) :
    supportProduct fam ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => (prime_of_mem_support hp).ne_zero

/-- Taking the prime factors of the support product recovers the original support. -/
theorem primeFactors_supportProduct {N : ℕ} (fam : BinaryFamily N) :
    (supportProduct fam).primeFactors = fam.support :=
  Nat.primeFactors_prod fun _ hp => prime_of_mem_support hp

/-- Each primitive odd conductor divides the whole support product. -/
theorem oddConductor_dvd_supportProduct {N : ℕ} (fam : BinaryFamily N) (x : Fin fam.b → ZMod 2) :
    oddConductor fam x ∣ supportProduct fam := by
  change (fam.h x).natAbs ∣ supportProduct fam
  rw [← Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr (fam.sqfree x))]
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, hq⟩

/-- Multiplication by a positive power of two adds two to the prime support. -/
theorem primeFactors_mul_two_pow {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * 2 ^ n).primeFactors = m.primeFactors ∪ {2} := by
  rw [Nat.primeFactors_mul hm (pow_ne_zero n (by decide)), Nat.primeFactors_pow _ hn,
    Nat.prime_two.primeFactors]

/-- Both indices are tested by the published interface. At a positive dyadic level the
upper index is in range exactly when no prime in the family support belongs to `Sig`. -/
theorem katoXi_support_iff {N n : ℕ} (fam : BinaryFamily N) (Sig : Finset ℕ) (hn : n ≠ 0) :
    KatoXi 2 Sig (supportProduct fam * 2 ^ n) ↔ Disjoint fam.support Sig := by
  have h0 : supportProduct fam * 2 ^ n ≠ 0 :=
    mul_ne_zero (supportProduct_ne_zero fam) (pow_ne_zero n (by decide))
  have hfac := primeFactors_mul_two_pow (supportProduct_ne_zero fam) hn
  rw [primeFactors_supportProduct] at hfac
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro q hqs hqSig
    have hqm : q ∈ (supportProduct fam * 2 ^ n).primeFactors := by
      rw [hfac]
      exact Finset.mem_union_left _ hqs
    have hq := h.2.2 q (prime_of_mem_support hqs) (Nat.dvd_of_mem_primeFactors hqm) hqSig
    exact two_not_mem_support fam (hq ▸ hqs)
  · intro hs
    refine ⟨Nat.one_le_iff_ne_zero.mpr h0, dvd_mul_of_dvd_right (dvd_pow_self _ hn) _, ?_⟩
    intro q hq hqd hqSig
    have hqm := (Nat.mem_primeFactors).mpr ⟨hq, hqd, h0⟩
    rw [hfac, Finset.mem_union, Finset.mem_singleton] at hqm
    exact hqm.resolve_left (fun hqs => (Finset.disjoint_left.mp hs hqs hqSig))

/-- Replacing the odd conductor by the whole family support introduces exactly the
unused primes; the positive common dyadic part contributes no factor. -/
theorem addedPrimes_eq_unused {N n : ℕ} (fam : BinaryFamily N) (x : Fin fam.b → ZMod 2)
    (hn : n ≠ 0) :
    (supportProduct fam * 2 ^ n).primeFactors \ (oddConductor fam x * 2 ^ n).primeFactors =
      unusedPrimes fam.support (fam.h x) := by
  have hd : oddConductor fam x ≠ 0 := Int.natAbs_ne_zero.mpr (fam.sqfree x).ne_zero
  rw [primeFactors_mul_two_pow (supportProduct_ne_zero fam) hn, primeFactors_supportProduct,
    primeFactors_mul_two_pow hd hn]
  ext q
  by_cases h₂ : q = 2
  · subst q
    simp [unusedPrimes, two_not_mem_support fam]
  · simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, h₂, or_false,
      unusedPrimes, Finset.mem_filter]
    constructor
    · rintro ⟨hq, hqd⟩
      exact ⟨hq, fun hdv => hqd (Nat.mem_primeFactors.mpr
        ⟨prime_of_mem_support hq, Int.natCast_dvd.mp hdv, hd⟩)⟩
    · rintro ⟨hq, hqd⟩
      exact ⟨hq, fun hdv => hqd (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hdv))⟩

/-- The explicit norm required at one level, including when it cannot be obtained
from `KatoXi`. This is a relation on the same classes at the two indices. -/
def FiniteNorm (D : EulerSystemData ℤ_[2]) (E : WeierstrassCurve ℚ)
    {N : ℕ} (fam : BinaryFamily N) (x : Fin fam.b → ZMod 2) (n : ℕ) : Prop :=
  let m := oddConductor fam x * 2 ^ n
  let M := supportProduct fam * 2 ^ n
  D.cor m M (Nat.mul_dvd_mul_right (oddConductor_dvd_supportProduct fam x) _) (D.z M) =
    (∏ q ∈ unusedPrimes fam.support (fam.h x),
      eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit m q)) • D.z m

/-- For the covered families the old interface supplies the precise finite norm. -/
theorem finiteNorm_of_isEulerSystem {E : WeierstrassCurve ℚ} {D : EulerSystemData ℤ_[2]}
    {Sig : Finset ℕ} (hD : D.IsEulerSystem 2 Sig (katoP E))
    {N : ℕ} (fam : BinaryFamily N) (hf : Disjoint fam.support Sig)
    (x : Fin fam.b → ZMod 2) {n : ℕ} (hn : n ≠ 0) : FiniteNorm D E fam x n := by
  have hM := (katoXi_support_iff fam Sig hn).2 hf
  have hd := Nat.mul_dvd_mul_right (oddConductor_dvd_supportProduct fam x) (2 ^ n)
  have hm : KatoXi 2 Sig (oddConductor fam x * 2 ^ n) := by
    refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, dvd_mul_of_dvd_right (dvd_pow_self _ hn) _, ?_⟩
    · exact mul_ne_zero (Int.natAbs_ne_zero.mpr (fam.sqfree x).ne_zero) (pow_ne_zero _ (by decide))
    · exact fun q hq hqm hqSig => hM.2.2 q hq (hqm.trans hd) hqSig
  have h := hD _ _ hm hM hd
  rw [addedPrimes_eq_unused fam x hn] at h
  exact h

/-- At a fixed odd part, raising a positive dyadic exponent introduces no norm
factor. This also gives the norm from `d * 2^(a+n)` to `d * 2^n` when both
indices are in the range of the retained system. -/
theorem dyadicNorm_of_isEulerSystem {E : WeierstrassCurve ℚ} {D : EulerSystemData ℤ_[2]}
    {Sig : Finset ℕ} (hD : D.IsEulerSystem 2 Sig (katoP E))
    {d n n' : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0) (hle : n ≤ n')
    (hl : KatoXi 2 Sig (d * 2 ^ n)) (hu : KatoXi 2 Sig (d * 2 ^ n')) :
    D.cor (d * 2 ^ n) (d * 2 ^ n') (Nat.mul_dvd_mul_left d (pow_dvd_pow 2 hle))
      (D.z (d * 2 ^ n')) = D.z (d * 2 ^ n) := by
  have h := hD _ _ hl hu (Nat.mul_dvd_mul_left d (pow_dvd_pow 2 hle))
  rw [primeFactors_mul_two_pow hd hn, primeFactors_mul_two_pow hd hn', Finset.sdiff_self,
    Finset.prod_empty, one_smul] at h
  exact h

/-- The full constituent character on the cofinal primitive level (E.2).
The modulus `2^a * d` is represented at level `d * 2^n` without losing
the dyadic character, including when `a = 2`. -/
def constituentWeight {N a n : ℕ} (fam : BinaryFamily N) (x : Fin fam.b → ZMod 2)
    (hn : max a 2 ≤ n)
    (χ₂ : (ZMod (2 ^ a))ˣ →* ℤ_[2]ˣ)
    (χodd : (ZMod (oddConductor fam x))ˣ →* ℤ_[2]ˣ) :
    (ZMod (oddConductor fam x * 2 ^ n))ˣ →* ℤ_[2]ˣ :=
  fullWeight
    (dvd_mul_of_dvd_right (pow_dvd_pow 2 (le_trans (le_max_left a 2) hn)) _)
    (dvd_mul_right _ _) χ₂ χodd

section Trace

variable {B : Type*} [CommGroup B]

/-- (K9), as the image of the original Euler factor under the full constituent
character and the deck quotient. Here the character is evaluated at arithmetic Frobenius
in the primitive level. Its inverse occurs in the original factor. -/
def constituentFactor (E : WeierstrassCurve ℚ) {m : ℕ}
    (bar : (ZMod m)ˣ →* B) (χ : (ZMod m)ˣ →* ℤ_[2]ˣ) (q : ℕ) : MonoidAlgebra ℤ_[2] B :=
  weightedMap bar χ (eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit m q))

/-- Finite (E.1) from the norm on the retained elements and the two transfer
laws. The two laws concern maps on all classes: composition through the primitive
level, and semilinearity for the coefficient map. The product acts after transfer
and there is no division by a group order. -/
theorem finite_e1 {N : ℕ} (fam : BinaryFamily N) (x : Fin fam.b → ZMod 2)
    (E : WeierstrassCurve ℚ) (D : EulerSystemData ℤ_[2]) (n : ℕ)
    (norm : FiniteNorm D E fam x n)
    {Y : Type*} [AddCommGroup Y] [Module (MonoidAlgebra ℤ_[2] B) Y]
    (bar : (ZMod (oddConductor fam x * 2 ^ n))ˣ →* B)
    (χ : (ZMod (oddConductor fam x * 2 ^ n))ˣ →* ℤ_[2]ˣ)
    (upper : D.H (supportProduct fam * 2 ^ n) →+ Y)
    (prim : D.H (oddConductor fam x * 2 ^ n) →+ Y)
    (trans : upper = prim.comp (D.cor _ _
      (Nat.mul_dvd_mul_right (oddConductor_dvd_supportProduct fam x) (2 ^ n))))
    (equiv : ∀ r z, prim (r • z) = weightedMap bar χ r • prim z) :
    upper (D.z (supportProduct fam * 2 ^ n)) =
      (∏ q ∈ unusedPrimes fam.support (fam.h x), constituentFactor E bar χ q) •
        prim (D.z (oddConductor fam x * 2 ^ n)) := by
  unfold FiniteNorm at norm
  rw [trans, AddMonoidHom.comp_apply, norm, equiv, map_prod]
  rfl

end Trace

/-- The existing reciprocity field shows that the unnormalized signed deck sum
is not killed by any positive natural number, for the character with those signs.
This is an anchor on the abstract module, prior to any cohomological comparison. -/
theorem anchored_weightedSum_nsmul_ne_zero {E : WeierstrassCurve ℚ} {Sig Sbad : Finset ℕ}
    (K : KatoZetaInterface E Sig Sbad) {m : ℕ} [NeZero m] (hm : KatoXi 2 Sig m)
    (χ : DirichletCharacter ℂ m) (signs : (ZMod m)ˣ → ℤ)
    (hχ : ∀ g, (signs g : ℂ) = χ (g : ZMod m))
    (hL : K.Lcont χ 1 ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    k • (∑ g : (ZMod m)ˣ, signs g • (MonoidAlgebra.of ℤ_[2] _ g • K.es.z m)) ≠ 0 := by
  intro h
  have h' := congrArg (K.per m) h
  simp only [map_nsmul, map_sum, map_zsmul, map_zero, zsmul_eq_mul, hχ, nsmul_eq_mul] at h'
  rw [K.recip m hm χ] at h'
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hk)
    (mul_ne_zero (mul_ne_zero K.s_ne_zero (K.b_ne_zero χ)) hL) h'

end ZInQ.Manuscript.RC.AppEK1
