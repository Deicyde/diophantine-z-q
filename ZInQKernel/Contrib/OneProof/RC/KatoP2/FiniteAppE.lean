import ZInQKernel.Contrib.OneProof.RC.KatoP2.ExtendedNorm
import ZInQKernel.Contrib.OneProof.RC.AppEK1.FiniteIdentity

/-! The finite (E.1) comparison can use the same norm data as the dyadic
Kodai application, independently of any Iwasawa divisibility. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open AppEK1 Kato812 ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.Even

/-- The prime-power tail of the finite norm at any positive full odd part. -/
theorem dyadicNorm_of_retained {E : WeierstrassCurve ℚ} {c ds : ℕ} (Z : RetainedZeta E c ds)
    (h812 : KatoProp812Print E c ds Z.es Z.zAt) {d n n' : ℕ}
    (hd : d ≠ 0) (hn : n ≠ 0) (hle : n ≤ n') (hs : Nat.Coprime d (c * ds)) :
    Z.es.cor (d * 2 ^ n) (d * 2 ^ n') (Nat.mul_dvd_mul_left d (pow_dvd_pow 2 hle))
      (Z.es.z (d * 2 ^ n')) = Z.es.z (d * 2 ^ n) := by
  have hn' : n' ≠ 0 := by omega
  have htwo : Nat.Coprime 2 (c * ds) :=
    Z.smooth_fixed.symm.coprime_dvd_left (dvd_mul_right _ _)
  have h := retained_norm Z h812 (by positivity : 0 < d * 2 ^ n) (by positivity)
    (Nat.mul_dvd_mul_left d (pow_dvd_pow 2 hle)) (hs.mul_left (htwo.pow_left n'))
  have hdiff : (d * 2 ^ n').primeFactors \ (fixedSupport E ∪ (d * 2 ^ n).primeFactors) = ∅ := by
    rw [primeFactors_mul_two_pow hd hn', primeFactors_mul_two_pow hd hn]
    exact Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_right
  simpa only [hdiff, Finset.prod_empty, one_smul] using h

/-- The finite norm needed for (E.1) at the actual newform level. The
fixed-prime deletion follows from the squareclass condition of the family. -/
theorem finiteNorm_of_retained {E : WeierstrassCurve ℚ} {c ds n : ℕ}
    (Z : RetainedZeta E c ds) (h812 : KatoProp812Print E c ds Z.es Z.zAt)
    (fam : BinaryFamily (CST.newformLevel E)) (x : Fin fam.b → ZMod 2)
    (hs : Nat.Coprime (supportProduct fam) (c * ds)) (hn : n ≠ 0) :
    FiniteNorm Z.es E fam x n := by
  have h2 : Nat.Coprime 2 (c * ds) :=
    Z.smooth_fixed.symm.coprime_dvd_left (dvd_mul_right _ _)
  have hd := Int.natAbs_ne_zero.mpr (fam.sqfree x).ne_zero
  have hf := supportProduct_ne_zero fam
  have hnorm := retained_norm Z h812
    (Nat.mul_pos (Nat.pos_of_ne_zero hd) (by positivity))
    (by exact Nat.mul_pos (Nat.pos_of_ne_zero hf) (by positivity))
    (Nat.mul_dvd_mul_right (oddConductor_dvd_supportProduct fam x) (2 ^ n))
    (hs.mul_left (h2.pow_left n))
  have hdiff : (supportProduct fam * 2 ^ n).primeFactors \
      (fixedSupport E ∪ (oddConductor fam x * 2 ^ n).primeFactors) =
        unusedPrimes fam.support (fam.h x) := by
    have hg := unused_disjoint_fixed fam x
    rw [← addedPrimes_eq_unused fam x hn] at hg ⊢
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_union]
    refine ⟨fun ⟨hu, hl⟩ => ⟨hu, fun h => hl (Or.inr h)⟩, ?_⟩
    rintro ⟨hu, hl⟩
    exact ⟨hu, fun h => h.elim (Finset.disjoint_left.mp hg (Finset.mem_sdiff.mpr ⟨hu, hl⟩)) hl⟩
  simpa only [FiniteNorm, hdiff] using hnorm

/-- The same finite (E.1) conclusion at these levels, using only the
retained 2004 construction, Prop. 8.12, and the weighted transfer laws. -/
theorem finite_e1_p2 {B : Type} [CommGroup B] {E : WeierstrassCurve ℚ} {c ds n : ℕ}
    (Z : RetainedZeta E c ds) (h812 : KatoProp812Print E c ds Z.es Z.zAt)
    (fam : BinaryFamily (CST.newformLevel E)) (x : Fin fam.b → ZMod 2)
    (hs : Nat.Coprime (supportProduct fam) (c * ds)) (hn : n ≠ 0)
    {Y : Type} [AddCommGroup Y] [Module (MonoidAlgebra ℤ_[2] B) Y]
    (bar : (ZMod (oddConductor fam x * 2 ^ n))ˣ →* B)
    (χ : (ZMod (oddConductor fam x * 2 ^ n))ˣ →* ℤ_[2]ˣ)
    (upper : Z.es.H (supportProduct fam * 2 ^ n) →+ Y)
    (prim : Z.es.H (oddConductor fam x * 2 ^ n) →+ Y)
    (trans : upper = prim.comp (Z.es.cor _ _
      (Nat.mul_dvd_mul_right (oddConductor_dvd_supportProduct fam x) (2 ^ n))))
    (equiv : ∀ r z, prim (r • z) = weightedMap bar χ r • prim z) :
    upper (Z.es.z (supportProduct fam * 2 ^ n)) =
      (∏ q ∈ unusedPrimes fam.support (fam.h x), constituentFactor E bar χ q) •
        prim (Z.es.z (oddConductor fam x * 2 ^ n)) :=
  finite_e1 fam x E Z.es n (finiteNorm_of_retained Z h812 fam x hs hn) bar χ upper prim trans equiv

end ZInQ.Manuscript.RC.KatoP2
