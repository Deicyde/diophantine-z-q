import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Interface
import ZInQKernel.Contrib.OneProof.RC.AppEK1.FiniteIdentity
import ZInQKernel.Contrib.OneProof.RC.Even.Smoothing

/-!
# Appendix E, finite (E.1) with the support-sensitive norm

The families are the existing admissible binary families at the actual form level.
Their local squareclass condition forces every odd conductor prime in the family
support to be present in every constituent. Such a prime stays in both omitted
supports and never contributes an Euler factor.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Kato812

open PrintsArith AppEK1 ZInQ.Contrib.CloudB3RC53 _root_.ZInQ.Manuscript.RC.Even

/-- A positive common power of two and the fixed form level do not change the
index set of the finite product. The removal of fixed primes is valid for
admissible families, even when the family support itself meets the form level. -/
theorem normSupport_eq_unused {E : WeierstrassCurve ℚ} {n : ℕ}
    (fam : BinaryFamily (CST.newformLevel E)) (x : Fin fam.b → ZMod 2) (hn : n ≠ 0) :
    (supportProduct fam * 2 ^ n).primeFactors \
      (fixedSupport E ∪ (oddConductor fam x * 2 ^ n).primeFactors) =
    unusedPrimes fam.support (fam.h x) := by
  have hgood := unused_disjoint_fixed fam x
  rw [← addedPrimes_eq_unused fam x hn] at hgood ⊢
  ext q
  simp only [Finset.mem_sdiff, Finset.mem_union]
  exact ⟨fun ⟨hupper, hnot⟩ => ⟨hupper, fun hlow => hnot (Or.inr hlow)⟩,
    fun ⟨hupper, hlow⟩ => ⟨hupper, fun h => h.elim
      (Finset.disjoint_left.mp hgood (Finset.mem_sdiff.mpr ⟨hupper, hlow⟩)) hlow⟩⟩

/-- At a fixed full odd part, changing positive dyadic exponents introduces
no factor, even if the odd part meets the form level. Take `n' = n + a`
to pass from `D * 2^n` to `d * 2^n` for `D = 2^a * d`. -/
theorem dyadicNorm_812 {E : WeierstrassCurve ℚ} {c ds : ℕ} {Sbad : Finset ℕ}
    (K : KatoZetaInterface812 E c ds Sbad) {d n n' : ℕ}
    (hd : d ≠ 0) (hn : n ≠ 0) (hle : n ≤ n')
    (hoddPart : Disjoint (c * ds).primeFactors d.primeFactors) :
    K.es.cor (d * 2 ^ n) (d * 2 ^ n')
      (Nat.mul_dvd_mul_left d (pow_dvd_pow 2 hle)) (K.es.z (d * 2 ^ n')) =
        K.es.z (d * 2 ^ n) := by
  have hn' : n' ≠ 0 := by omega
  have htwo : Disjoint (c * ds).primeFactors ({2} : Finset ℕ) :=
    K.smooth_bad.mono_right (Finset.singleton_subset_iff.mpr K.two_mem_bad)
  have hs : Disjoint (c * ds).primeFactors (d * 2 ^ n').primeFactors := by
    rw [primeFactors_mul_two_pow hd hn']
    exact Finset.disjoint_union_right.mpr ⟨hoddPart, htwo⟩
  have h := K.norm (by positivity : 0 < d * 2 ^ n) (by positivity)
    (Nat.mul_dvd_mul_left d (pow_dvd_pow 2 hle)) hs
  have hdiff : (d * 2 ^ n').primeFactors \ (Sbad ∪ (d * 2 ^ n).primeFactors) = ∅ := by
    rw [primeFactors_mul_two_pow hd hn', primeFactors_mul_two_pow hd hn]
    exact Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_right
  simpa only [hdiff, Finset.prod_empty, one_smul] using h

/-- Obtain the norm needed in the existing finite (E.1) proof. The smoothers
must avoid the family's support; the form level need not avoid that support. -/
theorem finiteNorm_of_kato812 {E : WeierstrassCurve ℚ} {c ds : ℕ}
    (K : KatoZetaInterface812 E c ds (fixedSupport E))
    (fam : BinaryFamily (CST.newformLevel E)) (x : Fin fam.b → ZMod 2)
    (hsmooth : Disjoint (c * ds).primeFactors fam.support) {n : ℕ} (hn : n ≠ 0) :
    FiniteNorm K.es E fam x n := by
  have hd : oddConductor fam x ≠ 0 := Int.natAbs_ne_zero.mpr (fam.sqfree x).ne_zero
  have hF := supportProduct_ne_zero fam
  have hs : Disjoint (c * ds).primeFactors (supportProduct fam * 2 ^ n).primeFactors := by
    rw [primeFactors_mul_two_pow hF hn, primeFactors_supportProduct]
    exact Finset.disjoint_union_right.mpr ⟨hsmooth,
      K.smooth_bad.mono_right (Finset.singleton_subset_iff.mpr K.two_mem_bad)⟩
  have h := K.norm (by positivity : 0 < oddConductor fam x * 2 ^ n) (by positivity)
    (Nat.mul_dvd_mul_right (oddConductor_dvd_supportProduct fam x) (2 ^ n)) hs
  rw [normSupport_eq_unused fam x hn] at h
  exact h

/-- The (K5) smoothers are prime to the entire family support. -/
theorem smoothing_avoids_support {N e Nodd : ℕ} (fam : BinaryFamily N) :
    Disjoint
      (smoothing e Nodd (supportProduct fam) * smoothing e Nodd (supportProduct fam)).primeFactors
      fam.support := by
  have hc : Nat.Coprime (smoothing e Nodd (supportProduct fam)) (supportProduct fam) :=
    coprime_one_add_of_dvd ⟨2 ^ e * (3 * Nodd), by ring⟩
  simpa only [primeFactors_supportProduct] using (hc.mul_left hc).disjoint_primeFactors

section Transfer

variable {B : Type*} [CommGroup B]

/-- Finite (E.1) for every admissible family at the form level, relative to the
widened retained interface for that family's (K5) smoothing. At `n ≥ max a 2`
one may take `χ = constituentWeight …` to obtain the full weight of (E.2).
The transfer laws remain the same as in the original finite proof. -/
theorem finite_e1_812 {E : WeierstrassCurve ℚ} (fam : BinaryFamily (CST.newformLevel E))
    (x : Fin fam.b → ZMod 2) {e Nodd n : ℕ} (hn : n ≠ 0)
    (K : KatoZetaInterface812 E (smoothing e Nodd (supportProduct fam))
      (smoothing e Nodd (supportProduct fam)) (fixedSupport E))
    {Y : Type*} [AddCommGroup Y] [Module (MonoidAlgebra ℤ_[2] B) Y]
    (bar : (ZMod (oddConductor fam x * 2 ^ n))ˣ →* B)
    (χ : (ZMod (oddConductor fam x * 2 ^ n))ˣ →* ℤ_[2]ˣ)
    (upper : K.es.H (supportProduct fam * 2 ^ n) →+ Y)
    (prim : K.es.H (oddConductor fam x * 2 ^ n) →+ Y)
    (trans : upper = prim.comp (K.es.cor _ _
      (Nat.mul_dvd_mul_right (oddConductor_dvd_supportProduct fam x) (2 ^ n))))
    (equiv : ∀ r z, prim (r • z) = weightedMap bar χ r • prim z) :
    upper (K.es.z (supportProduct fam * 2 ^ n)) =
      (∏ q ∈ unusedPrimes fam.support (fam.h x), constituentFactor E bar χ q) •
        prim (K.es.z (oddConductor fam x * 2 ^ n)) :=
  finite_e1 fam x E K.es n (finiteNorm_of_kato812 K fam x (smoothing_avoids_support fam) hn)
    bar χ upper prim trans equiv

end Transfer

end ZInQ.Manuscript.RC.Kato812
