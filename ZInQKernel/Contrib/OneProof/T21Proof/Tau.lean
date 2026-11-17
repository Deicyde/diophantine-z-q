import ZInQKernel.Contrib.OneProof.T21Proof.BaseChange
import ZInQKernel.Contrib.OneProof.T21Proof.GlobalStep
import ZInQKernel.Contrib.OneProof.T21Proof.Finite
import ZInQKernel.Contrib.TYZChain.Lcal

/-!
# t21-proof: the admissible embeddings `τ : ℚ(√−3) → B` and the place `2`

Task t21-proof.
* `admissible_signs`: an admissible `τ` (TYZ L527–534) has `τ(√−3) = ±i ± j ± k` and
  `τ((1 + √−3)/2) = ω_s`;
* `int_basis`: every element of `𝓞(ℚ(√−3))` is `m + n ω`, `ω = (1 + √−3)/2`;
* `piQ_tauHat_mem`: `τ̂(Ô_K)` lies in `ℤ_p + ℤ_p ω_s` at every place;
* the place `2`: `p_v = 2` and `v` is the only place containing `2`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open ZInQ.Contrib.TYZDecomp.H29Split IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## `ω = (1 + √−3)/2` -/

/-- `(1 + √−3)/2 ∈ 𝓞(ℚ(√−3))`. -/
def ωK : 𝓞 (QNeg 3) :=
  ⟨⟨1 / 2, 1 / 2⟩, by
    have h : (⟨1 / 2, 1 / 2⟩ : QNeg 3) = ZInQ.Contrib.TYZLcal.zeta3 + 1 := by
      ext <;> simp [ZInQ.Contrib.TYZLcal.zeta3, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast] <;> norm_num
    rw [h]
    exact ((ZInQ.Contrib.TYZLcal.zeta3_isPrimitiveRoot.isIntegral (by norm_num)).add
      isIntegral_one)⟩

theorem ωK_coe : ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ⟨1 / 2, 1 / 2⟩ := rfl

theorem sqrtNeg_eq : sqrtNeg 3 = 2 * ((ωK : 𝓞 (QNeg 3)) : QNeg 3) - 1 := by
  rw [ωK_coe]; ext <;> simp [sqrtNeg, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast] <;> norm_num

theorem sqrtNeg_sq : sqrtNeg 3 * sqrtNeg 3 = (-3 : QNeg 3) := by
  ext <;> simp [sqrtNeg, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

/-- **The integers of `ℚ(√−3)`**: `𝓞 = ℤ + ℤ ω`. -/
theorem int_basis (x : 𝓞 (QNeg 3)) : ∃ m n : ℤ, (x : QNeg 3) = m + n * ((ωK : 𝓞 (QNeg 3)) : QNeg 3) := by
  have := ZInQ.Contrib.TYZLcal.isCyclotomicExtension_three
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime
    ZInQ.Contrib.TYZLcal.zeta3_isPrimitiveRoot
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ
    ({ZInQ.Contrib.TYZLcal.zeta3} : Set (QNeg 3)))).mp x.2
  have hx : (x : QNeg 3) = ((y : Algebra.adjoin ℤ ({ZInQ.Contrib.TYZLcal.zeta3} : Set (QNeg 3))) :
      QNeg 3) := hy.symm
  rw [hx]
  have key : ∀ z ∈ Algebra.adjoin ℤ ({ZInQ.Contrib.TYZLcal.zeta3} : Set (QNeg 3)),
      ∃ m n : ℤ, z = m + n * ZInQ.Contrib.TYZLcal.zeta3 := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by rw [hx]; simp⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, n, rfl⟩ := hx
      obtain ⟨m', n', rfl⟩ := hy
      exact ⟨m + m', n + n', by push_cast; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨m, n, rfl⟩ := hx
      obtain ⟨m', n', rfl⟩ := hy
      refine ⟨m * m' - n * n', m * n' + n * m' - n * n', ?_⟩
      have hz2 : ZInQ.Contrib.TYZLcal.zeta3 * ZInQ.Contrib.TYZLcal.zeta3 =
          -1 - ZInQ.Contrib.TYZLcal.zeta3 := by
        ext <;> simp [ZInQ.Contrib.TYZLcal.zeta3, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast] <;> norm_num
      push_cast
      linear_combination ((n : QNeg 3) * n') * hz2
  obtain ⟨m, n, hmn⟩ := key y y.2
  refine ⟨m - n, n, ?_⟩
  rw [hmn, ωK_coe]
  ext <;> simp [ZInQ.Contrib.TYZLcal.zeta3, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast] <;> ring

/-! ## The signs of an admissible embedding -/

/-- `ω_s ∈ B = ℍ[ℚ]`. -/
def ωq (s : Signs) : ℍ[ℚ] := hurZ (ωH s)

theorem sq_eq_three {x y z : ℤ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
    (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) ∧ (z = 1 ∨ z = -1) := by
  have hx : x ^ 2 ≤ 3 := by nlinarith [sq_nonneg y, sq_nonneg z]
  have hy : y ^ 2 ≤ 3 := by nlinarith [sq_nonneg x, sq_nonneg z]
  have hz : z ^ 2 ≤ 3 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have bx : -1 ≤ x ∧ x ≤ 1 := by constructor <;> nlinarith
  have by' : -1 ≤ y ∧ y ≤ 1 := by constructor <;> nlinarith
  have bz : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith
  obtain ⟨bx1, bx2⟩ := bx
  obtain ⟨by1, by2⟩ := by'
  obtain ⟨bz1, bz2⟩ := bz
  interval_cases x <;> interval_cases y <;> interval_cases z <;> simp_all

/-- The sign bit of `±1`. -/
def bitOf (x : ℤ) : Fin 2 := if x = 1 then 0 else 1

theorem sg_bitOf {x : ℤ} (h : x = 1 ∨ x = -1) : sg (bitOf x) = x := by
  rcases h with rfl | rfl <;> decide

/-- **An admissible `τ` has `τ(ω) = ω_s` for sign bits `s`** (`τ(√−3) = ±i ± j ± k`). -/
theorem admissible_signs {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau 3 τ) :
    ∃ s : Signs, τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s := by
  obtain ⟨a, b, c, d, e, he⟩ := hτ.1 ωK
  have hsq : τ (sqrtNeg 3) * τ (sqrtNeg 3) = -3 := by
    rw [← map_mul, sqrtNeg_sq, map_neg, map_ofNat]
  rw [sqrtNeg_eq, map_sub, map_mul, map_ofNat, map_one, he] at hsq
  set r : ℤ := 2 * a - e - 1
  set x : ℤ := 2 * b + e
  set y : ℤ := 2 * c + e
  set z : ℤ := 2 * d + e
  have hq : (2 : ℍ[ℚ]) * ⟨(a : ℚ) - e / 2, b + e / 2, c + e / 2, d + e / 2⟩ - 1 =
      ⟨(r : ℚ), (x : ℚ), (y : ℚ), (z : ℚ)⟩ := by
    ext <;> simp [r, x, y, z, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
  rw [hq] at hsq
  have h0 := congrArg (·.re) hsq
  have h1 := congrArg (·.imI) hsq
  have h2 := congrArg (·.imJ) hsq
  have h3 := congrArg (·.imK) hsq
  simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] at h0 h1 h2 h3
  have hr : r = 0 := by
    by_contra hr
    have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr
    have hx0 : (x : ℚ) = 0 := by
      have : (r : ℚ) * x + r * x = 0 := by linarith
      have : 2 * ((r : ℚ) * x) = 0 := by linarith
      simpa [hr'] using this
    have hy0 : (y : ℚ) = 0 := by
      have : 2 * ((r : ℚ) * y) = 0 := by linarith
      simpa [hr'] using this
    have hz0 : (z : ℚ) = 0 := by
      have : 2 * ((r : ℚ) * z) = 0 := by linarith
      simpa [hr'] using this
    rw [hx0, hy0, hz0] at h0
    nlinarith [sq_nonneg (r : ℚ)]
  have hsum : x ^ 2 + y ^ 2 + z ^ 2 = 3 := by
    rw [hr] at h0
    have : ((x : ℚ)) ^ 2 + (y : ℚ) ^ 2 + (z : ℚ) ^ 2 = 3 := by push_cast at h0; nlinarith
    exact_mod_cast this
  obtain ⟨hx, hy, hz⟩ := sq_eq_three hsum
  refine ⟨(bitOf x, bitOf y, bitOf z), ?_⟩
  rw [he]
  apply hc_injective
  rw [ωq, hurZ, hc_hur]
  have hxs := sg_bitOf hx
  have hys := sg_bitOf hy
  have hzs := sg_bitOf hz
  -- coordinates
  have er : (a : ℚ) - e / 2 = 1 / 2 := by
    have : ((r : ℤ) : ℚ) = 0 := by rw [hr]; simp
    simp only [r] at this; push_cast at this; linarith
  simp only [hc, ωH, mapH, eq_intCast]
  have hbz : ((bitOf z : ℕ) : ℚ) = (1 - z) / 2 := by
    rcases hz with h | h <;> simp [bitOf, h]
  have hbx : ((bitOf x : ℕ) : ℚ) = (1 - x) / 2 := by
    rcases hx with h | h <;> simp [bitOf, h]
  have hby : ((bitOf y : ℕ) : ℚ) = (1 - y) / 2 := by
    rcases hy with h | h <;> simp [bitOf, h]
  have hzz : ((sg (bitOf z) : ℤ) : ℚ) = z := by rw [hzs]
  simp only [H4.mk.injEq]
  push_cast
  rw [hbz, hbx, hby, hzz]
  simp only [x, y, z]
  push_cast
  refine ⟨by linarith, by ring, by ring, by ring⟩

/-! ## `τ̂(Ô_K) ⊂ ℤ_p + ℤ_p ω` -/

theorem qp_int_add {p : ℕ} [Fact p.Prime] (m n : ℤ) (ω : ℍ[ℚ]) :
    qp p ((m : ℍ[ℚ]) + (n : ℍ[ℚ]) * ω) = (m : ℚ_[p]) • (1 : ℍ[ℚ_[p]]) + (n : ℚ_[p]) • qp p ω := by
  rw [map_add, map_mul, map_intCast, map_intCast]
  rw [← Quaternion.coe_mul_eq_smul]
  ext <;> simp

/-- **`τ̂(Ô_K)` lies in `ℤ_p + ℤ_p ω_s` at every place.** -/
theorem piQ_tauHat_mem {τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]} {s : Signs}
    (hs : τ ((ωK : 𝓞 (QNeg 3)) : QNeg 3) = ωq s)
    {a : FiniteAdeleRing (𝓞 (QNeg 3)) (QNeg 3)}
    (ha : a ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg 3)) (QNeg 3))
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    InR (qp (Pw w : ℕ) (ωq s)) (piQ w (tauHat 3 τ a)) := by
  obtain ⟨c, hc, he⟩ := tauHat_integral 3 τ ha w
  choose m n hmn using fun i => int_basis (RingOfIntegers.basis (QNeg 3) i)
  have hτb : ∀ i, qp (Pw w : ℕ) (τ (bK 3 i)) =
      (m i : ℚ_[Pw w]) • (1 : ℍ[ℚ_[Pw w]]) + (n i : ℚ_[Pw w]) • qp (Pw w : ℕ) (ωq s) := by
    intro i
    rw [bK, hmn i, map_add, map_mul, map_intCast, map_intCast, hs, qp_int_add]
  refine ⟨∑ i, c i * m i, ∑ i, c i * n i, ?_, ?_, 0, isHur_zero, ?_⟩
  · exact (Zp _).sum_mem fun i _ => (Zp _).mul_mem (hc i) (Padic.norm_int_le_one _)
  · exact (Zp _).sum_mem fun i _ => (Zp _).mul_mem (hc i) (Padic.norm_int_le_one _)
  · rw [he, smul_zero, add_zero, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hτb, smul_add, smul_smul, smul_smul]

/-! ## The place `2` -/

theorem Pw_coe (w : HeightOneSpectrum (𝓞 ℚ)) :
    (Pw w : ℕ) = Rat.HeightOneSpectrum.natGenerator w := rfl

theorem Pw_eq_two {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v) : (Pw v : ℕ) = 2 := by
  rw [Pw_coe]
  have hd : Rat.HeightOneSpectrum.natGenerator v ∣ 2 := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rw [map_ofNat] at this
    exact_mod_cast this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v)
    Nat.prime_two).mp hd

theorem eq_of_Pw_eq {v w : HeightOneSpectrum (𝓞 ℚ)} (h : (Pw w : ℕ) = (Pw v : ℕ)) : w = v :=
  Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)

theorem not_isPlaceTwo_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v) (hw : w ≠ v) :
    ¬ IsPlaceTwo w := fun h => hw (eq_of_Pw_eq (by rw [Pw_eq_two h, Pw_eq_two hv]))

theorem Pw_ne_two {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceTwo v) (hw : w ≠ v) :
    (Pw w : ℕ) ≠ 2 := fun h => hw (eq_of_Pw_eq (by rw [h, Pw_eq_two hv]))

theorem exists_place_of_prime (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 ℚ), (Pw w : ℕ) = p :=
  ⟨Rat.HeightOneSpectrum.primesEquiv.symm (⟨p, hp⟩ : Nat.Primes),
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply (⟨p, hp⟩ : Nat.Primes))⟩

end ZInQ.Contrib.T21Proof
