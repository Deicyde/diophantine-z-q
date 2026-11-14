/-
# Integer coefficients from integral polynomial resultants

A monic rational polynomial is the image of one monic integer polynomial if its
resultants with every integer polynomial of natural degree at most its own are
integers. The test polynomial need not be monic, and the boundary is `≤`, not `<`.

The proof clears denominators minimally and rules out each denominator prime
using the actual reduced degree, including the constant-reduction case.
AI-assisted proof development on the pinned Mathlib APIs.
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Polynomial

namespace PrivateResultantIntegrality

private lemma intMap_natDegree (F : ℤ[X]) :
    (F.map (Int.castRingHom ℚ)).natDegree = F.natDegree := by
  by_cases hF : F = 0
  · simp [hF]
  · apply natDegree_map_of_leadingCoeff_ne_zero (Int.castRingHom ℚ)
    change (F.leadingCoeff : ℚ) ≠ 0
    intro h
    exact (leadingCoeff_ne_zero.mpr hF) (Int.cast_injective h)

private lemma rational_smul_eq_C_mul (a : ℚ) (P : ℚ[X]) :
    a • P = C a * P := by
  ext i
  simp only [coeff_smul, coeff_C_mul, smul_eq_mul]

/-- Positive localization supplies an actual clearing denominator.  No
minimality, primitivity, or integrality premise is assumed here. -/
private lemma exists_positive_clear (P : ℚ[X]) :
    ∃ n : ℕ, 0 < n ∧ ∃ F : ℤ[X],
      F.map (Int.castRingHom ℚ) = (n : ℚ) • P := by
  classical
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples
      (R := ℤ) (M := Submonoid.pos ℤ) (S := ℚ) P.support P.coeff
  have hbpos : 0 < (b : ℤ) := b.property
  let n : ℕ := (b : ℤ).toNat
  have hn : 0 < n := by dsimp [n]; omega
  have hbn : (b : ℤ) = (n : ℤ) := by dsimp [n]; omega
  have hL : (n : ℚ) • P ∈ lifts (Int.castRingHom ℚ) := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro i
    by_cases hi : i ∈ P.support
    · obtain ⟨z, hz⟩ := hb i hi
      refine ⟨z, ?_⟩
      change (z : ℚ) = (b : ℤ) • P.coeff i at hz
      simpa only [Int.coe_castRingHom, coeff_smul, hbn, zsmul_eq_mul,
        smul_eq_mul, Int.cast_natCast] using hz
    · have hPi : P.coeff i = 0 := notMem_support_iff.mp hi
      exact ⟨0, by simp [coeff_smul, hPi]⟩
  exact ⟨n, hn, (mem_lifts _).mp hL⟩

private lemma cleared_shape (P : ℚ[X]) (hP : P.Monic)
    (D : ℕ) (hD : 0 < D) (F : ℤ[X])
    (hF : F.map (Int.castRingHom ℚ) = (D : ℚ) • P) :
    F.natDegree = P.natDegree ∧ F.leadingCoeff = (D : ℤ) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hFC : F.map (Int.castRingHom ℚ) = C (D : ℚ) * P :=
    hF.trans (rational_smul_eq_C_mul (D : ℚ) P)
  have hdeg : F.natDegree = P.natDegree := by
    have h := congrArg Polynomial.natDegree hFC
    rw [intMap_natDegree, natDegree_C_mul hDq] at h
    exact h
  have hcoef : (F.coeff P.natDegree : ℚ) = (D : ℚ) := by
    have h := congrArg (fun T : ℚ[X] => T.coeff P.natDegree) hFC
    simpa only [coeff_map, Int.coe_castRingHom, coeff_C_mul,
      hP.coeff_natDegree, mul_one] using h
  refine ⟨hdeg, ?_⟩
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
  change (F.coeff F.natDegree : ℚ) = ((D : ℤ) : ℚ)
  simpa only [hdeg, Int.cast_natCast] using hcoef

/-- A prime dividing a least positive clearing denominator cannot divide every
coefficient.  A natural factor D = p*k avoids any quotient-cast interface. -/
private lemma cleared_reduction_ne_zero (P : ℚ[X])
    (D : ℕ) (hD : 0 < D) (F : ℤ[X])
    (hF : F.map (Int.castRingHom ℚ) = (D : ℚ) • P)
    (hmin : ∀ n : ℕ, 0 < n →
      (∃ G : ℤ[X], G.map (Int.castRingHom ℚ) = (n : ℚ) • P) → D ≤ n)
    (p : ℕ) (hp : p.Prime) (hpD : p ∣ D) :
    F.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hzero
  have hpcoeff : ∀ i : ℕ, (p : ℤ) ∣ F.coeff i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (F.coeff i) p).mp
    have h := congrArg (fun T : (ZMod p)[X] => T.coeff i) hzero
    simpa only [coeff_map, Int.coe_castRingHom, coeff_zero] using h
  obtain ⟨k, hDk⟩ := hpD
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    simp [hk0] at hDk
    omega
  have hklt : k < D := by nlinarith [hp.two_le]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨G, hFac⟩ := (C_dvd_iff_dvd_coeff (p : ℤ) F).mpr hpcoeff
  have hG : G.map (Int.castRingHom ℚ) = (k : ℚ) • P := by
    ext i
    apply mul_left_cancel₀ hpq
    have hi := congrArg (fun T : ℚ[X] => T.coeff i) hF
    simpa only [hFac, coeff_map, coeff_C_mul, coeff_smul,
      Int.coe_castRingHom, smul_eq_mul, Int.cast_mul, Int.cast_natCast,
      hDk, Nat.cast_mul, mul_assoc] using hi
  have hDle : D ≤ k := hmin k hkpos ⟨G, hG⟩
  omega

/-- Integer resultant values force the fixed-degree integer resultant to vanish
modulo a denominator prime.  The exponent is the SECOND nominal degree. -/
private lemma resultant_zero_mod_of_integral
    (P : ℚ[X]) (D : ℕ) (F : ℤ[X])
    (hF : F.map (Int.castRingHom ℚ) = (D : ℚ) • P)
    (p : ℕ) (hpD : p ∣ D) (R : ℤ[X]) (hm : 0 < R.natDegree)
    (z : ℤ)
    (hz : P.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) :
    (F.resultant R P.natDegree R.natDegree : ZMod p) = 0 := by
  have hFC : F.map (Int.castRingHom ℚ) = C (D : ℚ) * P :=
    hF.trans (rational_smul_eq_C_mul (D : ℚ) P)
  have hz' : P.resultant (R.map (Int.castRingHom ℚ))
      P.natDegree R.natDegree = (z : ℚ) := by
    simpa only [intMap_natDegree] using hz
  have hscale : (F.resultant R P.natDegree R.natDegree : ℚ) =
      (D : ℚ) ^ R.natDegree *
        P.resultant (R.map (Int.castRingHom ℚ)) P.natDegree R.natDegree := by
    calc
      (F.resultant R P.natDegree R.natDegree : ℚ) =
          (F.map (Int.castRingHom ℚ)).resultant
            (R.map (Int.castRingHom ℚ)) P.natDegree R.natDegree :=
        (resultant_map_map (f := F) (g := R)
          (m := P.natDegree) (n := R.natDegree) (Int.castRingHom ℚ)).symm
      _ = (D : ℚ) ^ R.natDegree *
          P.resultant (R.map (Int.castRingHom ℚ)) P.natDegree R.natDegree := by
        rw [hFC]
        exact resultant_C_mul_left (f := P) (g := R.map (Int.castRingHom ℚ))
          (m := P.natDegree) (n := R.natDegree) (D : ℚ)
  rw [hz'] at hscale
  have hZ : F.resultant R P.natDegree R.natDegree = (D : ℤ) ^ R.natDegree * z := by
    exact_mod_cast hscale
  have hDmod : ((D : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (D : ℤ) p).mpr (by exact_mod_cast hpD)
  rw [hZ, Int.cast_mul, Int.cast_pow, hDmod, zero_pow hm.ne', zero_mul]

private def throughDegree (F : ℤ[X]) (e : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (e + 1), monomial k (F.coeff k)

private lemma throughDegree_coeff (F : ℤ[X]) (e j : ℕ) :
    (throughDegree F e).coeff j = if j ≤ e then F.coeff j else 0 := by
  classical
  simp only [throughDegree, finsetSum_coeff, coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]

private lemma throughDegree_natDegree (F : ℤ[X]) (e : ℕ)
    (hFe : F.coeff e ≠ 0) : (throughDegree F e).natDegree = e := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [throughDegree_coeff, if_neg (not_le.mpr hj)]
  · rw [throughDegree_coeff, if_pos le_rfl]
    exact hFe

private lemma throughDegree_map {S : Type*} [Semiring S]
    (F : ℤ[X]) (ρ : ℤ →+* S) (e : ℕ)
    (he : (F.map ρ).natDegree = e) :
    (throughDegree F e).map ρ = F.map ρ := by
  ext j
  rw [coeff_map, throughDegree_coeff]
  by_cases hj : j ≤ e
  · rw [if_pos hj]
    exact (coeff_map (p := F) ρ j).symm
  · rw [if_neg hj, map_zero]
    symm
    exact coeff_eq_zero_of_natDegree_lt (by rw [he]; omega)

private lemma padded_constant_X_ne_zero {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) (he0 : f.natDegree = 0) (d : ℕ) :
    f.resultant (X : K[X]) d 1 ≠ 0 := by
  let c : K := f.coeff 0
  have hfconst : f = C c := eq_C_of_natDegree_eq_zero he0
  have hc : c ≠ 0 := by
    intro h
    apply hf
    rw [hfconst, h, C_0]
  have hconst : f.resultant (X : K[X]) d 1 = (-1) ^ d * c := by
    rw [hfconst]
    simpa using (resultant_C_left (g := (X : K[X])) (m := d) (n := 1) c)
  rw [hconst]
  exact mul_ne_zero (pow_ne_zero d (neg_ne_zero.mpr one_ne_zero)) hc

private lemma padded_self_add_one_ne_zero {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) (d : ℕ)
    (hdeg : f.natDegree < d) (he : 0 < f.natDegree) :
    f.resultant (f + 1) d f.natDegree ≠ 0 := by
  let e : ℕ := f.natDegree
  let c : K := f.coeff e
  have hc : c ≠ 0 := by
    change f.leadingCoeff ≠ 0
    exact leadingCoeff_ne_zero.mpr hf
  have hcore : f.resultant (f + 1) e e = c ^ e := by
    calc
      f.resultant (f + 1) e e = f.resultant (1 + f * 1) e e := by
        congr 1
        ring
      _ = f.resultant 1 e e :=
        resultant_add_mul_right (f := f) (g := 1) (p := 1)
          (m := e) (n := e) (by simp) (by exact le_rfl)
      _ = c ^ e :=
        resultant_one_right (f := f) (m := e) (n := e)
  have hcoeff : (f + 1).coeff e = c := by
    change (f + 1).coeff f.natDegree = f.coeff f.natDegree
    simp only [coeff_add, coeff_one, if_neg he.ne', add_zero]
  have hpad := resultant_add_left_deg (f := f) (g := f + 1)
    (m := e) (n := e) (k := d - e) (by exact le_rfl)
  have hsum : e + (d - e) = d := by dsimp [e]; omega
  rw [hsum, hcoeff, hcore] at hpad
  change f.resultant (f + 1) d e ≠ 0
  rw [hpad]
  exact mul_ne_zero
    (mul_ne_zero
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ hc))
    (pow_ne_zero _ hc)

/-- Integer resultants reflect a monic integer lift. The arbitrary integer test
polynomial is bounded by natural degree, with the boundary included. -/
theorem integerPolynomial_of_integral_resultants
    (χ : ℚ[X]) (hχ : χ.Monic)
    (hres : ∀ R : ℤ[X], R.natDegree ≤ χ.natDegree →
      ∃ z : ℤ, χ.resultant (R.map (Int.castRingHom ℚ)) = (z : ℚ)) :
    ∃ F : ℤ[X], F.Monic ∧ F.map (Int.castRingHom ℚ) = χ := by
  classical
  by_cases hd0 : χ.natDegree = 0
  · have hχone : χ = 1 := eq_one_of_monic_natDegree_zero hχ hd0
    exact ⟨1, by simp, by simp [hχone]⟩
  have hdpos : 0 < χ.natDegree := by omega
  let Clears : ℕ → Prop := fun n =>
    0 < n ∧ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = (n : ℚ) • χ
  have hEx : ∃ n, Clears n := exists_positive_clear χ
  let D : ℕ := Nat.find hEx
  have hWitness : Clears D := Nat.find_spec hEx
  obtain ⟨hD, F, hF⟩ := hWitness
  have hmin : ∀ n : ℕ, 0 < n →
      (∃ G : ℤ[X], G.map (Int.castRingHom ℚ) = (n : ℚ) • χ) → D ≤ n := by
    intro n hn hG
    exact Nat.find_min' hEx ⟨hn, hG⟩
  obtain ⟨hFdeg, hFlead⟩ := cleared_shape χ hχ D hD F hF
  have hDone : D = 1 := by
    by_contra hDn
    obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hDn
    letI : Fact p.Prime := ⟨hp⟩
    let ρ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
    let f : (ZMod p)[X] := F.map ρ
    let e : ℕ := f.natDegree
    have hf0 : f ≠ 0 := cleared_reduction_ne_zero χ D hD F hF hmin p hp hpD
    have hlead0 : ρ F.leadingCoeff = 0 := by
      change (F.leadingCoeff : ZMod p) = 0
      rw [hFlead]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (D : ℤ) p).mpr
        (by exact_mod_cast hpD)
    have he_lt : e < χ.natDegree := by
      have h := natDegree_map_lt (p := F) (f := ρ) hlead0 hf0
      simpa only [hFdeg] using h
    by_cases he0 : e = 0
    · obtain ⟨z, hz⟩ := hres (X : ℤ[X])
        (by simpa only [natDegree_X] using (Nat.succ_le_iff.mpr hdpos))
      have hzero := resultant_zero_mod_of_integral χ D F hF p hpD
        (X : ℤ[X]) (by simp) z hz
      have hzero' : ρ (F.resultant (X : ℤ[X]) χ.natDegree 1) = 0 := by
        simpa only [ρ, Int.coe_castRingHom, natDegree_X] using hzero
      have hmap := resultant_map_map (f := F) (g := (X : ℤ[X]))
        (m := χ.natDegree) (n := 1) ρ
      have hbad : f.resultant (X : (ZMod p)[X]) χ.natDegree 1 = 0 := by
        have h := hmap.trans hzero'
        rw [map_X] at h
        simpa only [f] using h
      exact padded_constant_X_ne_zero f hf0 he0 χ.natDegree hbad
    · have hepos : 0 < e := by omega
      have hc : f.coeff e ≠ 0 := by
        change f.leadingCoeff ≠ 0
        exact leadingCoeff_ne_zero.mpr hf0
      have hFe : F.coeff e ≠ 0 := by
        intro h
        apply hc
        change (F.map ρ).coeff e = 0
        rw [coeff_map, h, map_zero]
      let H : ℤ[X] := throughDegree F e
      let R : ℤ[X] := H + 1
      have hHdeg : H.natDegree = e := throughDegree_natDegree F e hFe
      have hRdeg : R.natDegree = e := by
        dsimp [R]
        rw [natDegree_add_one, hHdeg]
      have hHm : H.map ρ = f := throughDegree_map F ρ e rfl
      have hRm : R.map ρ = f + 1 := by
        dsimp [R]
        rw [Polynomial.map_add, Polynomial.map_one, hHm]
      obtain ⟨z, hz⟩ := hres R (by rw [hRdeg]; exact he_lt.le)
      have hzero := resultant_zero_mod_of_integral χ D F hF p hpD R
        (by rw [hRdeg]; exact hepos) z hz
      have hzero' : ρ (F.resultant R χ.natDegree e) = 0 := by
        simpa only [ρ, Int.coe_castRingHom, hRdeg] using hzero
      have hmap := resultant_map_map (f := F) (g := R)
        (m := χ.natDegree) (n := e) ρ
      have hbad : f.resultant (f + 1) χ.natDegree e = 0 := by
        have h := hmap.trans hzero'
        rw [hRm] at h
        simpa only [f] using h
      exact padded_self_add_one_ne_zero f hf0 χ.natDegree he_lt hepos hbad
  refine ⟨F, ?_, ?_⟩
  · change F.leadingCoeff = 1
    simpa only [hDone, Nat.cast_one] using hFlead
  · simpa only [hDone, Nat.cast_one, one_smul] using hF

end PrivateResultantIntegrality
