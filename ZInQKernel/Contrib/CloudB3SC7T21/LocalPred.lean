import ZInQKernel.Contrib.CloudB3SC7T21.Hurwitz
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# t21-proof: local conditions in `ℍ[ℚ_p]`

Task t21-proof. For a prime `p` and `ω ∈ ℍ[ℚ_p]` with `ω² = ω − 1`:
* `LocOK y`: `y ∈ ℚ_p^× · O_{B,p}^×` (`y = c u`, `u` Hurwitz-integral of unit norm);
* `InR ω u`: `u ∈ ℤ_p + ℤ_p ω + 4 O_{B,p}` (the order `R_p = O_{K,p} + 4O_{B,p}` of TYZ, L543–544);
* `Loc2OK ω y`: `y = c u` with `u ∈ R_p^×`.
Each is closed under products and inverses.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open scoped Quaternion

/-! ## Quaternions over a ring hom -/

/-- Coordinatewise image of quaternions under a ring hom. -/
def qmap {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : ℍ[A] →+* ℍ[B] where
  toFun q := ⟨f q.re, f q.imI, f q.imJ, f q.imK⟩
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext <;> simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, map_mul, map_add, map_sub]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

@[simp] theorem qmap_re {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : ℍ[A]) :
    (qmap f q).re = f q.re := rfl
@[simp] theorem qmap_imI {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : ℍ[A]) :
    (qmap f q).imI = f q.imI := rfl
@[simp] theorem qmap_imJ {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : ℍ[A]) :
    (qmap f q).imJ = f q.imJ := rfl
@[simp] theorem qmap_imK {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : ℍ[A]) :
    (qmap f q).imK = f q.imK := rfl

theorem qmap_coe {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    qmap f (a : ℍ[A]) = (f a : ℍ[B]) := by
  ext <;> simp

theorem qmap_star {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : ℍ[A]) :
    qmap f (star q) = star (qmap f q) := by
  ext <;> simp

theorem hc_qmap {A B : Type*} [Field A] [CharZero A] [Field B] [CharZero B] (f : A →+* B)
    (q : ℍ[A]) : hc (qmap f q) = mapH f (hc q) := by
  ext <;> simp [hc, mapH, map_ofNat]

/-- `B → ℍ[ℚ_p]`. -/
def qp (p : ℕ) [Fact p.Prime] : ℍ[ℚ] →+* ℍ[ℚ_[p]] := qmap (Rat.castHom ℚ_[p])

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ℤ_p ⊂ ℚ_p`. -/
abbrev Zp (p : ℕ) [Fact p.Prime] : Subring ℚ_[p] := PadicInt.subring p

theorem mem_Zp {x : ℚ_[p]} : x ∈ Zp p ↔ ‖x‖ ≤ 1 := Iff.rfl

/-- `y ∈ ℚ_p^× O_{B,p}^×`. -/
def LocOK (y : ℍ[ℚ_[p]]) : Prop :=
  ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ u : ℍ[ℚ_[p]], y = c • u ∧ IsHur (Zp p) u ∧ ‖Quaternion.normSq u‖ = 1

/-- `u ∈ ℤ_p + ℤ_p ω + 4 O_{B,p}`. -/
def InR (ω u : ℍ[ℚ_[p]]) : Prop :=
  ∃ x z : ℚ_[p], ‖x‖ ≤ 1 ∧ ‖z‖ ≤ 1 ∧ ∃ a : ℍ[ℚ_[p]], IsHur (Zp p) a ∧ u = x • 1 + z • ω + (4 : ℚ_[p]) • a

/-- `y ∈ ℚ_p^× R_p^×`. -/
def Loc2OK (ω y : ℍ[ℚ_[p]]) : Prop :=
  ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ u : ℍ[ℚ_[p]], y = c • u ∧ IsHur (Zp p) u ∧ ‖Quaternion.normSq u‖ = 1 ∧
    InR ω u

theorem four_mem : (4 : ℚ_[p]) ∈ Zp p := by
  simp

theorem LocOK.one : LocOK (1 : ℍ[ℚ_[p]]) :=
  ⟨1, one_ne_zero, 1, by simp, isHur_one, by simp⟩

theorem LocOK.mul {y z : ℍ[ℚ_[p]]} (hy : LocOK y) (hz : LocOK z) : LocOK (y * z) := by
  obtain ⟨c, hc, u, rfl, hu, hn⟩ := hy
  obtain ⟨c', hc', u', rfl, hu', hn'⟩ := hz
  refine ⟨c * c', mul_ne_zero hc hc', u * u', ?_, hu.mul hu', ?_⟩
  · rw [smul_mul_smul]
  · rw [map_mul, norm_mul, hn, hn', one_mul]

/-- The inverse of `c u`: `(c · nrd u)⁻¹ ū`. -/
theorem eq_of_mul_eq_one {c : ℚ_[p]} {u z : ℍ[ℚ_[p]]} (hc : c ≠ 0)
    (hn : Quaternion.normSq u ≠ 0) (h : (c • u) * z = 1) :
    z = c⁻¹ • ((Quaternion.normSq u)⁻¹ • star u) := by
  have h1 : star u * ((c • u) * z) = star u := by rw [h, mul_one]
  have h3 : star u * (c • u) = c • ((Quaternion.normSq u : ℚ_[p]) : ℍ[ℚ_[p]]) := by
    rw [Algebra.mul_smul_comm, Quaternion.star_mul_self]
  have h2 : (c • ((Quaternion.normSq u : ℚ_[p]) : ℍ[ℚ_[p]])) * z = (c * Quaternion.normSq u) • z := by
    rw [smul_mul_assoc, Quaternion.coe_mul_eq_smul, smul_smul]
  rw [← mul_assoc, h3, h2] at h1
  rw [← h1, smul_smul, smul_smul]
  have : c⁻¹ * ((Quaternion.normSq u)⁻¹ * (c * Quaternion.normSq u)) = 1 := by field_simp
  rw [← mul_assoc] at this
  rw [this, one_smul]

theorem normSq_inv_star {u : ℍ[ℚ_[p]]} (hn : ‖Quaternion.normSq u‖ = 1) :
    ‖Quaternion.normSq ((Quaternion.normSq u)⁻¹ • star u)‖ = 1 := by
  rw [Quaternion.normSq_smul, Quaternion.normSq_star, norm_mul, norm_pow, norm_inv, hn]
  simp

theorem isHur_inv_star {u : ℍ[ℚ_[p]]} (hu : IsHur (Zp p) u) (hn : ‖Quaternion.normSq u‖ = 1) :
    IsHur (Zp p) ((Quaternion.normSq u)⁻¹ • star u) :=
  IsHur.smul (by rw [mem_Zp, norm_inv, hn, inv_one]) hu.star

theorem normSq_ne_zero_of {u : ℍ[ℚ_[p]]} (hn : ‖Quaternion.normSq u‖ = 1) :
    Quaternion.normSq u ≠ 0 := by
  intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn

theorem LocOK.of_mul_eq_one {y z : ℍ[ℚ_[p]]} (hy : LocOK y) (h : y * z = 1) : LocOK z := by
  obtain ⟨c, hc, u, rfl, hu, hn⟩ := hy
  exact ⟨c⁻¹, inv_ne_zero hc, _, eq_of_mul_eq_one hc (normSq_ne_zero_of hn) h,
    isHur_inv_star hu hn, normSq_inv_star hn⟩

/-! ## The order `R_p` -/

section R

variable {ω : ℍ[ℚ_[p]]}

theorem InR.mul (hω : IsHur (Zp p) ω) (hω2 : ω * ω = ω - 1) {u u' : ℍ[ℚ_[p]]}
    (hu : InR ω u) (hu' : InR ω u') (hhu' : IsHur (Zp p) u') : InR ω (u * u') := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  obtain ⟨x', z', hx', hz', a', ha', rfl⟩ := hu'
  have hxz : IsHur (Zp p) (x • (1 : ℍ[ℚ_[p]]) + z • ω) :=
    (isHur_one.smul (mem_Zp.mpr hx)).add (hω.smul (mem_Zp.mpr hz))
  refine ⟨x * x' - z * z', x * z' + z * x' + z * z', ?_, ?_,
    (x • (1 : ℍ[ℚ_[p]]) + z • ω) * a' + a * (x' • 1 + z' • ω + (4 : ℚ_[p]) • a'),
    (hxz.mul ha').add (ha.mul hhu'), ?_⟩
  · have := (Zp p).sub_mem ((Zp p).mul_mem (mem_Zp.mpr hx) (mem_Zp.mpr hx'))
      ((Zp p).mul_mem (mem_Zp.mpr hz) (mem_Zp.mpr hz'))
    exact this
  · have := (Zp p).add_mem ((Zp p).add_mem ((Zp p).mul_mem (mem_Zp.mpr hx) (mem_Zp.mpr hz'))
      ((Zp p).mul_mem (mem_Zp.mpr hz) (mem_Zp.mpr hx'))) ((Zp p).mul_mem (mem_Zp.mpr hz) (mem_Zp.mpr hz'))
    exact this
  · have e1 : (x • (1 : ℍ[ℚ_[p]]) + z • ω) * (x' • 1 + z' • ω) =
        (x * x' - z * z') • 1 + (x * z' + z * x' + z * z') • ω := by
      simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hω2]
      module
    rw [smul_add, mul_add, add_mul, mul_add, add_mul, ← e1]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, mul_add, add_mul]
    module

theorem InR.smul {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) {u : ℍ[ℚ_[p]]} (hu : InR ω u) : InR ω (c • u) := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  refine ⟨c * x, c * z, ?_, ?_, c • a, ha.smul (mem_Zp.mpr hc), ?_⟩
  · rw [norm_mul]; nlinarith [norm_nonneg c, norm_nonneg x]
  · rw [norm_mul]; nlinarith [norm_nonneg c, norm_nonneg z]
  · simp only [smul_add, smul_smul]; rw [mul_comm c 4]

theorem InR.star (hstar : star ω = 1 - ω) {u : ℍ[ℚ_[p]]} (hu : InR ω u) : InR ω (star u) := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  refine ⟨x + z, -z, ?_, by rwa [norm_neg], Star.star a, ha.star, ?_⟩
  · exact (Padic.nonarchimedean x z).trans (max_le hx hz)
  · simp only [star_add, Quaternion.star_smul, star_one, hstar]
    module

theorem InR.isHur (hω : IsHur (Zp p) ω) {u : ℍ[ℚ_[p]]} (hu : InR ω u) : IsHur (Zp p) u := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  exact ((isHur_one.smul (mem_Zp.mpr hx)).add (hω.smul (mem_Zp.mpr hz))).add (ha.smul four_mem)

theorem InR.one : InR ω (1 : ℍ[ℚ_[p]]) :=
  ⟨1, 0, by simp, by simp, 0, isHur_zero, by simp⟩

theorem Loc2OK.one : Loc2OK ω (1 : ℍ[ℚ_[p]]) :=
  ⟨1, one_ne_zero, 1, by simp, isHur_one, by simp, InR.one⟩

theorem Loc2OK.mul (hω : IsHur (Zp p) ω) (hω2 : ω * ω = ω - 1) {y z : ℍ[ℚ_[p]]}
    (hy : Loc2OK ω y) (hz : Loc2OK ω z) : Loc2OK ω (y * z) := by
  obtain ⟨c, hc, u, rfl, hu, hn, hR⟩ := hy
  obtain ⟨c', hc', u', rfl, hu', hn', hR'⟩ := hz
  refine ⟨c * c', mul_ne_zero hc hc', u * u', ?_, hu.mul hu', ?_, hR.mul hω hω2 hR' hu'⟩
  · rw [smul_mul_smul]
  · rw [map_mul, norm_mul, hn, hn', one_mul]

theorem Loc2OK.of_mul_eq_one (hstar : star ω = 1 - ω) {y z : ℍ[ℚ_[p]]} (hy : Loc2OK ω y)
    (h : y * z = 1) : Loc2OK ω z := by
  obtain ⟨c, hc, u, rfl, hu, hn, hR⟩ := hy
  refine ⟨c⁻¹, inv_ne_zero hc, _, eq_of_mul_eq_one hc (normSq_ne_zero_of hn) h,
    isHur_inv_star hu hn, normSq_inv_star hn, (hR.star hstar).smul ?_⟩
  rw [norm_inv, hn, inv_one]

end R

end ZInQ.Contrib.T21Proof
