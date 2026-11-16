import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# t21-proof: Hurwitz coordinates

Task t21-proof (report `docs/research/t21-proof.md`). Generic algebra of the Hurwitz order
`O_B = ℤ + ℤi + ℤj + ℤζ`, `ζ = (−1 + i + j + k)/2`, in Hamilton's quaternions `ℍ[R]` over a field
of characteristic zero: Hurwitz coordinates `hc`, the multiplication, conjugation and norm in these
coordinates (integer polynomials, `mulH`, `starH`, `nrdH`, valid over any commutative ring), and the
predicate `IsHur S y` (all Hurwitz coordinates in a subring `S`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Contrib.T21Proof

open scoped Quaternion

/-! ## Four coordinates -/

/-- Four coordinates (Hurwitz coordinates of a quaternion). -/
@[ext]
structure H4 (A : Type*) where
  a0 : A
  a1 : A
  a2 : A
  a3 : A
deriving DecidableEq

section Poly

variable {A : Type*} [CommRing A]

/-- Multiplication in Hurwitz coordinates. -/
def mulH (a b : H4 A) : H4 A where
  a0 := -a.a3 * b.a3 - a.a3 * b.a1 - a.a2 * b.a3 - a.a2 * b.a2 - a.a2 * b.a1 + a.a1 * b.a2 -
    a.a1 * b.a1 + a.a0 * b.a0
  a1 := -a.a3 * b.a2 + a.a2 * b.a3 + a.a2 * b.a1 - a.a1 * b.a3 - a.a1 * b.a2 + a.a1 * b.a0 +
    a.a0 * b.a1
  a2 := -a.a3 * b.a2 + a.a3 * b.a1 + a.a2 * b.a1 + a.a2 * b.a0 - a.a1 * b.a3 - a.a1 * b.a2 +
    a.a0 * b.a2
  a3 := -a.a3 * b.a3 + a.a3 * b.a2 - a.a3 * b.a1 + a.a3 * b.a0 - a.a2 * b.a3 - 2 * a.a2 * b.a1 +
    a.a1 * b.a3 + 2 * a.a1 * b.a2 + a.a0 * b.a3

/-- Conjugation in Hurwitz coordinates. -/
def starH (a : H4 A) : H4 A := ⟨a.a0 - a.a3, -a.a1, -a.a2, -a.a3⟩

/-- The reduced norm in Hurwitz coordinates. -/
def nrdH (a : H4 A) : A :=
  a.a3 ^ 2 + a.a2 * a.a3 + a.a2 ^ 2 + a.a1 * a.a3 + a.a1 ^ 2 - a.a0 * a.a3 + a.a0 ^ 2

/-- Coordinatewise image under a ring hom. -/
def mapH {B : Type*} [CommRing B] (f : A →+* B) (a : H4 A) : H4 B :=
  ⟨f a.a0, f a.a1, f a.a2, f a.a3⟩

theorem mapH_mulH {B : Type*} [CommRing B] (f : A →+* B) (a b : H4 A) :
    mapH f (mulH a b) = mulH (mapH f a) (mapH f b) := by
  ext <;> simp [mapH, mulH, map_ofNat]

theorem mapH_starH {B : Type*} [CommRing B] (f : A →+* B) (a : H4 A) :
    mapH f (starH a) = starH (mapH f a) := by
  ext <;> simp [mapH, starH]

theorem map_nrdH {B : Type*} [CommRing B] (f : A →+* B) (a : H4 A) :
    f (nrdH a) = nrdH (mapH f a) := by
  simp [mapH, nrdH]

end Poly

/-! ## Hurwitz coordinates of a quaternion -/

section Field

variable {R : Type*} [Field R] [CharZero R]

/-- The Hurwitz coordinates of `y`: `y = x₀ + x₁ i + x₂ j + x₃ ζ`. -/
def hc (y : ℍ[R]) : H4 R := ⟨y.re + y.imK, y.imI - y.imK, y.imJ - y.imK, 2 * y.imK⟩

/-- The quaternion with Hurwitz coordinates `x`. -/
def hur (x : H4 R) : ℍ[R] := ⟨x.a0 - x.a3 / 2, x.a1 + x.a3 / 2, x.a2 + x.a3 / 2, x.a3 / 2⟩

theorem hur_hc (y : ℍ[R]) : hur (hc y) = y := by
  ext <;> simp [hur, hc] <;> ring

theorem hc_hur (x : H4 R) : hc (hur x) = x := by
  ext <;> simp [hur, hc] <;> ring

theorem hc_injective : Function.Injective (hc : ℍ[R] → H4 R) := fun y z h => by
  rw [← hur_hc y, h, hur_hc]

theorem hc_mul (y z : ℍ[R]) : hc (y * z) = mulH (hc y) (hc z) := by
  ext <;> simp [hc, mulH] <;> ring

theorem hc_star (y : ℍ[R]) : hc (star y) = starH (hc y) := by
  ext <;> simp [hc, starH] <;> ring

theorem normSq_eq_nrdH (y : ℍ[R]) : Quaternion.normSq y = nrdH (hc y) := by
  rw [Quaternion.normSq_def']
  simp [hc, nrdH]
  ring

theorem hc_add (y z : ℍ[R]) : hc (y + z) = ⟨(hc y).a0 + (hc z).a0, (hc y).a1 + (hc z).a1,
    (hc y).a2 + (hc z).a2, (hc y).a3 + (hc z).a3⟩ := by
  ext <;> simp [hc] <;> ring

theorem hc_sub (y z : ℍ[R]) : hc (y - z) = ⟨(hc y).a0 - (hc z).a0, (hc y).a1 - (hc z).a1,
    (hc y).a2 - (hc z).a2, (hc y).a3 - (hc z).a3⟩ := by
  ext <;> simp [hc] <;> ring

theorem hc_smul (c : R) (y : ℍ[R]) : hc (c • y) = ⟨c * (hc y).a0, c * (hc y).a1,
    c * (hc y).a2, c * (hc y).a3⟩ := by
  ext <;> simp [hc] <;> ring

theorem hc_one : hc (1 : ℍ[R]) = ⟨1, 0, 0, 0⟩ := by
  ext <;> simp [hc]

theorem hc_coe (c : R) : hc (c : ℍ[R]) = ⟨c, 0, 0, 0⟩ := by
  ext <;> simp [hc]

/-- All Hurwitz coordinates lie in the subring `S`. -/
def IsHur (S : Subring R) (y : ℍ[R]) : Prop :=
  (hc y).a0 ∈ S ∧ (hc y).a1 ∈ S ∧ (hc y).a2 ∈ S ∧ (hc y).a3 ∈ S

variable {S : Subring R}

theorem isHur_iff {y : ℍ[R]} : IsHur S y ↔ ∃ a : H4 S, hc y = mapH S.subtype a := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨⟨⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩, rfl⟩
  · rintro ⟨a, ha⟩
    simp only [IsHur, ha, mapH, Subring.coe_subtype]
    exact ⟨a.a0.2, a.a1.2, a.a2.2, a.a3.2⟩

theorem IsHur.mul {y z : ℍ[R]} (hy : IsHur S y) (hz : IsHur S z) : IsHur S (y * z) := by
  obtain ⟨a, ha⟩ := isHur_iff.mp hy
  obtain ⟨b, hb⟩ := isHur_iff.mp hz
  exact isHur_iff.mpr ⟨mulH a b, by rw [hc_mul, ha, hb, mapH_mulH]⟩

theorem IsHur.star {y : ℍ[R]} (hy : IsHur S y) : IsHur S (star y) := by
  obtain ⟨a, ha⟩ := isHur_iff.mp hy
  exact isHur_iff.mpr ⟨starH a, by rw [hc_star, ha, mapH_starH]⟩

theorem IsHur.normSq_mem {y : ℍ[R]} (hy : IsHur S y) : Quaternion.normSq y ∈ S := by
  obtain ⟨a, ha⟩ := isHur_iff.mp hy
  rw [normSq_eq_nrdH, ha, ← map_nrdH]
  exact (nrdH a).2

theorem IsHur.add {y z : ℍ[R]} (hy : IsHur S y) (hz : IsHur S z) : IsHur S (y + z) := by
  obtain ⟨h0, h1, h2, h3⟩ := hy
  obtain ⟨k0, k1, k2, k3⟩ := hz
  simp only [IsHur, hc_add]
  exact ⟨S.add_mem h0 k0, S.add_mem h1 k1, S.add_mem h2 k2, S.add_mem h3 k3⟩

theorem IsHur.sub {y z : ℍ[R]} (hy : IsHur S y) (hz : IsHur S z) : IsHur S (y - z) := by
  obtain ⟨h0, h1, h2, h3⟩ := hy
  obtain ⟨k0, k1, k2, k3⟩ := hz
  simp only [IsHur, hc_sub]
  exact ⟨S.sub_mem h0 k0, S.sub_mem h1 k1, S.sub_mem h2 k2, S.sub_mem h3 k3⟩

theorem IsHur.smul {c : R} (hc' : c ∈ S) {y : ℍ[R]} (hy : IsHur S y) : IsHur S (c • y) := by
  obtain ⟨h0, h1, h2, h3⟩ := hy
  simp only [IsHur, hc_smul]
  exact ⟨S.mul_mem hc' h0, S.mul_mem hc' h1, S.mul_mem hc' h2, S.mul_mem hc' h3⟩

theorem isHur_coe {c : R} (hc' : c ∈ S) : IsHur S (c : ℍ[R]) := by
  simp only [IsHur, hc_coe]
  exact ⟨hc', S.zero_mem, S.zero_mem, S.zero_mem⟩

theorem isHur_one : IsHur S (1 : ℍ[R]) := by
  simp only [IsHur, hc_one]
  exact ⟨S.one_mem, S.zero_mem, S.zero_mem, S.zero_mem⟩

theorem isHur_zero : IsHur S (0 : ℍ[R]) := by
  simpa using isHur_coe (S := S) S.zero_mem

end Field

/-! ## Integer Hurwitz coordinates -/

section Int

theorem nrdH_mulH {A : Type*} [CommRing A] (a b : H4 A) : nrdH (mulH a b) = nrdH a * nrdH b := by
  simp only [nrdH, mulH]; ring

theorem mulH_assoc {A : Type*} [CommRing A] (a b c : H4 A) :
    mulH (mulH a b) c = mulH a (mulH b c) := by
  ext <;> simp only [mulH] <;> ring

/-- `1 + i` in Hurwitz coordinates. -/
def oneI : H4 ℤ := ⟨1, 1, 0, 0⟩

/-- `i` in Hurwitz coordinates. -/
def qI : H4 ℤ := ⟨0, 1, 0, 0⟩

/-- Scalar multiplication by an integer. -/
def smulH (n : ℤ) (a : H4 ℤ) : H4 ℤ := ⟨n * a.a0, n * a.a1, n * a.a2, n * a.a3⟩

theorem nrdH_smulH (n : ℤ) (a : H4 ℤ) : nrdH (smulH n a) = n ^ 2 * nrdH a := by
  simp only [nrdH, smulH]; ring

/-- Mod 2: an element of even norm is killed by `1 − i`. -/
theorem mod_two_check : ∀ a0 a1 a2 a3 : ZMod 2, nrdH (⟨a0, a1, a2, a3⟩ : H4 (ZMod 2)) = 0 →
    mulH ⟨1, -1, 0, 0⟩ (⟨a0, a1, a2, a3⟩ : H4 (ZMod 2)) = ⟨0, 0, 0, 0⟩ := by
  decide

theorem even_of_cast_zero {n : ℤ} (h : ((n : ZMod 2)) = 0) : ∃ m, n = 2 * m := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨m, hm⟩ := h
  exact ⟨m, hm⟩

/-- **Divisibility by `1 + i`**: an integral Hurwitz element of even norm is `(1 + i) b`. -/
theorem exists_oneI_mul {a : H4 ℤ} (ha : Even (nrdH a)) : ∃ b, a = mulH oneI b := by
  have h0 : nrdH (mapH (Int.castRingHom (ZMod 2)) a) = 0 := by
    rw [← map_nrdH]; obtain ⟨r, hr⟩ := ha
    rw [hr]; simp only [map_add, eq_intCast]; rw [← two_mul]; push_cast
    rw [show ((2 : ZMod 2)) = 0 from rfl, zero_mul]
  have hm := mod_two_check _ _ _ _ h0
  have hz : mapH (Int.castRingHom (ZMod 2)) (mulH ⟨1, -1, 0, 0⟩ a) = ⟨0, 0, 0, 0⟩ := by
    rw [mapH_mulH]; convert hm using 2
    simp [mapH]
    rfl
  generalize hc' : mulH ⟨1, -1, 0, 0⟩ a = c at hz
  simp only [mapH, H4.mk.injEq, eq_intCast] at hz
  obtain ⟨m0, e0⟩ := even_of_cast_zero hz.1
  obtain ⟨m1, e1⟩ := even_of_cast_zero hz.2.1
  obtain ⟨m2, e2⟩ := even_of_cast_zero hz.2.2.1
  obtain ⟨m3, e3⟩ := even_of_cast_zero hz.2.2.2
  refine ⟨⟨m0, m1, m2, m3⟩, ?_⟩
  -- `(1 + i)(1 − i) a = 2 a`
  have h2 : mulH oneI c = smulH 2 a := by
    rw [← hc']; ext <;> simp only [mulH, oneI, smulH] <;> ring
  have hcm : c = smulH 2 ⟨m0, m1, m2, m3⟩ := by
    ext
    · exact e0
    · exact e1
    · exact e2
    · exact e3
  rw [hcm] at h2
  have h3 : mulH oneI (smulH 2 ⟨m0, m1, m2, m3⟩) = smulH 2 (mulH oneI ⟨m0, m1, m2, m3⟩) := by
    ext <;> simp only [mulH, oneI, smulH] <;> ring
  rw [h3] at h2
  simp only [smulH, H4.mk.injEq] at h2
  ext
  · linarith [h2.1]
  · linarith [h2.2.1]
  · linarith [h2.2.2.1]
  · linarith [h2.2.2.2]

/-- **Elements of norm `4^m` are `2^m` times a unit.** -/
theorem eq_smul_unit_of_nrdH (m : ℕ) : ∀ a : H4 ℤ, nrdH a = 4 ^ m →
    ∃ μ : H4 ℤ, nrdH μ = 1 ∧ a = smulH (2 ^ m) μ := by
  induction m with
  | zero => intro a ha; exact ⟨a, by simpa using ha, by ext <;> simp [smulH]⟩
  | succ m ih =>
    intro a ha
    have hev : Even (nrdH a) := ⟨2 * 4 ^ m, by rw [ha]; ring⟩
    obtain ⟨b, rfl⟩ := exists_oneI_mul hev
    have hnb : nrdH b = 2 * 4 ^ m := by
      rw [nrdH_mulH, show nrdH oneI = 2 from rfl] at ha
      have : (2 : ℤ) * nrdH b = 2 * (2 * 4 ^ m) := by rw [ha]; ring
      linarith
    obtain ⟨c, rfl⟩ := exists_oneI_mul ⟨4 ^ m, by rw [hnb]; ring⟩
    have hnc : nrdH (mulH qI c) = 4 ^ m := by
      rw [nrdH_mulH, show nrdH qI = 1 from rfl, one_mul]
      rw [nrdH_mulH, show nrdH oneI = 2 from rfl] at hnb
      linarith
    obtain ⟨μ, hμ, hμe⟩ := ih _ hnc
    refine ⟨μ, hμ, ?_⟩
    have : mulH oneI (mulH oneI c) = smulH 2 (mulH qI c) := by
      ext <;> simp only [mulH, oneI, qI, smulH] <;> ring
    rw [this, hμe]
    ext <;> simp only [smulH] <;> ring

end Int

end ZInQ.Contrib.T21Proof
