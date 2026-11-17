import Mathlib.Algebra.Quaternion
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic

/-!
# Integral quaternion primitives for the squarefree Jones–Pall specialization

These primitives use Mathlib's actual Hamilton basis and conjugation. They do not
assume a norm-divisor theorem or the desired ternary representation.
- computation/finite residue proofs use kernel-checked `decide`, never native_decide;
- no target definition, dependency, or configuration is changed.
-/

namespace ZInQ.Contrib.OneProof.JonesPall

open scoped Quaternion

abbrev Q := ℍ[ℤ]

/-- Coordinatewise divisibility of an integral quaternion. -/
def DvdQ (d : ℤ) (q : Q) : Prop :=
  d ∣ q.re ∧ d ∣ q.imI ∧ d ∣ q.imJ ∧ d ∣ q.imK

/-- Exact coordinatewise division when `DvdQ d q` holds. -/
def divQ (d : ℤ) (q : Q) : Q :=
  ⟨q.re / d, q.imI / d, q.imJ / d, q.imK / d⟩

theorem smul_divQ {d : ℤ} {q : Q} (h : DvdQ d q) : d • divQ d q = q := by
  apply Quaternion.ext <;>
    simp only [divQ, Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul]
  · exact Int.mul_ediv_cancel' h.1
  · exact Int.mul_ediv_cancel' h.2.1
  · exact Int.mul_ediv_cancel' h.2.2.1
  · exact Int.mul_ediv_cancel' h.2.2.2

theorem dvdQ_iff_exists_smul {d : ℤ} {q : Q} : DvdQ d q ↔ ∃ u : Q, q = d • u := by
  constructor
  · intro h
    exact ⟨divQ d q, (smul_divQ h).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨⟨u.re, rfl⟩, ⟨u.imI, rfl⟩, ⟨u.imJ, rfl⟩, ⟨u.imK, rfl⟩⟩

theorem dvdQ_mul_right {d : ℤ} {q : Q} (h : DvdQ d q) (v : Q) : DvdQ d (q * v) := by
  obtain ⟨u, rfl⟩ := dvdQ_iff_exists_smul.mp h
  apply dvdQ_iff_exists_smul.mpr
  exact ⟨u * v, smul_mul_assoc d u v⟩

theorem dvdQ_mul_left {d : ℤ} {q : Q} (h : DvdQ d q) (v : Q) : DvdQ d (v * q) := by
  obtain ⟨u, rfl⟩ := dvdQ_iff_exists_smul.mp h
  apply dvdQ_iff_exists_smul.mpr
  exact ⟨v * u, mul_smul_comm d v u⟩

theorem dvdQ_of_smul {p d : ℤ} (hp : Prime p) (hd : ¬ p ∣ d) {q : Q}
    (h : DvdQ p (d • q)) : DvdQ p q := by
  have cancel : ∀ x : ℤ, p ∣ d * x → p ∣ x := fun x hx =>
    (hp.dvd_or_dvd hx).resolve_left hd
  exact ⟨cancel _ h.1, cancel _ h.2.1, cancel _ h.2.2.1, cancel _ h.2.2.2⟩

theorem dvdQ_add {d : ℤ} {q r : Q} (hq : DvdQ d q) (hr : DvdQ d r) :
    DvdQ d (q + r) :=
  ⟨hq.1.add hr.1, hq.2.1.add hr.2.1, hq.2.2.1.add hr.2.2.1, hq.2.2.2.add hr.2.2.2⟩

theorem dvdQ_sub {d : ℤ} {q r : Q} (hq : DvdQ d q) (hr : DvdQ d r) :
    DvdQ d (q - r) :=
  ⟨hq.1.sub hr.1, hq.2.1.sub hr.2.1, hq.2.2.1.sub hr.2.2.1, hq.2.2.2.sub hr.2.2.2⟩

theorem dvdQ_star {d : ℤ} {q : Q} (h : DvdQ d q) : DvdQ d (star q) := by
  simpa only [DvdQ, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
    Quaternion.imK_star, dvd_neg] using h

theorem dvdQ_coe {d x : ℤ} (h : d ∣ x) : DvdQ d (x : Q) :=
  ⟨h, dvd_zero _, dvd_zero _, dvd_zero _⟩

theorem normSq_divQ {d : ℤ} {q : Q} (h : DvdQ d q) :
    d ^ 2 * Quaternion.normSq (divQ d q) = Quaternion.normSq q := by
  calc
    d ^ 2 * Quaternion.normSq (divQ d q) = Quaternion.normSq (d • divQ d q) :=
      (Quaternion.normSq_smul d _).symm
    _ = Quaternion.normSq q := congrArg Quaternion.normSq (smul_divQ h)

/-- Division by a scalar prime to p preserves the left ideal q*v = 0 modulo p. -/
theorem divQ_preserves_annihilator {p d : ℤ} (hp : Prime p) (hd : ¬ p ∣ d)
    {q v a : Q} (hq : DvdQ p (q * v)) (hdiv : DvdQ d (a * q)) :
    DvdQ p (divQ d (a * q) * v) := by
  have h := dvdQ_mul_left hq a
  have e : d • (divQ d (a * q) * v) = a * (q * v) := by
    rw [← smul_mul_assoc, smul_divQ hdiv, mul_assoc]
  rw [← e] at h
  exact dvdQ_of_smul hp hd h

private theorem pair_even {x y : ℤ} (h : (x : ZMod 2) = (y : ZMod 2)) :
    (2 : ℤ) ∣ x - y ∧ (2 : ℤ) ∣ x + y := by
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) 2).mp
    push_cast
    rw [h]
    simp
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) 2).mp
    push_cast
    rw [h, ← two_mul]
    simp only [show (2 : ZMod 2) = 0 from rfl, zero_mul]

/-- The even-norm halving multiplier can always be chosen on the LEFT. -/
theorem exists_halving_multiplier (q : Q) (h : (2 : ℤ) ∣ Quaternion.normSq q) :
    ∃ u : Q, Quaternion.normSq u = 2 ∧ DvdQ 2 (u * q) := by
  have table : ∀ a b c d : ZMod 2,
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0 →
        (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    decide
  have hz : (q.re : ZMod 2) ^ 2 + (q.imI : ZMod 2) ^ 2 +
      (q.imJ : ZMod 2) ^ 2 + (q.imK : ZMod 2) ^ 2 = 0 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (Quaternion.normSq q) 2).mpr h
    simpa only [Quaternion.normSq_def', Int.cast_add, Int.cast_pow] using hh
  rcases table _ _ _ _ hz with hI | hJ | hK
  · obtain ⟨hab, hab'⟩ := pair_even hI.1
    obtain ⟨hcd, hcd'⟩ := pair_even hI.2
    refine ⟨⟨1, 1, 0, 0⟩, by norm_num [Quaternion.normSq_def'], ?_⟩
    simpa [DvdQ, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, add_comm, sub_eq_add_neg] using And.intro hab (And.intro hab' (And.intro hcd hcd'))
  · obtain ⟨hac, hac'⟩ := pair_even hJ.1
    obtain ⟨hbd, hbd'⟩ := pair_even hJ.2
    refine ⟨⟨1, 0, 1, 0⟩, by norm_num [Quaternion.normSq_def'], ?_⟩
    have hdb : (2 : ℤ) ∣ q.imK - q.imI := by
      simpa only [neg_sub] using (dvd_neg.mpr hbd)
    simpa [DvdQ, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, add_comm, sub_eq_add_neg] using And.intro hac (And.intro hbd' (And.intro hac' hdb))
  · obtain ⟨had, had'⟩ := pair_even hK.1
    obtain ⟨hbc, hbc'⟩ := pair_even hK.2
    refine ⟨⟨1, 0, 0, 1⟩, by norm_num [Quaternion.normSq_def'], ?_⟩
    simpa [DvdQ, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, add_comm, sub_eq_add_neg] using And.intro had (And.intro hbc (And.intro hbc' had'))

end ZInQ.Contrib.OneProof.JonesPall
