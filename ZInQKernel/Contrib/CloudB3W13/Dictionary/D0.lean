/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import Mathlib

/-!
# W13 dictionary D0: the residue characteristics `2`, `3` are invertible in `ℤ_(p)` for `p > 3`

Stated for `Localization.AtPrime (Ideal.span {(p : ℤ)})`, which is the kernel's `Zloc p`
(`ZInQKernel/OneProof/H/TailL.lean`: `pIdeal p := Ideal.span {(p : ℤ)}`,
`Zloc p := Localization.AtPrime (pIdeal p)`), so that this file does not import the `OneProof` cone.
-/

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

theorem d0_isUnit_natCast (p : ℕ) [Fact p.Prime] [(Ideal.span {(p : ℤ)}).IsPrime] {n : ℕ}
    (hn : ¬ p ∣ n) : IsUnit ((n : ℤ) : Localization.AtPrime (Ideal.span {(p : ℤ)})) := by
  have h := (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime (Ideal.span {(p : ℤ)})) (Ideal.span {(p : ℤ)}) (n : ℤ)).2
  rw [map_natCast] at h
  push_cast
  refine h ?_
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
  exact fun hd => hn (Int.natCast_dvd_natCast.1 hd)

/-- **D0.** For a prime `p > 3`, `2`, `3` and `6` are units of `ℤ_(p)`. -/
theorem d0_units (p : ℕ) [hp : Fact p.Prime] [(Ideal.span {(p : ℤ)}).IsPrime] (h3 : 3 < p) :
    IsUnit (2 : Localization.AtPrime (Ideal.span {(p : ℤ)})) ∧
      IsUnit (3 : Localization.AtPrime (Ideal.span {(p : ℤ)})) ∧
      IsUnit (6 : Localization.AtPrime (Ideal.span {(p : ℤ)})) := by
  have hnd : ∀ n : ℕ, 0 < n → n ≤ 3 → ¬ p ∣ n := fun n h0 hn hd =>
    absurd (Nat.le_of_dvd h0 hd) (by omega)
  have h2 := d0_isUnit_natCast p (hnd 2 (by norm_num) (by norm_num))
  have h3' := d0_isUnit_natCast p (hnd 3 (by norm_num) (by norm_num))
  push_cast at h2 h3'
  refine ⟨h2, h3', ?_⟩
  have : (6 : Localization.AtPrime (Ideal.span {(p : ℤ)})) = 2 * 3 := by norm_num
  rw [this]
  exact h2.mul h3'

end ZInQ.Contrib.CloudB2Shimura.Dictionary
