/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.Data.Nat.Prime.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.Data.Nat.Prime.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.Data.Nat.Prime.Basic

/-! # `gcd`/`lcm` with `q * n` for a prime `q` (backport) -/

public section

theorem Nat.Prime.gcd_mul_eq_of_dvd_of_not_mul_dvd {q n m : ℕ} (hq : q.Prime) (hnm : n ∣ m)
    (hqnm : ¬q * n ∣ m) : Nat.gcd m (q * n) = n := by
  obtain ⟨t, rfl⟩ := hnm
  have hqt : Nat.Coprime t q := Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hq).mpr
    fun h ↦ hqnm (by rw [mul_comm q n]; exact mul_dvd_mul_left n h)
  rw [mul_comm q n, Nat.gcd_mul_left, hqt.gcd_eq_one, mul_one]

/-- If `n ∣ m` and `q * n ∤ m` for a prime `q`, then `lcm m (q * n) = q * m`. -/
theorem Nat.Prime.lcm_mul_eq_of_dvd_of_not_mul_dvd {q n m : ℕ} (hq : q.Prime) (hnm : n ∣ m)
    (hqnm : ¬q * n ∣ m) : Nat.lcm m (q * n) = q * m := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hqnm (by simpa using hnm)
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) ?_
  have := Nat.gcd_mul_lcm m (q * n)
  rw [hq.gcd_mul_eq_of_dvd_of_not_mul_dvd hnm hqnm] at this
  rw [this, Nat.mul_left_comm, Nat.mul_comm m, Nat.mul_left_comm]
