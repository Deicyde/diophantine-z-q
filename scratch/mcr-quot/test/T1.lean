import ZInQKernel.HDecomp.QM.Structures
open LeafQM
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [nrdZ, mulCoord]
  ring

/-- **The unit table** (computed by `py/units.py`): every class of `(ℤ/3)⁴` of nonzero norm mod 3
contains a unit `ofInt n` of `𝒪` (inverse `ofInt m`). -/
theorem unit_table : ∀ a b c d : ZMod 3,
    a ^ 2 + a * c + c ^ 2 - 2 * b ^ 2 - 2 * b * d - 2 * d ^ 2 ≠ 0 →
    ∃ n m : Fin 4 → ℤ, mulCoord n m = ![1, 0, 0, 0] ∧ mulCoord m n = ![1, 0, 0, 0] ∧
      ((n 0 : ℤ) : ZMod 3) = a ∧ ((n 1 : ℤ) : ZMod 3) = b ∧ ((n 2 : ℤ) : ZMod 3) = c ∧
      ((n 3 : ℤ) : ZMod 3) = d := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, 0, 0, -2], ![-3, 0, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 0, 0, 2], ![-3, 0, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 0], ![1, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, 1], ![-1, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, 1, -1], ![-1, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 0], ![-1, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, 1], ![1, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 0, -1, -1], ![1, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -2, 0, 0], ![-3, 2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-3, -2, 0, 2], ![-3, 2, 0, -2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, 0], ![-1, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 1, 1, 1], ![-2, -1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, 1, -1], ![-1, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, 0], ![1, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, 1, -1, 1], ![2, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, 1, -1, -1], ![1, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, 0], ![-3, -2, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, 2, 0, -2], ![-3, -2, 0, 2], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![0, -1, 1, 0], ![-1, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, 1, 1], ![-1, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-3, -1, 1, -1], ![-2, 1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 0], ![1, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![0, -1, -1, 1], ![1, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![3, -1, -1, -1], ![2, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 0], ![1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, 1], ![-1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 0, -1], ![-1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 0, 1, 1], ![2, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, 1, -1], ![2, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 0], ![0, 0, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, 1], ![0, 0, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 0, -1, -1], ![0, 0, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, 0], ![-1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -3, 1], ![-2, -1, 3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 0, -1], ![-1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, 1, 0], ![2, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, 1, 1, -1], ![2, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, 0], ![0, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, 1, -1, 1], ![-3, -1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, 1, -1, -1], ![0, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 0], ![-1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 0, 1], ![-1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -3, -1], ![-2, 1, 3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 0], ![2, 1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, 1, 1], ![2, 1, -1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![1, -1, -1, 0], ![0, -1, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![1, -1, -1, 1], ![0, -1, -1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-2, -1, -1, -1], ![-3, 1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 0], ![-1, 0, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, 1], ![1, 0, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 0, -1], ![1, 0, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 0], ![0, 0, -1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, 1], ![0, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, 1, -1], ![0, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 0, -1, 1], ![-2, 0, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 0, -1, -1], ![-2, 0, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, 0], ![1, 1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 3, 1], ![2, -1, -3, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 0, -1], ![1, 1, 0, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, 0], ![0, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -2, 1], ![-3, -1, 2, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, 1, -1], ![0, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, 1, -1, 0], ![-2, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim
  · exact fun _ => ⟨![-1, 1, -1, -1], ![-2, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 0], ![1, -1, 0, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 0, 1], ![1, -1, 0, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 3, -1], ![2, 1, -3, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 0], ![0, -1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, 1, 1], ![0, -1, 1, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -2, -1], ![-3, 1, 2, 1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 0], ![-2, 1, 1, 0], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · exact fun _ => ⟨![-1, -1, -1, 1], ![-2, 1, 1, -1], by decide, by decide, rfl, rfl, rfl, rfl⟩
  · intro h; exact (h (by decide)).elim

