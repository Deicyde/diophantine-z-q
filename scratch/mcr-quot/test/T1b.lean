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


theorem nrdZ_mod3 (nc : Fin 4 → ℤ) :
    ((nrdZ (fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i) : ℤ) : ZMod 3) = 1 := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  simp [nrdZ, h3]

/-- **`𝒪^× ↠ (𝒪/3𝒪)^×`**: an element of `𝒪` invertible modulo `3𝒪` is congruent modulo `3𝒪` to a
unit of `𝒪` (the unit table). -/
theorem exists_unit_congr (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) :
    ∃ u : Oˣ, ∃ c : O, (u : O) - u₀ = 3 * c := by
  obtain ⟨nu, hnu⟩ := u₀.2
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨c, hc⟩ := h
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have hcB : (v₀ : B) * u₀ - 1 = 3 * c := by
    have := congrArg Subtype.val hc
    simpa [h33] using this
  have key : mulCoord nv nu = fun i => (![1, 0, 0, 0] : Fin 4 → ℤ) i + 3 * nc i := by
    have e : ofInt (mulCoord nv nu) - ofInt ![1, 0, 0, 0] = ofInt (fun i => 3 * nc i) := by
      rw [← ofInt_mul, ofInt_one, ← AV.three_mul_ofInt, ← hnu, ← hnv, ← hnc, hcB]
    rw [AV.ofInt_sub] at e
    have e2 := AV.ofInt_injective e
    funext i
    have := congrFun e2 i
    simp only [Pi.sub_apply] at this
    omega
  have hN : ((nrdZ nu : ℤ) : ZMod 3) ≠ 0 := by
    intro h0
    have e := nrdZ_mul nv nu
    rw [key] at e
    have e3 := congrArg (fun z : ℤ => (z : ZMod 3)) e
    simp only [nrdZ_mod3, Int.cast_mul, h0, mul_zero] at e3
    exact one_ne_zero e3
  have hN' : ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 ≠ 0 := by
    have : ((nrdZ nu : ℤ) : ZMod 3) = ((nu 0 : ℤ) : ZMod 3) ^ 2 + (nu 0 : ZMod 3) * (nu 2 : ZMod 3) +
      (nu 2 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) ^ 2 - 2 * (nu 1 : ZMod 3) * (nu 3 : ZMod 3) -
      2 * (nu 3 : ZMod 3) ^ 2 := by simp [nrdZ]
    rwa [← this]
  obtain ⟨n, m, hnm, hmn, h0, h1, h2, h3⟩ := unit_table _ _ _ _ hN'
  have hdiv : ∀ i, (3 : ℤ) ∣ n i - nu i := by
    intro i
    have hi : ((nu i : ℤ) : ZMod 3) = ((n i : ℤ) : ZMod 3) := by
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).1 hi
  choose k hk using hdiv
  let u : Oˣ :=
    { val := ⟨ofInt n, ⟨n, rfl⟩⟩
      inv := ⟨ofInt m, ⟨m, rfl⟩⟩
      val_inv := by
        apply Subtype.ext
        change ofInt n * ofInt m = 1
        rw [ofInt_mul, hnm, ofInt_one]
      inv_val := by
        apply Subtype.ext
        change ofInt m * ofInt n = 1
        rw [ofInt_mul, hmn, ofInt_one] }
  refine ⟨u, ⟨ofInt k, ⟨k, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change ofInt n - (u₀ : B) = ((3 : O) : B) * ofInt k
  rw [hnu, h33, AV.ofInt_sub, AV.three_mul_ofInt]
  congr 1
  funext i
  simp [hk i]
