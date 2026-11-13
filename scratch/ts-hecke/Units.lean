import ZInQKernel.HDecomp.QM.Structures

/-! # ts-hecke: `𝒪^× → (𝒪/3𝒪)^×` is onto (development file)

Table of 72 explicit units (`units_table.py`), checked by `decide`. -/

noncomputable section

namespace TSHeckeUnits

open LeafQM LeafQM.AV

/-- The reduced norm in `ofInt` coordinates:
`nrd(n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+k)/2) = n₀² + n₀n₂ + n₂² − 2(n₁² + n₁n₃ + n₃²)`. -/
def nrdC (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

/-- The conjugate in `ofInt` coordinates. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem nrdC_mul (n m : Fin 4 → ℤ) : nrdC (mulCoord n m) = nrdC n * nrdC m := by
  simp only [nrdC, mulCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem mulCoord_smul_conjC (n : Fin 4 → ℤ) (ε : ℤ) :
    mulCoord n (fun i => ε * conjC n i) = ![ε * nrdC n, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [mulCoord, conjC, nrdC] <;> ring

theorem mulCoord_smul_conjC' (n : Fin 4 → ℤ) (ε : ℤ) :
    mulCoord (fun i => ε * conjC n i) n = ![ε * nrdC n, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [mulCoord, conjC, nrdC] <;> ring

/-- A unit of `𝒪` from coordinates of reduced norm `ε = ±1`. -/
def unitOf (n : Fin 4 → ℤ) (ε : ℤ) (hε : nrdC n = ε) (hε2 : ε * ε = 1) : Oˣ where
  val := ⟨ofInt n, n, rfl⟩
  inv := ⟨ofInt (fun i => ε * conjC n i), _, rfl⟩
  val_inv := by
    apply Subtype.ext
    change ofInt n * ofInt (fun i => ε * conjC n i) = 1
    rw [ofInt_mul, mulCoord_smul_conjC, hε, hε2, ofInt_one]
  inv_val := by
    apply Subtype.ext
    change ofInt (fun i => ε * conjC n i) * ofInt n = 1
    rw [ofInt_mul, mulCoord_smul_conjC', hε, hε2, ofInt_one]

def unitTbl : List (Fin 4 → ℤ) :=
  [![0, 0, 0, 0],
   ![1, 0, 0, 0],
   ![-1, 0, 0, 0],
   ![-3, -2, 0, 0],
   ![1, 1, 0, 0],
   ![-1, 1, 0, 0],
   ![-3, 2, 0, 0],
   ![1, -1, 0, 0],
   ![-1, -1, 0, 0],
   ![0, 0, 1, 0],
   ![0, 0, 0, 0],
   ![-1, 0, 1, 0],
   ![0, 1, 1, 0],
   ![1, 1, 1, 0],
   ![-1, 1, 1, 0],
   ![0, -1, 1, 0],
   ![1, -1, 1, 0],
   ![-1, -1, 1, 0],
   ![0, 0, -1, 0],
   ![1, 0, -1, 0],
   ![0, 0, 0, 0],
   ![0, 1, -1, 0],
   ![1, 1, -1, 0],
   ![-1, 1, -1, 0],
   ![0, -1, -1, 0],
   ![1, -1, -1, 0],
   ![-1, -1, -1, 0],
   ![-3, 0, 0, -2],
   ![1, 0, 0, 1],
   ![-1, 0, 0, 1],
   ![0, 0, 0, 0],
   ![1, 1, -3, 1],
   ![-1, 1, 3, 1],
   ![-3, 2, 0, -2],
   ![1, -1, 0, 1],
   ![-1, -1, 0, 1],
   ![0, 0, 1, 1],
   ![1, 0, 1, 1],
   ![-1, 0, 1, 1],
   ![-3, 1, 1, 1],
   ![0, 0, 0, 0],
   ![-1, 1, -2, 1],
   ![0, -1, 1, 1],
   ![1, -1, 1, 1],
   ![-1, -1, 1, 1],
   ![0, 0, -1, 1],
   ![1, 0, -1, 1],
   ![-1, 0, -1, 1],
   ![3, 1, -1, 1],
   ![-2, 1, -1, 1],
   ![0, 0, 0, 0],
   ![0, -1, -1, 1],
   ![1, -1, -1, 1],
   ![-1, -1, -1, 1],
   ![-3, 0, 0, 2],
   ![1, 0, 0, -1],
   ![-1, 0, 0, -1],
   ![-3, -2, 0, 2],
   ![1, 1, 0, -1],
   ![-1, 1, 0, -1],
   ![0, 0, 0, 0],
   ![1, -1, -3, -1],
   ![-1, -1, 3, -1],
   ![0, 0, 1, -1],
   ![1, 0, 1, -1],
   ![-1, 0, 1, -1],
   ![0, 1, 1, -1],
   ![1, 1, 1, -1],
   ![-1, 1, 1, -1],
   ![-3, -1, 1, -1],
   ![0, 0, 0, 0],
   ![-1, -1, -2, -1],
   ![0, 0, -1, -1],
   ![1, 0, -1, -1],
   ![-1, 0, -1, -1],
   ![0, 1, -1, -1],
   ![1, 1, -1, -1],
   ![-1, 1, -1, -1],
   ![3, -1, -1, -1],
   ![-2, -1, -1, -1],
   ![0, 0, 0, 0]]


/-- The table entry for a residue vector. -/
def tbl (c : Fin 4 → ZMod 3) : Fin 4 → ℤ :=
  unitTbl.getD ((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val) 0

/-- The reduced norm mod 3. -/
def nrd3 (c : Fin 4 → ZMod 3) : ZMod 3 :=
  c 0 ^ 2 + c 0 * c 2 + c 2 ^ 2 - 2 * (c 1 ^ 2 + c 1 * c 3 + c 3 ^ 2)

/-- **The table is correct** (checked by `decide`): for every residue of nonzero reduced norm,
the entry reduces to it and has reduced norm `±1`. -/
theorem tbl_spec : ∀ c : Fin 4 → ZMod 3, nrd3 c ≠ 0 →
    (∀ i, ((tbl c i : ℤ) : ZMod 3) = c i) ∧ (nrdC (tbl c) = 1 ∨ nrdC (tbl c) = -1) := by
  decide +kernel

theorem nrdC_cast (n : Fin 4 → ℤ) : ((nrdC n : ℤ) : ZMod 3) = nrd3 (fun i => (n i : ZMod 3)) := by
  simp [nrdC, nrd3]

/-- **`𝒪^× → (𝒪/3𝒪)^×` is onto** (compiled): an element `u₀` of `𝒪` invertible modulo `3𝒪` is
congruent mod `3𝒪` to a unit. -/
theorem exists_unit_congr (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) :
    ∃ u : Oˣ, ∃ d : O, u₀ - (u : O) = 3 * d := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨nu, hnu⟩ := u₀.2
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have h1 : ((1 : O) : B) = ofInt ![1, 0, 0, 0] := by rw [ofInt_one]; rfl
  have hcoord : mulCoord nv nu - ![1, 0, 0, 0] = fun i => 3 * nc i := by
    apply ofInt_injective
    rw [← ofInt_sub, ← ofInt_mul, ← three_mul_ofInt, ← hnu, ← hnv, ← hnc, ← h1, ← h33]
    exact congrArg Subtype.val hc
  -- the reduced norm of `u₀` is nonzero mod 3
  have hn1 : ((nrdC (mulCoord nv nu) : ℤ) : ZMod 3) = 1 := by
    have : mulCoord nv nu = fun i => ![1, 0, 0, 0] i + 3 * nc i := by
      funext i
      have := congrFun hcoord i
      simp only [Pi.sub_apply] at this
      linarith
    rw [this, nrdC_cast]
    simp only [nrd3]
    simp [show (3 : ZMod 3) = 0 from rfl]
  have hnu3 : nrd3 (fun i => (nu i : ZMod 3)) ≠ 0 := by
    intro h0
    rw [nrdC_mul, Int.cast_mul, nrdC_cast nu, h0, mul_zero] at hn1
    exact zero_ne_one hn1
  obtain ⟨hred, hε⟩ := tbl_spec _ hnu3
  set n := tbl (fun i => (nu i : ZMod 3))
  have hdvd : ∀ i, (3 : ℤ) ∣ nu i - n i := by
    intro i
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (nu i - n i) 3).1
      (by rw [Int.cast_sub, hred i, sub_self])
    exact_mod_cast this
  let ε : ℤ := nrdC n
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [ε, h]
  refine ⟨unitOf n ε rfl hε2, ⟨ofInt (fun i => (nu i - n i) / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  change (u₀ : B) - ofInt n = ((3 : O) : B) * ofInt (fun i => (nu i - n i) / 3)
  rw [hnu, h33, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact (Int.mul_ediv_cancel' (hdvd i)).symm

end TSHeckeUnits

end

#print axioms TSHeckeUnits.tbl_spec
#print axioms TSHeckeUnits.exists_unit_congr
