import ZInQKernel.Contrib.OneProof.RC.EisSlash.Residues
import ZInQKernel.Contrib.OneProof.RC.EisForm.Modularity

/-! The character of the finite residue weight, and its effect on the
Eisenstein constituent in tex 9647–9654, 9762–9764 and 9862–9864.
The residue computation is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane CongruenceSubgroup
open O12Eisenstein O12EisConst EisForm
open scoped MatrixGroups

variable {m₁ m₂ N : ℕ} [NeZero m₂]

/-- The ordered pair's weight on an integer row. The inverse is on the
second character, as required by its Gauss transform in the Fourier series. -/
def rowWeight (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (x : Fin 2 → ℤ) : ℂ :=
  if (m₂ : ℤ) ∣ x 0 then a ((x 0 / (m₂ : ℤ) : ℤ) : ZMod m₁) *
    b⁻¹ (x 1 : ZMod m₂) else 0

/-- The finite coefficient on a residue class at the product level. -/
def characterWeight (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (r : Fin 2 → ZMod N) : ℂ :=
  rowWeight a b (residueLift r)

private theorem rowWeight_grid (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂) (x t : Fin 2 → ℤ) :
    rowWeight a b (grid N x t) = rowWeight a b x := by
  have h0 : grid N x t 0 = x 0 + (m₂ : ℤ) * ((m₁ : ℤ) * t 0) := by
    change (N : ℤ) * t 0 + x 0 = _
    rw [hN, Nat.cast_mul]
    ring
  have h1 : (grid N x t 1 : ZMod m₂) = (x 1 : ZMod m₂) := by
    change (((N : ℤ) * t 1 + x 1 : ℤ) : ZMod m₂) = _
    simp [hN]
  have hc : (m₂ : ℤ) ∣ (m₂ : ℤ) * ((m₁ : ℤ) * t 0) := dvd_mul_right _ _
  have hm : (m₂ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m₂
  simp only [rowWeight, h0, h1, Int.dvd_add_left hc,
    Int.add_mul_ediv_left _ _ hm, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul, add_zero]

theorem characterWeight_on_row [NeZero N] (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂) (x : Fin 2 → ℤ) :
    characterWeight a b (rowResidue N x) = rowWeight a b x := by
  obtain ⟨t, ht⟩ := exists_grid_of_residue_eq (v := x) (a := residueLift (rowResidue N x))
    (by rw [rowResidue_lift])
  exact (rowWeight_grid hN a b _ _).symm.trans (congrArg (rowWeight a b) ht).symm

private theorem rowWeight_transform (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (g : Gamma0 N) (x : Fin 2 → ℤ) :
    rowWeight a b x = (a ((g.val 1 1 : ℤ) : ZMod m₁) * b ((g.val 1 1 : ℤ) : ZMod m₂)) *
      rowWeight a b (x ᵥ* g.val.val) := by
  let A : ℤ := g.val 0 0
  let B : ℤ := g.val 0 1
  let D : ℤ := g.val 1 1
  have hc : (N : ℤ) ∣ g.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.property)
  obtain ⟨u, hu₀⟩ := hc
  have hu : g.val 1 0 = (m₂ : ℤ) * (m₁ : ℤ) * u :=
    hu₀.trans (by rw [hN, Nat.cast_mul])
  have hdet : A * D - B * g.val 1 0 = 1 :=
    (Matrix.det_fin_two g.val.val).symm.trans g.val.prop
  have hAD {m : ℕ} (hm : m ∣ N) : (A : ZMod m) * (D : ZMod m) = 1 := by
    have hC : ((g.val 1 0 : ℤ) : ZMod m) = 0 := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        ((by exact_mod_cast hm : (m : ℤ) ∣ N).trans
          ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.property)))
    have he := congrArg (fun v : ℤ => (v : ZMod m)) hdet
    simpa [hC] using he
  have hd₁ : m₁ ∣ N := hN ▸ dvd_mul_left m₁ m₂
  have hd₂ : m₂ ∣ N := hN ▸ dvd_mul_right m₂ m₁
  have h0 : (x ᵥ* g.val.val) 0 = x 0 * A + x 1 * g.val 1 0 := by
    simp [vecMul, dotProduct, Fin.sum_univ_two, A]
  have hC₂ : ((g.val 1 0 : ℤ) : ZMod m₂) = 0 := by simp [hu]
  have hdiv : (m₂ : ℤ) ∣ (x ᵥ* g.val.val) 0 ↔ (m₂ : ℤ) ∣ x 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [h0, Int.cast_add, Int.cast_mul, hC₂, mul_zero, add_zero]
    constructor
    · intro h
      have hh := congrArg (· * (D : ZMod m₂)) h
      simpa [mul_assoc, hAD hd₂] using hh
    · intro h
      rw [h, zero_mul]
  by_cases hx : (m₂ : ℤ) ∣ x 0
  · have hx' := hx
    obtain ⟨t, ht⟩ := hx'
    have hfirst : (x ᵥ* g.val.val) 0 = (m₂ : ℤ) * (t * A + x 1 * ((m₁ : ℤ) * u)) := by
      rw [h0, ht, hu]
      ring
    have hm : (m₂ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m₂
    have hy : ((x ᵥ* g.val.val) 1 : ZMod m₂) = (x 1 : ZMod m₂) * (D : ZMod m₂) := by
      have he : (x ᵥ* g.val.val) 1 = x 0 * B + x 1 * D := by
        simp [vecMul, dotProduct, Fin.sum_univ_two, B, D]
      simp [he, ht]
    have hi : b (D : ZMod m₂) * b⁻¹ (D : ZMod m₂) = 1 := by
      rw [MulChar.inv_apply_eq_inv']
      exact mul_inv_cancel₀ (MulChar.apply_ne_zero_iff.mpr
        (isUnit_iff_dvd_one.mpr ⟨(A : ZMod m₂), by rw [mul_comm, hAD hd₂]⟩))
    have ha : a (D : ZMod m₁) * a (A : ZMod m₁) = 1 := by
      rw [← map_mul, mul_comm (D : ZMod m₁), hAD hd₁, map_one]
    simp only [rowWeight, hx, hdiv.mpr hx, ite_true, hy]
    rw [show x 0 / (m₂ : ℤ) = t by rw [ht, Int.mul_ediv_cancel_left _ hm],
      show (x ᵥ* g.val.val) 0 / (m₂ : ℤ) = t * A + x 1 * ((m₁ : ℤ) * u) by
        rw [hfirst, Int.mul_ediv_cancel_left _ hm]]
    change _ = (a (D : ZMod m₁) * b (D : ZMod m₂)) * _
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, mul_zero, add_zero, map_mul]
    calc
      _ = (a (D : ZMod m₁) * a (A : ZMod m₁)) *
        (b (D : ZMod m₂) * b⁻¹ (D : ZMod m₂)) *
        (a (t : ZMod m₁) * b⁻¹ (x 1 : ZMod m₂)) := by rw [ha, hi, one_mul, one_mul]
      _ = _ := by ring
  · simp [rowWeight, hx, hdiv]

/-- The residue weights pull back by the indicated product of characters. -/
theorem characterWeight_pullback [NeZero N] (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (g : Gamma0 N) (r : Fin 2 → ZMod N) :
    characterWeight a b ((residueEquiv N g.val).symm r) =
      (a ((g.val 1 1 : ℤ) : ZMod m₁) * b ((g.val 1 1 : ℤ) : ZMod m₂)) *
        characterWeight a b r := by
  let x := residueLift ((residueEquiv N g.val).symm r)
  have hx : rowResidue N (x ᵥ* g.val.val) = r := by
    rw [rowResidue_vecMul, rowResidue_lift]
    exact (residueEquiv N g.val).apply_symm_apply r
  have hright := characterWeight_on_row hN a b (x ᵥ* g.val.val)
  rw [hx] at hright
  rw [hright]
  exact rowWeight_transform hN a b g x

variable {D : Type*} [Field D] {p : ℕ} [Fact p.Prime]

instance pairLevelNeZero (E : CharacterPair D p) : NeZero (pairLevel E) :=
  ⟨mul_ne_zero (mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne _)) (NeZero.ne _)⟩

/-- The actual, ordered weight at the product level of the constituent. -/
def pairWeight (E : CharacterPair D p) (c : D →+* ℂ) :
    (Fin 2 → ZMod (pairLevel E)) → ℂ :=
  if E.twistUnramified then characterWeight (E.ramified.ringHomComp c) (E.unram.ringHomComp c)
  else characterWeight (E.unram.ringHomComp c) (E.ramified.ringHomComp c)

private theorem pairNebentypus_value (E : CharacterPair D p) (c : D →+* ℂ)
    (g : Gamma0 (pairLevel E)) :
    (↑(pairNebentypus E c ((Gamma0Map (pairLevel E)).toHomUnits g)) : ℂ) =
      (E.unram.ringHomComp c) ((g.val 1 1 : ℤ) : ZMod E.unramLevel) *
      (E.ramified.ringHomComp c) ((g.val 1 1 : ℤ) : ZMod (p * E.awayLevel)) := by
  let u : (ZMod (pairLevel E))ˣ := (Gamma0Map (pairLevel E)).toHomUnits g
  let χᵣ : DirichletCharacter D (pairLevel E) := E.ramified.changeLevel (dvd_mul_right _ _)
  let χᵤ : DirichletCharacter D (pairLevel E) := E.unram.changeLevel (dvd_mul_left _ _)
  let χ : DirichletCharacter D (pairLevel E) := χᵣ * χᵤ
  change (↑((χ.ringHomComp c).toUnitHom u) : ℂ) = _
  rw [MulChar.coe_toUnitHom, MulChar.ringHomComp_apply]
  change c (χᵣ u * χᵤ u) = _
  have hᵣ : χᵣ u = E.ramified (ZMod.cast (u : ZMod (pairLevel E))) :=
    DirichletCharacter.changeLevel_eq_cast_of_dvd E.ramified
      (show p * E.awayLevel ∣ pairLevel E from dvd_mul_right _ _) u
  have hᵤ : χᵤ u = E.unram (ZMod.cast (u : ZMod (pairLevel E))) :=
    DirichletCharacter.changeLevel_eq_cast_of_dvd E.unram
      (show E.unramLevel ∣ pairLevel E from dvd_mul_left _ _) u
  rw [hᵣ, hᵤ]
  change c (E.ramified (ZMod.cast ((g.val 1 1 : ℤ) : ZMod (pairLevel E))) *
    E.unram (ZMod.cast ((g.val 1 1 : ℤ) : ZMod (pairLevel E)))) = _
  rw [ZMod.cast_intCast (show p * E.awayLevel ∣ pairLevel E from dvd_mul_right _ _),
    ZMod.cast_intCast (show E.unramLevel ∣ pairLevel E from dvd_mul_left _ _), map_mul, mul_comm]
  rfl

theorem pairWeight_pullback (E : CharacterPair D p) (c : D →+* ℂ)
    (g : Gamma0 (pairLevel E)) (r : Fin 2 → ZMod (pairLevel E)) :
    pairWeight E c ((residueEquiv (pairLevel E) g.val).symm r) =
      (↑(pairNebentypus E c ((Gamma0Map (pairLevel E)).toHomUnits g)) : ℂ) * pairWeight E c r := by
  rw [pairNebentypus_value]
  cases h : E.twistUnramified
  · simp only [pairWeight, h, Bool.false_eq_true, ite_false]
    exact characterWeight_pullback rfl _ _ g r
  · simp only [pairWeight, h, ite_true]
    rw [mul_comm ((E.unram.ringHomComp c) _)]
    exact characterWeight_pullback (mul_comm _ _) _ _ g r


end ZInQ.Manuscript.RC.EisSlash
