import ZInQKernel.Contrib.OneProof.RC.Central.BaseZero
import ZInQKernel.Contrib.OneProof.RC.Central.Correction

/-!
# Lane RC15 (central): non-vacuity of the base-zero core and of the coordinate

The hypotheses of `baseZero_core` are jointly satisfiable with a **nonzero** generic coordinate,
so the lemma's conclusion (regular, and zero at the centre) is not forced by its hypotheses being
contradictory or by the coordinate being zero to begin with. The model: the DVR `ℤ₂` with residue
map to `𝔽₂`, the zero `1 × 1` differential (central dimensions `(1,1)`), the cycle `z = 2` and the
functional `w = 1`; the generic coordinate is `2 ≠ 0`, regular, with central value `0`.

Also (`disk_example`): with a torsion disk, `D = diag(2, 0)`, the coordinate of `z = (0, z₂)` and
`w = (0, w₂)` is `z₂ w₂ / 2`: the disk `[ℤ₂ --2--> ℤ₂]` contributes `2⁻¹`, i.e. `(−1)^{2+1} v₂(2)`
to the valuation, the sign rule of tex 4058–4060.

Every declaration in this file is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Central

open Matrix

/-- The defining identity of the coordinate in the model: `z ⊗ w = 2 · adj 0` for the zero
`1 × 1` differential (`adj 0 = 1`). PROVED. -/
theorem model_coord :
    IsClassFunctionalCoord ((0 : Matrix (Fin 1) (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]))
      (fun _ => algebraMap ℤ_[2] ℚ_[2] 2) (fun _ => algebraMap ℤ_[2] ℚ_[2] 1) 2 := by
  ext i j
  fin_cases i; fin_cases j
  simp [vecMulVec_apply, adjugate_fin_one]
  norm_cast

/-- The central cycle of the model vanishes: `2 ↦ 0 ∈ 𝔽₂`. PROVED. -/
theorem model_central_zero : ∀ _ : Fin 1, PadicInt.toZMod (p := 2) (2 : ℤ_[2]) = 0 := by
  intro _
  rw [map_ofNat]
  decide

/-- **The maximal ideal of `ℤ₂` is killed by the residue map**, so `baseZero_core` applies to the
model. PROVED. -/
theorem toZMod_kills_maximalIdeal :
    ∀ x ∈ IsLocalRing.maximalIdeal ℤ_[2], PadicInt.toZMod (p := 2) x = 0 := by
  intro x hx
  rw [← PadicInt.ker_toZMod] at hx
  exact hx

/-- **`baseZero_core` is non-vacuous.** Its hypotheses hold jointly in the model, with a nonzero
generic coordinate. PROVED. -/
theorem baseZero_core_nonvacuous :
    ∃ (D : Matrix (Fin 1) (Fin 1) ℤ_[2]) (z w : Fin 1 → ℤ_[2]) (uprim : ℚ_[2]),
      (D.map (PadicInt.toZMod (p := 2))).rank = 0 ∧ D *ᵥ z = 0 ∧
      IsClassFunctionalCoord (D.map (algebraMap ℤ_[2] ℚ_[2]))
        (fun i => algebraMap ℤ_[2] ℚ_[2] (z i)) (fun i => algebraMap ℤ_[2] ℚ_[2] (w i)) uprim ∧
      (∀ i, PadicInt.toZMod (p := 2) (z i) = 0) ∧ uprim ≠ 0 :=
  ⟨0, fun _ => 2, fun _ => 1, 2, by simp, by simp, model_coord, model_central_zero,
    by norm_num⟩

/-- The conclusion of `baseZero_core` on the model: the nonzero generic coordinate `2` is regular
and vanishes at the centre. PROVED. -/
theorem baseZero_core_model :
    ∃ u₀ : ℤ_[2], algebraMap ℤ_[2] ℚ_[2] u₀ = 2 ∧ PadicInt.toZMod (p := 2) u₀ = 0 :=
  (baseZero_core (F := ℚ_[2]) (PadicInt.toZMod (p := 2)) toZMod_kills_maximalIdeal
    (0 : Matrix (Fin 1) (Fin 1) ℤ_[2]) (by simp) (fun _ => 2) (fun _ => 1) (by simp) 2
    model_coord model_central_zero 1).1

/-- **A torsion disk contributes `d⁻¹`** (tex 4058–4060): for `D = diag(2, 0)` the coordinate of
`z = (0, z₂)`, `w = (0, w₂)` is `z₂ w₂ / 2`. PROVED. -/
theorem disk_example (z₂ w₂ : ℚ_[2]) :
    IsClassFunctionalCoord !![(2 : ℚ_[2]), 0; 0, 0] ![0, z₂] ![0, w₂] (z₂ * w₂ / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, adjugate_fin_two]

end ZInQ.Manuscript.RC.Central
