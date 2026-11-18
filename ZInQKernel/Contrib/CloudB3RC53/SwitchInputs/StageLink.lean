import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.CoordSwitch

/-!
# RC53 SwitchInputs: the stage-model link for stage models of any size

Lemma `ex:limits-derivative-switch` (tex L4834–4907) and the regularity paragraph of
`ex:limits-uniform-lower-bound` (tex L5137–5153: the switch "preserves the valuation of its
class-functional determinant coordinate"); Lemma `ex:arith-base-zero` (tex L4360–4366: "All
cancellable disks have unit differential, so integral determinant base change identifies the
coordinate").

`CoordSwitch.lean` reduces UniformSwitch's `CoordStep` to the GLUE link `StageModelLink`: the stage
coordinate is a unit multiple of the coordinate of the generic minimal model `M` (a `2 × 2` matrix,
the cone of RC16's connecting map `∂_F` or `∂_S`). It proves the link for `2 × 2` stage models. Here
the link is proved for stage models of every size that reduce, by an integral change of basis of unit
determinant, to `M ⊕ (unit disks)`:

* `adjugate_fromBlocks_one_inl`: the `M`-block of `adj (M ⊕ 1)` is `adj M` (cofactor expansion along
  the identity block).
* `ConeReduction`: a stage model `D` (with class `z`, functional `w`) is reduced to the cone `M` if
  `P D Q = M ⊕ 1_m` over `F` (block diagonal, reindexed by an equivalence `Fin 2 ⊕ Fin m ≃ Fin N`) for
  integral `P, Q` of unit determinant, and the transformed class and functional restrict on the
  `M`-block to `z₀` and `l₀`.
* `stageModelLink_of_coneReduction` (PROVED): `ConeReduction` and `adj M ≠ 0` give `StageModelLink`
  with the unit `det P · det Q`.
* `StageConeIdentification` (the remaining GLUE, named): the stage models of the old and new
  configurations reduce to the cones of `∂_F` (`oldMat`) and `∂_S` (`newMat`). This is the Nekovář
  identification of the generic minimal model of `C_F` / `C_S` with the cone of the connecting map
  (6.3.3–6.3.4), together with the cancellation of unit disks.
* `coordStep_of_coneIdentification` (PROVED from the GLUE): an actual `CoordStep`.

Non-vacuity (LESSON 2): a genuine `3 × 3` stage model (`ex3Stage`: the minimal model `oldMat 1 e₀`
plus one unit disk), its `ConeReduction`, the resulting `StageModelLink`, and an actual `CoordStep`
from the `3 × 3` old stage to the `2 × 2` new stage of `CoordSwitch`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Module Matrix ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Central
  ZInQ.Contrib.CloudB3RC53.UniformSwitch

section Block

variable {R : Type*} [CommRing R] {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k]
  [DecidableEq l]

/-- **The `M`-block of the adjugate of `M ⊕ 1`** is `adj M`: the cofactor of `fromBlocks M 0 0 1` at
two indices of the first block is the corresponding cofactor of `M` times `det 1`. PROVED. -/
theorem adjugate_fromBlocks_one_inl (M : Matrix k k R) (i j : k) :
    adjugate (fromBlocks M 0 0 (1 : Matrix l l R)) (Sum.inl i) (Sum.inl j) = adjugate M i j := by
  rw [adjugate_apply, adjugate_apply]
  have h : (fromBlocks M 0 0 (1 : Matrix l l R)).updateRow (Sum.inl j) (Pi.single (Sum.inl i) 1) =
      fromBlocks (M.updateRow j (Pi.single i 1)) 0 0 1 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [updateRow_apply, Pi.single_apply]
  rw [h, det_fromBlocks_zero₂₁, det_one, mul_one]

end Block

section Link

variable {A F : Type} [CommRing A] [Field F]

/-- **Reduction of a stage model to the cone `M` plus unit disks** (tex L4360–4366, L4888–4906):
integral `P, Q` of unit determinant with `P D Q = M ⊕ 1_m` over `F` (reindexed by `e`), such that
the transformed class `Q⁻¹ z` and functional `w P⁻¹` restrict on the `M`-block to `z₀` and `l₀`. -/
def ConeReduction (ι : A →+* F) {N : ℕ} (D : Matrix (Fin N) (Fin N) A) (z w : Fin N → A)
    (M : Matrix (Fin 2) (Fin 2) F) (z₀ l₀ : Fin 2 → F) : Prop :=
  ∃ (m : ℕ) (e : Fin 2 ⊕ Fin m ≃ Fin N) (P Q : Matrix (Fin N) (Fin N) A),
    IsUnit P.det ∧ IsUnit Q.det ∧
    (P * D * Q).map ι = reindex e e (fromBlocks M 0 0 (1 : Matrix (Fin m) (Fin m) F)) ∧
    (∀ i, ((Q.map ι)⁻¹ *ᵥ fun t => ι (z t)) (e (Sum.inl i)) = z₀ i) ∧
    (∀ j, ((fun t => ι (w t)) ᵥ* (P.map ι)⁻¹) (e (Sum.inl j)) = l₀ j)

/-- **The stage-model link for stage models of any size** (tex L4360–4366, L4834–4907, L5137–5153).
If a stage model `D` (class `z`, functional `w`, coordinate `u`) reduces to the cone `M` plus unit
disks (`ConeReduction`) and `adj M ≠ 0`, then `u` is the unit `ι(det P · det Q)` times every
coordinate of `M` on `(z₀, l₀)`: `StageModelLink`. PROVED. -/
theorem stageModelLink_of_coneReduction (ι : A →+* F) {N : ℕ} (D : Matrix (Fin N) (Fin N) A)
    (z w : Fin N → A) (u : F)
    (hu : IsClassFunctionalCoord (D.map ι) (fun i => ι (z i)) (fun i => ι (w i)) u)
    (M : Matrix (Fin 2) (Fin 2) F) (z₀ l₀ : Fin 2 → F) (hred : ConeReduction ι D z w M z₀ l₀)
    (hadj : M.adjugate ≠ 0) : StageModelLink ι u M z₀ l₀ := by
  obtain ⟨m, e, P, Q, hP, hQ, hM, hz, hw⟩ := hred
  refine ⟨P.det * Q.det, hP.mul hQ, fun u₀ hu₀ => ?_⟩
  have hPι : IsUnit (P.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hP.map ι
  have hQι : IsUnit (Q.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hQ.map ι
  have h := (MinimalComplexes.coordinateBaseChangeUnit_proof F N (D.map ι) (P.map ι) (Q.map ι)
    (fun i => ι (z i)) (fun i => ι (w i)) u hPι hQι).1 hu
  rw [← Matrix.map_mul, ← Matrix.map_mul, hM] at h
  obtain ⟨i, j, hij⟩ : ∃ i j, M.adjugate i j ≠ 0 := exists_entry_ne_zero hadj
  -- compare the `(i, j)` entries on the `M`-block
  have e1 := congrFun (congrFun h (e (Sum.inl i))) (e (Sum.inl j))
  rw [vecMulVec_apply, hz i, hw j, Matrix.smul_apply, adjugate_reindex, reindex_apply,
    submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, adjugate_fromBlocks_one_inl,
    smul_eq_mul] at e1
  have e2 := congrFun (congrFun hu₀ i) j
  rw [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul] at e2
  have hcoef : Ring.inverse ((P.map ι).det * (Q.map ι).det) * u = u₀ :=
    mul_right_cancel₀ hij (e1.symm.trans e2)
  have hdet : ι (P.det * Q.det) = (P.map ι).det * (Q.map ι).det := by
    rw [map_mul, RingHom.map_det, RingHom.map_det]; rfl
  have hne : (P.map ι).det * (Q.map ι).det ≠ 0 := (hPι.mul hQι).ne_zero
  rw [← hcoef, hdet, Ring.inverse_eq_inv', ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **The remaining GLUE, named: the stage models are the cones of the connecting maps** (Lemma
`ex:limits-derivative-switch`, tex L4888–4906; Nekovář 6.3.3–6.3.4 for the identification of the
generic minimal models; tex L4360–4366 for the cancellation of unit disks). For the old stage `S`
(finite plane condition) and the new stage `S'` (singular plane condition) at a switch with plane
data `ε, σ, J, v`: each stage model reduces, by an integral change of basis of unit determinant, to
the cone of `∂_F` (`oldMat ε v`, class `v`, functional `λ_A`) resp. `∂_S` (`newMat ε σ J v`, class
`J v`, functional `λ_B`) plus unit disks. Classification: GLUE (input). -/
def StageConeIdentification (ι : A →+* F) (S S' : TwoTermStage ι) (ε σ : F)
    (J : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : Prop :=
  ConeReduction ι S.D S.z S.w (oldMat ε v) v (Pi.single 0 1) ∧
    ConeReduction ι S'.D S'.z S'.w (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1)

/-- `J v ≠ 0` for an involution `J` and `v ≠ 0`. -/
theorem mulVec_ne_zero_of_sq {J : Matrix (Fin 2) (Fin 2) F} (hJ2 : J * J = 1) {v : Fin 2 → F}
    (hv : v ≠ 0) : J *ᵥ v ≠ 0 := by
  intro h
  apply hv
  rw [← one_mulVec v, ← hJ2, ← mulVec_mulVec, h, mulVec_zero]

/-- **UniformSwitch's `CoordStep` from the cone identification** (tex L4834–4907, L4940–4950,
L5137–5153): for stage models of any size, the GLUE `StageConeIdentification` gives the two links
(`stageModelLink_of_coneReduction`), hence an actual `CoordStep` (`coordStep_of_switch`).
PROVED (from the GLUE). -/
noncomputable def coordStep_of_coneIdentification (ι : A →+* F) (S S' : TwoTermStage ι) {ε σ : F}
    (hε : ε ≠ 0) (hσ : σ * σ = 1) {J : Matrix (Fin 2) (Fin 2) F} (hJ2 : J * J = 1)
    (hJdet : J.det = -1) {v : Fin 2 → F} (hv : v ≠ 0)
    (hcone : StageConeIdentification ι S S' ε σ J v) : CoordStep ι S.u S'.u :=
  coordStep_of_switch ι hε hσ hJ2 hJdet hv
    (stageModelLink_of_coneReduction ι S.D S.z S.w S.u S.hu _ _ _ hcone.1
      (oldMat_adjugate_ne_zero hε hv))
    (stageModelLink_of_coneReduction ι S'.D S'.z S'.w S'.u S'.hu _ _ _ hcone.2
      (newMat_adjugate_ne_zero hε (left_ne_zero_of_mul_eq_one hσ) (mulVec_ne_zero_of_sq hJ2 hv)))

end Link

/-! ### Non-vacuity: a `3 × 3` stage model (LESSON 2) -/

section Examples

/-- The `3 × 3` stage matrix `diag(0, -1, 1)`: the minimal model `oldMat 1 e₀ = diag(0, -1)` plus one
unit disk. -/
def ex3D : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The `3 × 3` old stage over `ℚ`: class and functional `e₀`, coordinate `-1`. -/
def ex3Stage : TwoTermStage (RingHom.id ℚ) where
  n := 2
  D := ex3D
  z := ![1, 0, 0]
  w := ![1, 0, 0]
  u := -1
  hz := by ext i; fin_cases i <;> simp [ex3D, mulVec, dotProduct, Fin.sum_univ_three]
  hw := by ext j; fin_cases j <;> simp [ex3D, vecMul, dotProduct, Fin.sum_univ_three]
  hu := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ex3D, adjugate_fin_three, vecMulVec_apply]

theorem ex3D_eq_block :
    (1 * ex3D * 1).map (RingHom.id ℚ) =
      reindex finSumFinEquiv finSumFinEquiv
        (fromBlocks (oldMat 1 exV) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℚ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ex3D, oldMat, exV, reindex_apply, finSumFinEquiv, Fin.addCases, Fin.castLT]

/-- **Non-vacuity of `ConeReduction` for a `3 × 3` stage model**: `P = Q = 1`, the block equivalence
`Fin 2 ⊕ Fin 1 ≃ Fin 3`. PROVED. -/
theorem ex3_coneReduction :
    ConeReduction (N := 3) (RingHom.id ℚ) ex3D ![1, 0, 0] ![1, 0, 0] (oldMat 1 exV) exV
      (Pi.single 0 1) := by
  have h1 : ((1 : Matrix (Fin 3) (Fin 3) ℚ).map (RingHom.id ℚ)) = 1 := by
    ext i j; simp [Matrix.one_apply]
  refine ⟨1, finSumFinEquiv, 1, 1, by simp, by simp, ex3D_eq_block, fun i => ?_, fun j => ?_⟩
  · rw [h1, inv_one, one_mulVec]
    fin_cases i <;> rfl
  · rw [h1, inv_one, vecMul_one]
    fin_cases j <;> rfl

/-- **The `3 × 3` stage link** (non-vacuity of `stageModelLink_of_coneReduction` beyond `2 × 2`). -/
theorem ex3_link : StageModelLink (RingHom.id ℚ) ex3Stage.u (oldMat 1 exV) exV (Pi.single 0 1) :=
  stageModelLink_of_coneReduction (RingHom.id ℚ) ex3Stage.D ex3Stage.z ex3Stage.w ex3Stage.u
    ex3Stage.hu _ _ _ (by exact ex3_coneReduction) (oldMat_adjugate_ne_zero one_ne_zero exV_ne_zero)

/-- The `2 × 2` new stage of `CoordSwitch` reduces to its cone with no disks. -/
theorem exNew_coneReduction :
    ConeReduction (N := 2) (RingHom.id ℚ) (newMat 1 1 (switchJ0 ℚ) exV) (switchJ0 ℚ *ᵥ exV)
      (Pi.single 1 1) (newMat 1 1 (switchJ0 ℚ) exV) (switchJ0 ℚ *ᵥ exV) (Pi.single 1 1) := by
  have h1 : ((1 : Matrix (Fin 2) (Fin 2) ℚ).map (RingHom.id ℚ)) = 1 := by
    ext i j; simp [Matrix.one_apply]
  refine ⟨0, Equiv.sumEmpty (Fin 2) (Fin 0), 1, 1, by simp, by simp, ?_, fun i => ?_, fun j => ?_⟩
  · ext i j
    simp [reindex_apply]
  · rw [h1, inv_one, one_mulVec]
    simp
  · rw [h1, inv_one, vecMul_one]
    simp

/-- **Non-vacuity of `StageConeIdentification` and `coordStep_of_coneIdentification`**: an actual
`CoordStep` from the `3 × 3` old stage to the `2 × 2` new stage over `ℚ`. -/
noncomputable def ex3CoordStep : CoordStep (RingHom.id ℚ) ex3Stage.u exStage_new.u :=
  coordStep_of_coneIdentification (RingHom.id ℚ) ex3Stage exStage_new one_ne_zero (mul_one 1)
    (switchJ0_sq (K := ℚ)) (switchJ0_det (K := ℚ)) exV_ne_zero
    ⟨by exact ex3_coneReduction, by exact exNew_coneReduction⟩

end Examples

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
