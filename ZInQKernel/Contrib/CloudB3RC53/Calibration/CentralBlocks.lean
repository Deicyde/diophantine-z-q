import ZInQKernel.Contrib.CloudB3RC53.Calibration.Lengths

/-!
# Calibration (4.6): the central quotient block from the local blocks

The input `hcentral` of `hvprim_of_model_and_lengths` (`Lengths.lean`) identifies the central
determinant of the full/Kummer quotient block `D_W` with that of the block-diagonal matrix
`diag(χ Fr_r − r, χ Fr_r − r, 2·1, …, 2·1)` (tex L4066–4078). As a determinant this is basis
dependent; what (4.6) uses is its central `2`-adic valuation. This file derives that valuation from
the block structure (Elliot's computation):

* the quotient complex is the direct sum of the local quotients at the two places above the moving
  prime and at the `2ω` active places (`τ` is multiplicative over direct sums, `tau_sum`), in
  retained bases related to the local bases by a graded change of basis with integral unit
  determinants (`tau_rebase`: the determinant changes by `det P · det Q`, of central valuation
  `0`): `D_W = P · diag(B_mov, B_act) · Q`, `v₂ det P(0) = v₂ det Q(0) = 0`;
* at either place above the moving prime the local block is RC15's two-place block
  `twoPlaceBlock F r z z⁻¹` over `ℚ₂[[t]]` (the singular block of (4.4)), whose Frobenius `F` has
  central value `Fr_r` and whose moving scalars `z, z⁻¹` have central value `χ = χ_h(r) = ±1` (the
  moving character is trivial at the centre);
* at the active places the local block is the minimal model `2 · 1` of `E[2]` in degree two
  (`v2_det_active`; the minimal model is the input, as in `Lengths.lean`).

Results:

* `central_det`, `central_twoPlaceBlock`: specialization at the centre commutes with determinants
  and with the two-place block.
* `v2_central_det_of_local_blocks`: `v₂ det D_W(0) = v₂ det diag(twoPlaceBlock F r χ χ, 2·1)`, i.e.
  `hcentral` at the level of valuations.
* `hδ_of_local_blocks`: `v₂ det D_W(0) = 2 v₂N + 4ω` (the input `hδ`).
* `hvprim_of_model_and_local_blocks`: `hvprim_of_model_and_lengths` with `hcentral` replaced by the
  local block structure.
* `localBlocks_example`: the hypotheses are inhabited (`P = Q = 1`, constant blocks).

**Classification.** PROVED (the block structure is the named input).
-/

namespace ZInQ.Contrib.CloudB3RC53.Calibration

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-- Specialization at the centre commutes with determinants. -/
theorem central_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (PowerSeries ℚ_[2])) :
    central M.det = (M.map central).det := by
  have := RingHom.map_det (PowerSeries.constantCoeff (R := ℚ_[2])) M
  have e : M.map central = (PowerSeries.constantCoeff (R := ℚ_[2])).mapMatrix M := by
    ext i j; simp [central, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [e, ← this]
  simp [central, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Specialization at the centre of the two-place block. -/
theorem central_twoPlaceBlock (F : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2]))
    (q z zi : PowerSeries ℚ_[2]) :
    (twoPlaceBlock F q z zi).map central =
      twoPlaceBlock (F.map central) (central q) (central z) (central zi) := by
  ext (i | i) (j | j) <;>
    simp [twoPlaceBlock, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      central] <;> split_ifs <;> simp

/-- **`hcentral` at the level of valuations**: from the local block structure
`D_W = P · diag(twoPlaceBlock F' r z z', B_act) · Q` (relabelled by `e`), with integral unit base
changes, the central Frobenius `F'(0) = F`, the central moving scalars `z(0) = z'(0) = χ`, and the
active minimal model `B_act(0) = 2 · 1`. -/
theorem v2_central_det_of_local_blocks {κ : Type*} [Fintype κ] [DecidableEq κ] (ω : ℕ)
    (DW P Q : Matrix κ κ (PowerSeries ℚ_[2])) (e : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * ω))
    (F' : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])) (r : ℕ) (z z' : PowerSeries ℚ_[2])
    (Bact : Matrix (Fin (4 * ω)) (Fin (4 * ω)) (PowerSeries ℚ_[2]))
    (hDW : DW = P * (fromBlocks (twoPlaceBlock F' (r : PowerSeries ℚ_[2]) z z') 0 0 Bact).submatrix
      e e * Q)
    (hP : v2 (central P.det) = 0) (hQ : v2 (central Q.det) = 0)
    (F : Matrix (Fin 2) (Fin 2) ℚ_[2]) (χ : ℤ) (hF : F'.map central = F)
    (hz : central z = χ) (hz' : central z' = χ)
    (hact : Bact.map central = (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2])) :
    v2 (central DW.det) = v2 (fromBlocks (twoPlaceBlock F (r : ℚ_[2]) (χ : ℚ_[2]) (χ : ℚ_[2])) 0 0
        ((2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2]))).det := by
  rw [hDW, det_mul, det_mul, det_submatrix_equiv_self, central_mul, central_mul, v2_mul, v2_mul,
    hP, hQ, zero_add, add_zero, central_det, Matrix.fromBlocks_map, central_twoPlaceBlock, hF,
    hz, hz', hact]
  have hr0 : central (r : PowerSeries ℚ_[2]) = r := by simp [central]
  have h0 : ∀ {m n : Type} (M : Matrix m n (PowerSeries ℚ_[2])), M = 0 → M.map central = 0 := by
    intro m n M hM; subst hM; exact Matrix.map_zero _ (by simp [central])
  rw [hr0, h0 _ rfl, h0 _ rfl]

/-- **The input `hδ` from the local blocks**: `v₂ det D_W(0) = 2 v₂N + 4ω`. -/
theorem hδ_of_local_blocks {κ : Type*} [Fintype κ] [DecidableEq κ] (ω : ℕ)
    (DW P Q : Matrix κ κ (PowerSeries ℚ_[2])) (e : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * ω))
    (F' : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])) (r : ℕ) (z z' : PowerSeries ℚ_[2])
    (Bact : Matrix (Fin (4 * ω)) (Fin (4 * ω)) (PowerSeries ℚ_[2]))
    (hDW : DW = P * (fromBlocks (twoPlaceBlock F' (r : PowerSeries ℚ_[2]) z z') 0 0 Bact).submatrix
      e e * Q)
    (hP : v2 (central P.det) = 0) (hQ : v2 (central Q.det) = 0)
    (F : Matrix (Fin 2) (Fin 2) ℚ_[2]) (hr : Odd r) (a χ : ℤ) (hχ : χ = 1 ∨ χ = -1)
    (ha : F.trace = a) (hd : F.det = r) (hN : (r : ℤ) + 1 - χ * a ≠ 0) (hF : F'.map central = F)
    (hz : central z = χ) (hz' : central z' = χ)
    (hact : Bact.map central = (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2])) :
    v2 (central DW.det) =
      ((2 * ((padicValInt 2 ((r : ℤ) + 1 - χ * a) : ℕ) : ℤ) + 4 * (ω : ℤ) : ℤ) : WithTop ℤ) := by
  rw [v2_central_det_of_local_blocks ω DW P Q e F' r z z' Bact hDW hP hQ F χ hF hz hz' hact,
    v2_det_quotient F r hr a χ hχ ha hd hN ω]

/-- **`hvprim` with `hcentral` replaced by the local block structure** (tex L4051–4078). -/
theorem hvprim_of_model_and_local_blocks {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])) (X : Matrix (Fin n) κ (PowerSeries ℚ_[2]))
    (DW : Matrix κ κ (PowerSeries ℚ_[2])) (zK wK : Fin n → PowerSeries ℚ_[2])
    (zP wP : Fin n ⊕ κ → PowerSeries ℚ_[2]) (uK uprim : PowerSeries ℚ_[2])
    (hz : ∀ i, zP (Sum.inl i) = zK i) (hw : ∀ i, wP (Sum.inl i) = wK i)
    (hP : IsCoordOn (fromBlocks DK X 0 DW) zP wP uprim)
    (hKc : IsClassFunctionalCoord DK zK wK uK) (hadj : DK.adjugate ≠ 0) (j vL vm gA sA : ℤ)
    (hK : v2 (central uK) = (((j + vL + vm) + (j + vL + vm) +
      (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
        Central.diskContribution 3 gA) : ℤ) : WithTop ℤ))
    (ω : ℕ) (P Q : Matrix κ κ (PowerSeries ℚ_[2])) (e : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * ω))
    (F' : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])) (r : ℕ) (z z' : PowerSeries ℚ_[2])
    (Bact : Matrix (Fin (4 * ω)) (Fin (4 * ω)) (PowerSeries ℚ_[2]))
    (hDW : DW = P * (fromBlocks (twoPlaceBlock F' (r : PowerSeries ℚ_[2]) z z') 0 0 Bact).submatrix
      e e * Q)
    (hPu : v2 (central P.det) = 0) (hQu : v2 (central Q.det) = 0)
    (F : Matrix (Fin 2) (Fin 2) ℚ_[2]) (hr : Odd r) (a χ : ℤ) (hχ : χ = 1 ∨ χ = -1)
    (ha : F.trace = a) (hd : F.det = r) (hN : (r : ℤ) + 1 - χ * a ≠ 0) (hF : F'.map central = F)
    (hzc : central z = χ) (hzc' : central z' = χ)
    (hact : Bact.map central = (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * ω)) (Fin (4 * ω)) ℚ_[2])) :
    v2 (central uprim) = ((ZInQ.Manuscript.RC.Wiring.primValuation j vL vm gA sA
      ((padicValInt 2 ((r : ℤ) + 1 - χ * a) : ℕ) : ℤ) (ω : ℤ) : ℤ) : WithTop ℤ) :=
  hvprim_of_triangular_model DK X DW zK wK zP wP uK uprim hz hw hP hKc hadj j vL vm gA sA _ _ hK
    (hδ_of_local_blocks ω DW P Q e F' r z z' Bact hDW hPu hQu F hr a χ hχ ha hd hN hF hzc hzc'
      hact)

/-- **Non-vacuity of the local block structure**: `P = Q = 1`, `e` the identity, constant blocks
`twoPlaceBlock F r χ χ` and `2 · 1`, with `F = diag(1, 1)`, `r = 1`, `χ = 1`, `ω = 1`. -/
theorem localBlocks_example :
    v2 (central (fromBlocks (twoPlaceBlock ((1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).map
        (PowerSeries.C)) ((1 : ℕ) : PowerSeries ℚ_[2]) 1 1) 0 0
        ((2 : PowerSeries ℚ_[2]) • (1 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) _))).det) =
      v2 (fromBlocks (twoPlaceBlock (1 : Matrix (Fin 2) (Fin 2) ℚ_[2]) ((1 : ℕ) : ℚ_[2])
        ((1 : ℤ) : ℚ_[2]) ((1 : ℤ) : ℚ_[2])) 0 0
        ((2 : ℚ_[2]) • (1 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℚ_[2]))).det := by
  refine v2_central_det_of_local_blocks 1 _ 1 1 (Equiv.refl _)
    ((1 : Matrix (Fin 2) (Fin 2) ℚ_[2]).map PowerSeries.C) 1 1 1
    ((2 : PowerSeries ℚ_[2]) • (1 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) _)) ?_ ?_ ?_ _ 1 ?_ ?_ ?_ ?_
  · simp
  · simp [central, v2]
  · simp [central, v2]
  · ext i j; simp [central, Matrix.one_apply, apply_ite]
  · simp [central]
  · simp [central]
  · ext i j
    by_cases h : i = j
    · subst h; simp [central]
      exact map_ofNat PowerSeries.constantCoeff 2
    · simp [central, h]

end ZInQ.Contrib.CloudB3RC53.Calibration
