import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.OuterIntegral
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.CoordinateUnit

/-!
# RC53 SwitchInputs: the stage coordinates are the switch coordinates

Lemma `ex:limits-derivative-switch` (tex L4834–4907) and its use in Proposition
`ex:limits-uniform-lower-bound` (tex L4940–4950, L5137–5153): "Lemma `ex:limits-derivative-switch`
therefore makes this class span the new generic kernel and preserves the valuation of its
class-functional determinant coordinate". The switching data of `UniformSwitch` ask, at each switch,
that the old and new stage coordinates be the finite and singular switch coordinates `u_F`, `u_S` of
RC16's `switch_coord_relation` (the field `CoordStep` of `UniformSwitch/Regularity.lean`, and the
per-instance field `OuterSwitchStep.coords` of `SwitchInputs/OuterIntegral.lean`).

**The determinant computation (PROVED).** Generically the strict complex has `H¹ = 0` and
`H²(C_str) = ⟨A, B⟩^∨` (dual basis `A*, B*`), so the minimal models of the two plane conditions are
the cones of the connecting maps: `C_F = [F_v --∂_F--> H²(C_str)]` and `C_S = [S_v --∂_S--> H²(C_str)]`
in degrees one and two. With RC16's connecting maps (`bdryF`, `bdryS`; `∂_F x = ε e₂(x, v) B*`,
`∂_S y = σ ε e₂(v, J y) A*`) their matrices are `oldMat` and `newMat`, the actual old class is
`v = f(A)` with functional `λ_A` (the first dual coordinate), and the derivative class is `J v = s(B)`
with functional `λ_B`. We compute their class-functional coordinates (RC15's `IsClassFunctionalCoord`)
exactly: `-ε⁻¹` and `(σ ε)⁻¹`, and show that they are the switch coordinates `u_F`, `u_S` of the
switch data `planeSwitchData` with strict volume form `ω = dualVol` and normalizations
`μ_F = μ_S = -1` (`stage_coords_eq_switch_coords`). Integral changes of basis of the stage models
multiply the coordinates by units (`MinimalComplexes/CoordinateUnit`), which the switch data absorb
into unit normalizations `μ_F = -ι(c)`, `μ_S = -ι(c')` (`coordStep_of_switch`).

**GLUE (new style).** `StageModelLink`: the stage coordinate is a unit multiple of the coordinate of
the generic minimal model of its plane condition. Its content is the identification of the generic
minimal model of `C_F` (resp. `C_S`) with the cone of `∂_F` (resp. `∂_S`), i.e. the strict/relaxed
duality `H²(C_str) ≅ H¹(C_rel)^∨` of Nekovář 6.3.3–6.3.4 (RC16's modelling input for `bdry`), together
with an integral change of basis between the stage model and that minimal model. For `2 × 2` stage
models related to the minimal model by an integral change of basis it is PROVED
(`stageModelLink_of_baseChange`).

Nodes:
* `oldMat_eq_bdryF`, `newMat_eq_bdryS` (PROVED): the stage matrices are the matrices of `∂_F`, `∂_S`.
* `oldMat_coord`, `newMat_coord` (PROVED, tex L4888–4906): the class-functional coordinates.
* `stage_coords_eq_switch_coords` (PROVED): they are `u_F`, `u_S` of `planeSwitchData`.
* `stageModelLink_of_baseChange` (PROVED): the GLUE link from an integral change of basis.
* `coordStep_of_switch` (PROVED from the links): UniformSwitch's `CoordStep`.
* `outerCoords_of_switch` (PROVED from the links): the field `OuterSwitchStep.coords`.
* Non-vacuity (LESSON 2): `exStage_old`, `exStage_new`, `exPlaneCoordStep`, `exOuterLink`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Module Matrix Filter ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Central
  ZInQ.Contrib.CloudB3RC53.UniformSwitch

section Core

variable {K : Type*} [Field K]

/-- The finite localization `f = (A ↦ v, B ↦ 0)` on `H¹(C_rel) = K²` (tex L4888–4890). -/
def planeF (v : Fin 2 → K) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := (Pi.basisFun K (Fin 2)).constr K ![v, 0]

/-- The singular localization `s = (A ↦ 0, B ↦ J v)` ((4.2), tex L4888–4890). -/
def planeS (J : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (Pi.basisFun K (Fin 2)).constr K ![0, J *ᵥ v]

theorem planeF_A (v : Fin 2 → K) : planeF v (Pi.basisFun K (Fin 2) 0) = v := by
  rw [planeF, Module.Basis.constr_basis]; rfl
theorem planeF_B (v : Fin 2 → K) : planeF v (Pi.basisFun K (Fin 2) 1) = 0 := by
  rw [planeF, Module.Basis.constr_basis]; rfl
theorem planeS_A (J : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    planeS J v (Pi.basisFun K (Fin 2) 0) = 0 := by
  rw [planeS, Module.Basis.constr_basis]; rfl
theorem planeS_B (J : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    planeS J v (Pi.basisFun K (Fin 2) 1) = J *ᵥ v := by
  rw [planeS, Module.Basis.constr_basis]; rfl

/-- The matrix of the finite connecting map `∂_F : F_v → H²(C_str) = ⟨A*, B*⟩`, i.e. the differential
of the generic minimal model `[F_v → H²(C_str)]` of `C_F`. -/
def oldMat (ε : K) (v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K := !![0, 0; ε * v 1, -(ε * v 0)]

/-- The matrix of the singular connecting map `∂_S : S_v → H²(C_str)`. -/
def newMat (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![σ * ε * (J *ᵥ v) 1, -(σ * ε * (J *ᵥ v) 0); 0, 0]

/-- **`oldMat` is the matrix of `∂_F`** in the bases `e_j` of `F_v` and `A*, B*` of `H²(C_str)`
(RC16 `bdryF_eq`, tex L4888–4906). PROVED. -/
theorem oldMat_eq_bdryF (ε σ : K) {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    (v : Fin 2 → K) (i j : Fin 2) :
    oldMat ε v i j = bdryF ε σ J (planeF v) (planeS J v) (Pi.single j 1) (Pi.single i 1) := by
  rw [bdryF_eq (Pi.basisFun K (Fin 2)) hJ2 (planeS_A J v) (planeS_B J v)]
  fin_cases i <;> fin_cases j <;> simp [oldMat, weil_apply]

/-- `J² = 1` and `det J = -1` force `tr J = 0`. -/
theorem trace_zero_of_sq_det {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    (hJdet : J.det = -1) : J 0 0 + J 1 1 = 0 := by
  have e01 := congrFun (congrFun hJ2 0) 1
  have e10 := congrFun (congrFun hJ2 1) 0
  have e00 := congrFun (congrFun hJ2 0) 0
  have e11 := congrFun (congrFun hJ2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10 e00 e11
  rw [Matrix.det_fin_two] at hJdet
  by_contra h
  have h01 : J 0 1 = 0 := by
    have : J 0 1 * (J 0 0 + J 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right h
  have h10 : J 1 0 = 0 := by
    have : J 1 0 * (J 0 0 + J 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right h
  rw [h01, h10] at e00 e11 hJdet
  apply h
  have : (J 0 0 + J 1 1) * (J 0 0 + J 1 1) = 0 := by linear_combination e00 + e11 + 2 * hJdet
  exact mul_self_eq_zero.1 this

/-- **`newMat` is the matrix of `∂_S`** (RC16 `bdryS_eq`). PROVED. -/
theorem newMat_eq_bdryS (ε σ : K) {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    (hJdet : J.det = -1) (v : Fin 2 → K) (i j : Fin 2) :
    newMat ε σ J v i j = bdryS ε σ J (planeF v) (planeS J v) (Pi.single j 1) (Pi.single i 1) := by
  rw [bdryS_eq (Pi.basisFun K (Fin 2)) (planeF_A v) (planeF_B v)]
  have htr := trace_zero_of_sq_det hJ2 hJdet
  fin_cases i <;> fin_cases j <;>
    simp [newMat, weil_apply, mulVec, dotProduct, Fin.sum_univ_two]
  · linear_combination (σ * ε * v 1) * htr
  · linear_combination (-(σ * ε * v 0)) * htr

/-- **The old stage coordinate** (tex L4888–4906): the class-functional coordinate of the actual
old class `v` and its functional `λ_A` (first dual coordinate) on `[F_v --∂_F--> H²(C_str)]` is
`-ε⁻¹`. PROVED. -/
theorem oldMat_coord {ε : K} (hε : ε ≠ 0) (v : Fin 2 → K) :
    IsClassFunctionalCoord (oldMat ε v) v (Pi.single 0 1) (-ε⁻¹) := by
  unfold IsClassFunctionalCoord
  rw [oldMat, adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, Pi.single_apply] <;> field_simp

/-- **The new stage coordinate**: the class-functional coordinate of the derivative class `J v`
and its functional `λ_B` (second dual coordinate) on `[S_v --∂_S--> H²(C_str)]` is `(σ ε)⁻¹`.
PROVED. -/
theorem newMat_coord {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0) (J : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 → K) :
    IsClassFunctionalCoord (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1) ((σ * ε)⁻¹) := by
  unfold IsClassFunctionalCoord
  rw [newMat, adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, Pi.single_apply] <;> field_simp

/-- The plane switch data: RC16's switch data on `H¹(C_rel) = K²` with `f`, `s` as above, the strict
volume form `ω = dualVol` (unit volume of `A* ∧ B*`), normalizations `μ_F`, `μ_S`, and admissible
complements (which exist by `switch_exists_admissible_F/S`). -/
def planeSwitchData {ε σ : K} (hε : ε ≠ 0) (hσ : σ * σ = 1) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) (hJdet : J.det = -1) {v : Fin 2 → K} (hv : v ≠ 0) (μF μS : K) :
    SwitchCoordData K :=
  let b := Pi.basisFun K (Fin 2)
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul_eq_one hσ
  have hF := switch_exists_admissible_F (σ := σ) b hε hJ2 hv (planeF_A v) (planeS_A J v)
    (planeS_B J v) (dualVol_isAlt b) (dualVol_ne_zero b) (one_ne_zero (α := K))
  have hS := switch_exists_admissible_S b hε hσ0 hJ2 hJdet hv (planeF_A v) (planeF_B v)
    (planeS_B J v) (dualVol_isAlt b) (dualVol_ne_zero b) (μS := (1 : K)) one_ne_zero
  { ε := ε, σ := σ, J := J, f := planeF v, s := planeS J v, v := v, ω := dualVol b,
    μF := μF, μS := μS, x := hF.choose, y := hS.choose, w := hF.choose_spec.choose,
    w' := hS.choose_spec.choose, hσ := hσ, hJ2 := hJ2, hJdet := hJdet, hfA := planeF_A v,
    hsA := planeS_A J v, hfB := planeF_B v, hsB := planeS_B J v, hω := dualVol_isAlt b,
    hxw := hF.choose_spec.choose_spec.2, hyw := hS.choose_spec.choose_spec.2 }

theorem planeSwitchData_uF {ε σ : K} (hε : ε ≠ 0) (hσ : σ * σ = 1) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) (hJdet : J.det = -1) {v : Fin 2 → K} (hv : v ≠ 0) (μF μS : K) :
    (planeSwitchData hε hσ hJ2 hJdet hv μF μS).uF = μF / ε := by
  set X := planeSwitchData hε hσ hJ2 hJdet hv μF μS
  rw [SwitchCoordData.uF, coordF_eq (Pi.basisFun K (Fin 2)) X.hJ2 X.hfA X.hsA X.hsB X.hω X.μF X.hxw]
  change μF / (ε * dualVol (Pi.basisFun K (Fin 2)) _ _) = _
  rw [dualVol_basis, mul_one]

theorem planeSwitchData_uS {ε σ : K} (hε : ε ≠ 0) (hσ : σ * σ = 1) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) (hJdet : J.det = -1) {v : Fin 2 → K} (hv : v ≠ 0) (μF μS : K) :
    (planeSwitchData hε hσ hJ2 hJdet hv μF μS).uS = -μS / (σ * ε) := by
  set X := planeSwitchData hε hσ hJ2 hJdet hv μF μS
  rw [SwitchCoordData.uS, coordS_eq (Pi.basisFun K (Fin 2)) X.hJ2 X.hJdet X.hfA X.hfB X.hsB X.hω X.μS
    X.hyw]
  change -μS / (σ * (ε * dualVol (Pi.basisFun K (Fin 2)) _ _)) = _
  rw [dualVol_basis, mul_one]

/-- **The stage coordinates are the switch coordinates** (tex L4888–4906, L5137–5153): with
`μ_F = μ_S = -1`, the class-functional coordinates of the old stage `[F_v → H²(C_str)]` (actual class
`v`, functional `λ_A`) and of the new stage `[S_v → H²(C_str)]` (derivative `J v`, functional `λ_B`)
are `u_F` and `u_S` of `planeSwitchData`. PROVED. -/
theorem stage_coords_eq_switch_coords {ε σ : K} (hε : ε ≠ 0) (hσ : σ * σ = 1)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) (hJdet : J.det = -1) {v : Fin 2 → K}
    (hv : v ≠ 0) :
    IsClassFunctionalCoord (oldMat ε v) v (Pi.single 0 1)
        (planeSwitchData hε hσ hJ2 hJdet hv (-1) (-1)).uF ∧
      IsClassFunctionalCoord (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1)
        (planeSwitchData hε hσ hJ2 hJdet hv (-1) (-1)).uS := by
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul_eq_one hσ
  rw [planeSwitchData_uF, planeSwitchData_uS]
  refine ⟨?_, ?_⟩
  · have := oldMat_coord hε v
    rwa [show (-1 : K) / ε = -ε⁻¹ by field_simp]
  · have := newMat_coord hε hσ0 J v
    rwa [show -(-1 : K) / (σ * ε) = (σ * ε)⁻¹ by field_simp]

/-- The adjugate of the old stage matrix is nonzero when `ε ≠ 0`, `v ≠ 0`. -/
theorem oldMat_adjugate_ne_zero {ε : K} (hε : ε ≠ 0) {v : Fin 2 → K} (hv : v ≠ 0) :
    (oldMat ε v).adjugate ≠ 0 := by
  intro h
  apply hv
  ext i
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  rw [oldMat, adjugate_fin_two_of] at h0 h1
  simp at h0 h1
  fin_cases i
  · simpa [hε] using h0
  · simpa [hε] using h1

/-- The adjugate of the new stage matrix is nonzero when `ε, σ ≠ 0`, `J v ≠ 0`. -/
theorem newMat_adjugate_ne_zero {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} {v : Fin 2 → K} (hv : J *ᵥ v ≠ 0) :
    (newMat ε σ J v).adjugate ≠ 0 := by
  intro h
  apply hv
  ext i
  have h0 := congrFun (congrFun h 0) 1
  have h1 := congrFun (congrFun h 1) 1
  rw [newMat, adjugate_fin_two_of] at h0 h1
  simp at h0 h1
  fin_cases i
  · simpa [hε, hσ] using h0
  · simpa [hε, hσ] using h1

end Core

/-! ### The GLUE link and the switch fields -/

section Link

variable {A F : Type} [CommRing A] [Field F]

/-- **GLUE (new style): the stage coordinate is a unit multiple of the minimal-model coordinate**
(tex L4834–4907, L4976–4996). For a stage coordinate `u`, the generic minimal model `M` of its plane
condition with class `z₀` and functional `l₀`: there is a unit `c` of `A` with `u = ι(c) · u₀` for
every coordinate `u₀` of `(M, z₀, l₀)`. Content: the identification of the generic minimal model of
`C_F` (resp. `C_S`) with the cone `[F_v → H²(C_str)]` (resp. `[S_v → H²(C_str)]`) — the strict/relaxed
duality of Nekovář 6.3.3–6.3.4 — and an integral change of basis to the stage model (which multiplies
the coordinate by a unit: `stageModelLink_of_baseChange`). -/
def StageModelLink (ι : A →+* F) (u : F) (M : Matrix (Fin 2) (Fin 2) F) (z₀ l₀ : Fin 2 → F) : Prop :=
  ∃ c : A, IsUnit c ∧ ∀ u₀, IsClassFunctionalCoord M z₀ l₀ u₀ → u = ι c * u₀

/-- **The link from an integral change of basis** (tex L4834–4907 with `CoordinateUnit`): if a
`2 × 2` stage model `D` over `A` (with class `z`, functional `w` and coordinate `u`) is related to the
minimal model `M` by integral invertible `P, Q` (`P D Q = M` over `F`, `z = Q z₀`, `w = l₀ P`), then
`StageModelLink` holds with the unit `c = det P · det Q`. PROVED. -/
theorem stageModelLink_of_baseChange (ι : A →+* F) (D P Q : Matrix (Fin 2) (Fin 2) A)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (z w : Fin 2 → A) (u : F)
    (hu : IsClassFunctionalCoord (D.map ι) (fun i => ι (z i)) (fun i => ι (w i)) u)
    (M : Matrix (Fin 2) (Fin 2) F) (z₀ l₀ : Fin 2 → F) (hM : (P * D * Q).map ι = M)
    (hz : (fun i => ι (z i)) = Q.map ι *ᵥ z₀) (hw : (fun i => ι (w i)) = l₀ ᵥ* P.map ι)
    (hadj : M.adjugate ≠ 0) :
    StageModelLink ι u M z₀ l₀ := by
  refine ⟨P.det * Q.det, hP.mul hQ, fun u₀ hu₀ => ?_⟩
  have hPι : IsUnit (P.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hP.map ι
  have hQι : IsUnit (Q.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hQ.map ι
  have h := (MinimalComplexes.coordinateBaseChangeUnit_proof F 2 (D.map ι) (P.map ι) (Q.map ι)
    (fun i => ι (z i)) (fun i => ι (w i)) u hPι hQι).1 hu
  have hQinv : (Q.map ι)⁻¹ *ᵥ (fun i => ι (z i)) = z₀ := by
    rw [hz, mulVec_mulVec, Matrix.nonsing_inv_mul _ hQι, one_mulVec]
  have hPinv : (fun i => ι (w i)) ᵥ* (P.map ι)⁻¹ = l₀ := by
    rw [hw, vecMul_vecMul, Matrix.mul_nonsing_inv _ hPι, vecMul_one]
  rw [hQinv, hPinv, ← Matrix.map_mul, ← Matrix.map_mul, hM] at h
  have heq := isClassFunctionalCoord_unique hadj h hu₀
  have hdet : ι (P.det * Q.det) = (P.map ι).det * (Q.map ι).det := by
    rw [map_mul, RingHom.map_det, RingHom.map_det]; rfl
  have hne : (P.map ι).det * (Q.map ι).det ≠ 0 := (hPι.mul hQι).ne_zero
  rw [← heq, hdet, Ring.inverse_eq_inv', ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- The sign `σ` (with `σ² = 1`) lies in the image of `A`. -/
theorem sign_in_image (ι : A →+* F) {σ : F} (hσ : σ * σ = 1) : ∃ σ₀ : A, σ = ι σ₀ := by
  rcases mul_self_eq_one_iff.1 hσ with rfl | rfl
  · exact ⟨1, (map_one ι).symm⟩
  · exact ⟨-1, by rw [map_neg, map_one]⟩

/-- **UniformSwitch's `CoordStep` from the switch plane** (tex L4940–4950, L5137–5153). Let `u`, `u'`
be the old and new stage coordinates, linked (GLUE `StageModelLink`) to the generic minimal models
`[F_v → H²(C_str)]` (class `v`, functional `λ_A`) and `[S_v → H²(C_str)]` (class `J v`, functional
`λ_B`) of the switch plane. Then the old coordinate is `u_F` and the new one `u_S` of the plane switch
data with unit normalizations `μ_F = -ι(c)`, `μ_S = -ι(c')`, and the sign `σ` comes from `A`: an
actual `CoordStep ι u u'`. PROVED (from the links). -/
noncomputable def coordStep_of_switch (ι : A →+* F) {ε σ : F} (hε : ε ≠ 0) (hσ : σ * σ = 1)
    {J : Matrix (Fin 2) (Fin 2) F} (hJ2 : J * J = 1) (hJdet : J.det = -1) {v : Fin 2 → F}
    (hv : v ≠ 0) {u u' : F} (hold : StageModelLink ι u (oldMat ε v) v (Pi.single 0 1))
    (hnew : StageModelLink ι u' (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1)) :
    CoordStep ι u u' :=
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul_eq_one hσ
  { X := planeSwitchData hε hσ hJ2 hJdet hv (-ι hold.choose) (-ι hnew.choose)
    mF := -hold.choose
    mS := -hnew.choose
    σ₀ := (sign_in_image ι hσ).choose
    hmF := hold.choose_spec.1.neg
    hmS := hnew.choose_spec.1.neg
    hμF := by simp [planeSwitchData]
    hμS := by simp [planeSwitchData]
    hσ₀ := (sign_in_image ι hσ).choose_spec
    hu := (hold.choose_spec.2 _ (oldMat_coord hε v)).trans (by
      rw [planeSwitchData_uF]; field_simp)
    hu' := (hnew.choose_spec.2 _ (newMat_coord hε hσ0 J v)).trans (by
      rw [planeSwitchData_uS]; field_simp) }

end Link

/-! ### The outer per-instance identification -/

section Outer

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {J : Type} (𝒰 : Ultrafilter J)

/-- **The outer per-instance switch coordinates** (tex L4940–4950; the field
`OuterSwitchStep.coords` of `SwitchInputs/OuterIntegral.lean`). Let `cOld`, `cNew` be the inner
coordinates of two consecutive outer configurations. Suppose, on an outer-large set, each instance has
switch-plane data `(ε, σ, J, v)` and its two inner coordinates are linked (GLUE `StageModelLink` over
`algebraMap R K`) to the generic minimal models of the switch plane. Then on that set there are
switch data with unit normalizations `μ_F = algebraMap mF`, `μ_S = algebraMap mS` whose `u_F`, `u_S`
are the old and new inner coordinates — exactly the clause of `OuterSwitchStep.coords`.
PROVED (from the links). -/
theorem outerCoords_of_switch (cOld cNew : J → K)
    (hlink : ∀ᶠ j in (𝒰 : Filter J), ∃ (ε σ : K) (hε : ε ≠ 0) (hσ : σ * σ = 1)
      (Jm : Matrix (Fin 2) (Fin 2) K) (hJ2 : Jm * Jm = 1) (hJdet : Jm.det = -1) (v : Fin 2 → K)
      (hv : v ≠ 0),
      StageModelLink (algebraMap R K) (cOld j) (oldMat ε v) v (Pi.single 0 1) ∧
        StageModelLink (algebraMap R K) (cNew j) (newMat ε σ Jm v) (Jm *ᵥ v) (Pi.single 1 1)) :
    ∀ᶠ j in (𝒰 : Filter J), ∃ (Y : SwitchCoordData K) (mF mS : R),
      IsUnit mF ∧ IsUnit mS ∧ Y.μF = algebraMap R K mF ∧ Y.μS = algebraMap R K mS ∧
        cOld j = Y.uF ∧ cNew j = Y.uS := by
  refine hlink.mono fun j hj => ?_
  obtain ⟨ε, σ, hε, hσ, Jm, hJ2, hJdet, v, hv, hold, hnew⟩ := hj
  let C := coordStep_of_switch (algebraMap R K) hε hσ hJ2 hJdet hv hold hnew
  exact ⟨C.X, C.mF, C.mS, C.hmF, C.hmS, C.hμF, C.hμS, C.hu, C.hu'⟩

end Outer

/-! ### Non-vacuity (LESSON 2) -/

section Examples

/-- The example plane over `ℚ`: `ε = σ = 1`, `J = diag(1, -1)`, `v = e₀`. -/
abbrev exV : Fin 2 → ℚ := ![1, 0]

theorem exV_ne_zero : exV ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

theorem exJ_v_ne_zero : switchJ0 ℚ *ᵥ exV ≠ 0 := by
  intro h; have := congrFun h 0; simp [switchJ0, mulVec, dotProduct, Fin.sum_univ_two] at this

/-- The old stage over `A = F = ℚ`: the generic minimal model `[F_v → H²(C_str)]` itself. -/
def exStage_old : TwoTermStage (RingHom.id ℚ) where
  n := 1
  D := oldMat 1 exV
  z := exV
  w := Pi.single 0 1
  u := -1
  hz := by ext i; fin_cases i <;> simp [oldMat, mulVec, dotProduct, Fin.sum_univ_two]
  hw := by ext j; fin_cases j <;> simp [oldMat, vecMul, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  hu := by
    have := oldMat_coord (one_ne_zero (α := ℚ)) exV
    simpa using this

/-- The new stage over `ℚ`: the generic minimal model `[S_v → H²(C_str)]`. -/
def exStage_new : TwoTermStage (RingHom.id ℚ) where
  n := 1
  D := newMat 1 1 (switchJ0 ℚ) exV
  z := switchJ0 ℚ *ᵥ exV
  w := Pi.single 1 1
  u := 1
  hz := by
    ext i; fin_cases i <;> simp [newMat, switchJ0, mulVec, dotProduct, Fin.sum_univ_two]
  hw := by
    ext j; fin_cases j <;>
      simp [newMat, switchJ0, vecMul, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  hu := by
    have := newMat_coord (one_ne_zero (α := ℚ)) one_ne_zero (switchJ0 ℚ) exV
    simpa using this

theorem exLink_old : StageModelLink (RingHom.id ℚ) exStage_old.u (oldMat 1 exV) exV (Pi.single 0 1) :=
  ⟨1, isUnit_one, fun u₀ hu₀ => by
    have h := isClassFunctionalCoord_unique (oldMat_adjugate_ne_zero one_ne_zero exV_ne_zero)
      exStage_old.hu hu₀
    simpa using h⟩

theorem exLink_new : StageModelLink (RingHom.id ℚ) exStage_new.u (newMat 1 1 (switchJ0 ℚ) exV)
    (switchJ0 ℚ *ᵥ exV) (Pi.single 1 1) :=
  ⟨1, isUnit_one, fun u₀ hu₀ => by
    have h := isClassFunctionalCoord_unique
      (newMat_adjugate_ne_zero one_ne_zero one_ne_zero exJ_v_ne_zero) exStage_new.hu hu₀
    simpa using h⟩

/-- **Non-vacuity of the links and of `coordStep_of_switch`**: an actual `CoordStep` between the
example stages over `ℚ`, with genuine switch coordinates `u_F = -1`, `u_S = 1`. -/
noncomputable def exPlaneCoordStep : CoordStep (RingHom.id ℚ) exStage_old.u exStage_new.u :=
  coordStep_of_switch (RingHom.id ℚ) one_ne_zero (mul_one 1) (switchJ0_sq (K := ℚ)) (switchJ0_det (K := ℚ))
    exV_ne_zero exLink_old exLink_new

/-- **Non-vacuity of the outer link hypothesis**: constant inner coordinates `-1`, `1` over
`ℤ ⊆ ℚ` satisfy the hypotheses of `outerCoords_of_switch` along any ultrafilter. -/
theorem exOuterLink (𝒰 : Ultrafilter ℕ) :
    ∀ᶠ j in (𝒰 : Filter ℕ), ∃ (Y : SwitchCoordData ℚ) (mF mS : ℤ),
      IsUnit mF ∧ IsUnit mS ∧ Y.μF = algebraMap ℤ ℚ mF ∧ Y.μS = algebraMap ℤ ℚ mS ∧
        (fun _ => (-1 : ℚ)) j = Y.uF ∧ (fun _ => (1 : ℚ)) j = Y.uS := by
  refine outerCoords_of_switch 𝒰 (R := ℤ) _ _ (Eventually.of_forall fun _ =>
    ⟨1, 1, one_ne_zero, mul_one 1, switchJ0 ℚ, switchJ0_sq (K := ℚ), switchJ0_det (K := ℚ), exV, exV_ne_zero,
      ⟨1, isUnit_one, fun u₀ hu₀ => ?_⟩, ⟨1, isUnit_one, fun u₀ hu₀ => ?_⟩⟩)
  · have h := isClassFunctionalCoord_unique (oldMat_adjugate_ne_zero one_ne_zero exV_ne_zero)
      (by simpa using oldMat_coord (one_ne_zero (α := ℚ)) exV) hu₀
    simp [← h]
  · have h := isClassFunctionalCoord_unique
      (newMat_adjugate_ne_zero one_ne_zero one_ne_zero exJ_v_ne_zero)
      (by simpa using newMat_coord (one_ne_zero (α := ℚ)) one_ne_zero (switchJ0 ℚ) exV) hu₀
    simp [← h]

end Examples

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
