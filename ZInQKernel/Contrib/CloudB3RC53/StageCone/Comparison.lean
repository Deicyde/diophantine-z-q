import ZInQKernel.Contrib.CloudB3RC53.StageCone.AugExact
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.StageLink

/-!
# Stage cone, part 2: the integral content of `StageConeIdentification`

Lemma `ex:limits-derivative-switch`, tex L4888–4906, and tex L4360–4366 ("All cancellable disks
have unit differential, so integral determinant base change identifies the coordinate").

`SwitchInputs/StageLink.lean` names the GLUE `StageConeIdentification`: each stage model reduces, by
an integral change of basis of unit determinant, to the cone `M` of the connecting map (`oldMat`,
`newMat`) plus unit disks (`ConeReduction`). `SwitchInputs/ConeIdent.lean` proves the generic-fibre
half and notes that the integral half does not follow from generic data, since an equivalence over
the fraction field does not fix the integral lattice.

This file isolates that integral content exactly. A **generic comparison**
`g : StageMap ι S M z₀ l₀` is a chain map over `F` from the stage complex `[F^N --D--> F^N]` to
`[F² --M--> F²]` with `f¹ z = z₀` and `l₀ f² = w`. Such maps live over the fraction field and carry
no integral information by themselves (Part A of `ConeIdent.lean` matches the cohomologies). The
integral information is one number: the torsion of the cone of the augmented comparison,
`g.coneTorsion`, relative to the standard bases.

* `stage_coord_eq` (PROVED): `u = (−1)^{N+1} · u₀ · τ(cone g)⁻¹` for any generic comparison, where
  `u` and `u₀` are the stage and cone coordinates (both nonzero, adjugates nonzero; acyclicity of
  the augmented complexes is derived, `StageCone/AugExact.lean`).
* **`stageModelLink_iff` (PROVED)**: `StageModelLink ι u M z₀ l₀` holds iff
  `τ(cone g) ∈ (−1)^{N+1} · ι(Aˣ)` (`StageMap.IntegralUnit`), for ANY generic comparison `g`.
  So the integral half of `StageConeIdentification` is equivalent to the single lattice statement
  "the comparison of the stage model with the cone preserves the integral determinant lattice up to
  sign".
* `integralUnit_of_coneReduction` (PROVED): `ConeReduction` implies `IntegralUnit` for every generic
  comparison.
* `StageConeComparison` (the sharpened GLUE) and `coordStep_of_coneComparison` (PROVED from it): an
  actual `CoordStep`.
* Non-vacuity: the `3 × 3` stage `ex3Stage` of `StageLink.lean` with the comparison
  `f¹ = f² = [I | 0]` (`ex3StageMap`) satisfies `IntegralUnit` (`ex3_integralUnit`); with the
  identity comparison of the `2 × 2` new stage, `StageConeComparison` holds
  (`ex3_stageConeComparison`) and gives an actual `CoordStep` (`ex3CoordStep'`).

The stage models in the project are abstract (`UniformSwitch.TwoTermStage`), and no stage model is
constructed from the genuine integral Selmer complexes. So `IntegralUnit` cannot be proved
outright. It is the named remaining input. It is implied by `ConeReduction`
(`integralUnit_of_coneReduction`) and asks for no block form.

**Classification.** PROVED (`StageConeComparison` is the named GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.StageCone

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Uniform

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}

theorem stage_hz (S : TwoTermStage ι) :
    (twoTerm (S.D.map ι)).d1 *ᵥ (fun i => ι (S.z i)) = 0 := by
  funext i
  change ((S.D.map ι) *ᵥ (ι ∘ S.z)) i = 0
  rw [← RingHom.map_mulVec, S.hz]
  exact map_zero ι

theorem stage_hw (S : TwoTermStage ι) :
    (fun i => ι (S.w i)) ᵥ* (twoTerm (S.D.map ι)).d1 = 0 := by
  funext j
  change ((ι ∘ S.w) ᵥ* (S.D.map ι)) j = 0
  rw [← RingHom.map_vecMul, S.hw]
  exact map_zero ι

/-- **A generic comparison** of the stage model `S` with the cone `[F² --M--> F²]` (class `z₀`,
functional `l₀`): a chain map over `F` carrying the class to the class and pulling the functional
back to the functional. -/
structure StageMap (S : TwoTermStage ι) (M : Matrix (Fin 2) (Fin 2) F) (z₀ l₀ : Fin 2 → F) where
  /-- The chain map. -/
  f : FourMap (twoTerm (S.D.map ι)) (twoTerm M)
  /-- `f¹ z = z₀`. -/
  hz : f.f1 *ᵥ (fun i => ι (S.z i)) = z₀
  /-- `l₀ f² = w`. -/
  hl : l₀ ᵥ* f.f2 = fun i => ι (S.w i)

variable {S : TwoTermStage ι} {M : Matrix (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F}

/-- The sign `(−1)^{|κ_odd(aug S)|}`. -/
abbrev stageSign (S : TwoTermStage ι) : F :=
  (-1) ^ Fintype.card (Fin (S.n + 1) ⊕ (Empty ⊕ Unit))

/-- **The torsion of the cone of the augmented comparison**, in the standard bases. -/
def StageMap.coneTorsion (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) : F :=
  torsion (BasedCx.cone (g.f.augMap _ _ (stage_hz S) (stage_hw S) z₀ l₀ hz₀ hl₀ g.hz g.hl))
    ((σ₀ 2).sumCongr (σ₀ (S.n + 1)).symm)

/-- **The integral lattice condition**: the cone torsion is an integral unit up to the canonical
sign. -/
def StageMap.IntegralUnit (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) : Prop :=
  ∃ c : Aˣ, g.coneTorsion hz₀ hl₀ = stageSign S * ι c

/-- **The coordinates through a generic comparison** (PROVED):
`u = (−1)^{N+1} · u₀ · τ(cone g)⁻¹`. -/
theorem stage_coord_eq (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    {u₀ : F} (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMadj : M.adjugate ≠ 0) :
    S.u = stageSign S * u₀ * (g.coneTorsion hz₀ hl₀)⁻¹ := by
  obtain ⟨hC⟩ := contraction_aug_twoTerm _ _ _ _ (stage_hz S) (stage_hw S) S.hu hS0 hSadj
  obtain ⟨hD⟩ := contraction_aug_twoTerm _ _ _ _ hz₀ hl₀ hu₀ hu₀0 hMadj
  have h := kmCoord_eq_of_fourMap g.f _ _ (stage_hz S) (stage_hw S) z₀ l₀ hz₀ hl₀ g.hz g.hl hC hD
    (σ₀ (S.n + 1)) (σ₀ 2)
  rw [kmCoord_twoTerm _ _ _ _ _ _ hC S.hu, kmCoord_twoTerm _ _ _ _ _ _ hD hu₀] at h
  exact h

theorem stageSign_mul_self (S : TwoTermStage ι) : stageSign S * stageSign S = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩

/-- `a u₀ = s u₀ t⁻¹` with `s² = 1`, `u₀ ≠ 0` gives `t = s a⁻¹`. -/
theorem solve_cone {s a u₀ t : F} (hs : s * s = 1) (hu₀ : u₀ ≠ 0) (e : a * u₀ = s * u₀ * t⁻¹) :
    t = s * a⁻¹ := by
  have ha : a = s * t⁻¹ := mul_right_cancel₀ hu₀ (by rw [e]; ring)
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [ha, mul_inv, inv_inv, hsi, ← mul_assoc, hs, one_mul]

/-- `t = s a` with `s² = 1` gives `s u₀ t⁻¹ = a⁻¹ u₀`. -/
theorem coord_of_cone {s a u₀ : F} (hs : s * s = 1) : s * u₀ * (s * a)⁻¹ = a⁻¹ * u₀ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [mul_inv, hsi]
  calc s * u₀ * (s * a⁻¹) = (s * s) * a⁻¹ * u₀ := by ring
    _ = a⁻¹ * u₀ := by rw [hs, one_mul]

/-- **The integral half of `StageConeIdentification` is exactly the lattice condition** (PROVED):
for nondegenerate stage and cone and ANY generic comparison `g`, `StageModelLink` holds iff the
cone torsion of `g` is an integral unit up to the canonical sign. -/
theorem stageModelLink_iff (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    {u₀ : F} (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMadj : M.adjugate ≠ 0) :
    StageModelLink ι S.u M z₀ l₀ ↔ g.IntegralUnit hz₀ hl₀ := by
  have key := stage_coord_eq g hz₀ hl₀ hS0 hSadj hu₀ hu₀0 hMadj
  have hs := stageSign_mul_self S
  have ht : g.coneTorsion hz₀ hl₀ ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero, mul_zero] at key; exact hS0 key
  constructor
  · rintro ⟨c, hc, hlink⟩
    obtain ⟨c, rfl⟩ := hc
    have hιc : ι (c : A) * ι ((c⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨c⁻¹, ?_⟩
    rw [← inv_eq_of_mul_eq_one_right hιc]
    exact solve_cone hs hu₀0 ((hlink u₀ hu₀).symm.trans key)
  · rintro ⟨c, hc⟩
    have hιc : ι (c : A) * ι ((c⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨((c⁻¹ : Aˣ) : A), Units.isUnit _, fun u₁ hu₁ => ?_⟩
    rw [isClassFunctionalCoord_unique hMadj hu₁ hu₀, key, hc, ← inv_eq_of_mul_eq_one_right hιc]
    exact coord_of_cone hs

/-- **`ConeReduction` gives the lattice condition for every generic comparison** (PROVED). -/
theorem integralUnit_of_coneReduction (g : StageMap S M z₀ l₀) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    {u₀ : F} (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMadj : M.adjugate ≠ 0)
    (hred : ConeReduction ι S.D S.z S.w M z₀ l₀) : g.IntegralUnit hz₀ hl₀ :=
  (stageModelLink_iff g hz₀ hl₀ hS0 hSadj hu₀ hu₀0 hMadj).1
    (stageModelLink_of_coneReduction ι S.D S.z S.w S.u S.hu M z₀ l₀ hred hMadj)

/-! ### The sharpened GLUE and the coordinate step -/

section Glue

theorem oldMat_hz (ε : F) (v : Fin 2 → F) : (twoTerm (oldMat ε v)).d1 *ᵥ v = 0 := by
  ext i; fin_cases i <;> simp [twoTerm, oldMat, mulVec, dotProduct, Fin.sum_univ_two]; ring

theorem oldMat_hl (ε : F) (v : Fin 2 → F) :
    (Pi.single 0 1 : Fin 2 → F) ᵥ* (twoTerm (oldMat ε v)).d1 = 0 := by
  ext j; fin_cases j <;> simp [twoTerm, oldMat, vecMul, dotProduct, Fin.sum_univ_two]

theorem newMat_hz (ε σ : F) (J : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    (twoTerm (newMat ε σ J v)).d1 *ᵥ (J *ᵥ v) = 0 := by
  ext i; fin_cases i <;> simp [twoTerm, newMat, mulVec, dotProduct, Fin.sum_univ_two]; ring

theorem newMat_hl (ε σ : F) (J : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    (Pi.single 1 1 : Fin 2 → F) ᵥ* (twoTerm (newMat ε σ J v)).d1 = 0 := by
  ext j; fin_cases j <;> simp [twoTerm, newMat, vecMul, dotProduct, Fin.sum_univ_two]

/-- **The sharpened GLUE** (replacing the integral half of `StageConeIdentification`): the old and
new stage models admit generic comparisons with the cones of `∂_F` (`oldMat`) and `∂_S` (`newMat`)
whose cone torsions are integral units up to the canonical sign. Classification: GLUE (input). -/
def StageConeComparison (S S' : TwoTermStage ι) (ε σ : F) (J : Matrix (Fin 2) (Fin 2) F)
    (v : Fin 2 → F) : Prop :=
  (∃ g : StageMap S (oldMat ε v) v (Pi.single 0 1), g.IntegralUnit (oldMat_hz ε v) (oldMat_hl ε v))
    ∧ ∃ g : StageMap S' (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1),
      g.IntegralUnit (newMat_hz ε σ J v) (newMat_hl ε σ J v)

/-- The old stage link from the lattice condition. -/
theorem stageModelLink_old {S : TwoTermStage ι} {ε : F} (hε : ε ≠ 0) {v : Fin 2 → F} (hv : v ≠ 0)
    (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    (h : ∃ g : StageMap S (oldMat ε v) v (Pi.single 0 1),
      g.IntegralUnit (oldMat_hz ε v) (oldMat_hl ε v)) :
    StageModelLink ι S.u (oldMat ε v) v (Pi.single 0 1) := by
  obtain ⟨g, hg⟩ := h
  exact (stageModelLink_iff g _ _ hS0 hSadj (oldMat_coord hε v) (neg_ne_zero.mpr (inv_ne_zero hε))
    (oldMat_adjugate_ne_zero hε hv)).2 hg

/-- The new stage link from the lattice condition. -/
theorem stageModelLink_new {S : TwoTermStage ι} {ε σ : F} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) F} {v : Fin 2 → F} (hv : J *ᵥ v ≠ 0)
    (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    (h : ∃ g : StageMap S (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1),
      g.IntegralUnit (newMat_hz ε σ J v) (newMat_hl ε σ J v)) :
    StageModelLink ι S.u (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1) := by
  obtain ⟨g, hg⟩ := h
  exact (stageModelLink_iff g _ _ hS0 hSadj (newMat_coord hε hσ J v)
    (inv_ne_zero (mul_ne_zero hσ hε)) (newMat_adjugate_ne_zero hε hσ hv)).2 hg

/-- **UniformSwitch's `CoordStep` from the sharpened GLUE** (tex L4834–4907, L5137–5153; PROVED
from `StageConeComparison`), for nondegenerate stage models of any size. -/
noncomputable def coordStep_of_coneComparison (S S' : TwoTermStage ι) {ε σ : F} (hε : ε ≠ 0)
    (hσ : σ * σ = 1) {J : Matrix (Fin 2) (Fin 2) F} (hJ2 : J * J = 1) (hJdet : J.det = -1)
    {v : Fin 2 → F} (hv : v ≠ 0) (hS0 : S.u ≠ 0) (hSadj : (S.D.map ι).adjugate ≠ 0)
    (hS'0 : S'.u ≠ 0) (hS'adj : (S'.D.map ι).adjugate ≠ 0)
    (h : StageConeComparison S S' ε σ J v) : CoordStep ι S.u S'.u :=
  coordStep_of_switch ι hε hσ hJ2 hJdet hv (stageModelLink_old hε hv hS0 hSadj h.1)
    (stageModelLink_new hε (left_ne_zero_of_mul_eq_one hσ) (mulVec_ne_zero_of_sq hJ2 hv) hS'0
      hS'adj h.2)

end Glue

/-! ### Non-vacuity: a `3 × 3` stage and its comparison with the cone -/

section Examples

/-- The projection `[I | 0] : ℚ³ → ℚ²`. -/
def proj32 : Matrix (Fin 2) (Fin 3) ℚ := fun i j => if (j : ℕ) = i then 1 else 0

theorem ex3_c1 : oldMat 1 exV * proj32 = proj32 * ex3D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oldMat, ex3D, proj32, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ex3_hz : proj32 *ᵥ ![1, 0, 0] = exV := by
  ext i
  fin_cases i <;> simp [proj32, mulVec, dotProduct, Fin.sum_univ_succ]

theorem ex3_hl : (Pi.single 0 1 : Fin 2 → ℚ) ᵥ* proj32 = ![1, 0, 0] := by
  ext j
  fin_cases j <;> simp [proj32, vecMul, dotProduct, Fin.sum_univ_succ]

theorem ex3D_map_id : ex3D.map (RingHom.id ℚ) = ex3D := by
  ext i j; rfl

/-- The comparison of the `3 × 3` stage `diag(0, −1, 1)` with the cone `oldMat 1 e₀ = diag(0, −1)`:
the projection onto the first two coordinates in both degrees. -/
def ex3StageMap : StageMap ex3Stage (oldMat 1 exV) exV (Pi.single 0 1) where
  f :=
    { f0 := 0
      f1 := proj32
      f2 := proj32
      f3 := 0
      c0 := Matrix.ext fun _ j => j.elim
      c1 := by
        change oldMat 1 exV * proj32 = proj32 * ex3D.map (RingHom.id ℚ)
        rw [ex3D_map_id]
        exact ex3_c1
      c2 := Matrix.ext fun i _ => i.elim }
  hz := ex3_hz
  hl := ex3_hl

theorem ex3Stage_adj : (ex3Stage.D.map (RingHom.id ℚ)).adjugate ≠ 0 := by
  intro h
  have h0 := congrFun (congrFun h 0) 0
  change (ex3D.map (RingHom.id ℚ)).adjugate 0 0 = 0 at h0
  rw [ex3D_map_id, adjugate_fin_three] at h0
  simp [ex3D] at h0

/-- **Non-vacuity: the lattice condition holds for the `3 × 3` stage** (from the `3 × 3` link of
`StageLink.lean` and `stageModelLink_iff`). -/
theorem ex3_integralUnit : ex3StageMap.IntegralUnit (oldMat_hz 1 exV) (oldMat_hl 1 exV) :=
  (stageModelLink_iff ex3StageMap _ _ (by simp [ex3Stage]) ex3Stage_adj
    (oldMat_coord one_ne_zero exV) (by norm_num)
    (oldMat_adjugate_ne_zero one_ne_zero exV_ne_zero)).1
    ex3_link

theorem exNew_map_id :
    (newMat 1 1 (switchJ0 ℚ) exV).map (RingHom.id ℚ) = newMat 1 1 (switchJ0 ℚ) exV := by
  ext i j; rfl

/-- The identity comparison of the `2 × 2` new stage with its cone. -/
def exNewStageMap :
    StageMap exStage_new (newMat 1 1 (switchJ0 ℚ) exV) (switchJ0 ℚ *ᵥ exV) (Pi.single 1 1) where
  f :=
    { f0 := 0
      f1 := (1 : Matrix (Fin 2) (Fin 2) ℚ)
      f2 := (1 : Matrix (Fin 2) (Fin 2) ℚ)
      f3 := 0
      c0 := Matrix.ext fun _ j => j.elim
      c1 := by
        change newMat 1 1 (switchJ0 ℚ) exV * (1 : Matrix (Fin 2) (Fin 2) ℚ) =
          (1 : Matrix (Fin 2) (Fin 2) ℚ) * (newMat 1 1 (switchJ0 ℚ) exV).map (RingHom.id ℚ)
        rw [exNew_map_id, Matrix.mul_one, Matrix.one_mul]
      c2 := Matrix.ext fun i _ => i.elim }
  hz := one_mulVec _
  hl := vecMul_one _

theorem exStage_new_adj : (exStage_new.D.map (RingHom.id ℚ)).adjugate ≠ 0 := by
  change ((newMat 1 1 (switchJ0 ℚ) exV).map (RingHom.id ℚ)).adjugate ≠ 0
  rw [exNew_map_id]
  exact newMat_adjugate_ne_zero one_ne_zero one_ne_zero exJ_v_ne_zero

theorem exNew_integralUnit :
    exNewStageMap.IntegralUnit (newMat_hz 1 1 (switchJ0 ℚ) exV) (newMat_hl 1 1 (switchJ0 ℚ) exV) :=
  (stageModelLink_iff exNewStageMap _ _ (by simp [exStage_new]) exStage_new_adj
    (newMat_coord one_ne_zero one_ne_zero _ exV) (by norm_num)
    (newMat_adjugate_ne_zero one_ne_zero one_ne_zero exJ_v_ne_zero)).1 exLink_new

/-- **Non-vacuity: `StageConeComparison` holds** for the `3 × 3` old stage and the `2 × 2` new
stage, and `coordStep_of_coneComparison` gives an actual `CoordStep`. -/
theorem ex3_stageConeComparison :
    StageConeComparison ex3Stage exStage_new 1 1 (switchJ0 ℚ) exV :=
  ⟨⟨ex3StageMap, ex3_integralUnit⟩, ⟨exNewStageMap, exNew_integralUnit⟩⟩

/-- An actual `CoordStep` from the sharpened GLUE. -/
noncomputable def ex3CoordStep' : CoordStep (RingHom.id ℚ) ex3Stage.u exStage_new.u :=
  coordStep_of_coneComparison ex3Stage exStage_new one_ne_zero (mul_one 1) (switchJ0_sq (K := ℚ))
    (switchJ0_det (K := ℚ)) exV_ne_zero (by simp [ex3Stage]) ex3Stage_adj (by simp [exStage_new])
    exStage_new_adj ex3_stageConeComparison

end Examples

end ZInQ.Contrib.CloudB3RC53.StageCone
