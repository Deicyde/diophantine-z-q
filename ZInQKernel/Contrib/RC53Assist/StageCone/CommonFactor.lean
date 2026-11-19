import ZInQKernel.Contrib.CloudB3RC53.StageCone.Comparison

/-!
# A common strict determinant factor

The determinant switch in the manuscript retains the strict factor, including
its torsion (the derivative-switch proof, lines 4900–4906, and the regularity
proof, lines 5148–5152). The normalized comparison torsions need only differ
by an integral unit. Neither normalized torsion need itself be a unit.

The construction below retains the original plane pairing and puts the common
factor into the strict volume form. It produces the existing coordinate-step
consumer without deleting a nonunit strict factor.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.StageCone

open Matrix Module
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.StageCone
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Central
open ZInQ.Manuscript.RC.Uniform

section Normalization

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}
variable {S : TwoTermStage ι} {M : Matrix (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F}

/-- Remove the canonical comparison sign. -/
def normalizedConeTorsion (g : StageMap S M z₀ l₀)
    (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0) (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) : F :=
  stageSign S * g.coneTorsion hz₀ hl₀

/-- The stage coordinate is divided by the normalized comparison torsion. -/
theorem stage_coord_eq_normalized (g : StageMap S M z₀ l₀)
    (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0) (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0)
    (hS : S.u ≠ 0) (hSad : (S.D.map ι).adjugate ≠ 0) {u₀ : F}
    (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMad : M.adjugate ≠ 0) :
    S.u = u₀ * (normalizedConeTorsion g hz₀ hl₀)⁻¹ := by
  rw [stage_coord_eq g hz₀ hl₀ hS hSad hu₀ hu₀0 hMad]
  have hs : (stageSign S)⁻¹ = stageSign S :=
    inv_eq_of_mul_eq_one_right (stageSign_mul_self S)
  rw [normalizedConeTorsion, mul_inv, hs]
  ring

/-- Nondegenerate comparison torsions do not vanish. -/
theorem normalizedConeTorsion_ne_zero (g : StageMap S M z₀ l₀)
    (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0) (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0)
    (hS : S.u ≠ 0) (hSad : (S.D.map ι).adjugate ≠ 0) {u₀ : F}
    (hu₀ : IsClassFunctionalCoord M z₀ l₀ u₀) (hu₀0 : u₀ ≠ 0) (hMad : M.adjugate ≠ 0) :
    normalizedConeTorsion g hz₀ hl₀ ≠ 0 := by
  intro h0
  have h := stage_coord_eq_normalized g hz₀ hl₀ hS hSad hu₀ hu₀0 hMad
  rw [h0, _root_.inv_zero, mul_zero] at h
  exact hS h

/-- The individual integral-unit condition is exactly unit-valued normalized torsion. -/
theorem integralUnit_iff_normalized (g : StageMap S M z₀ l₀)
    (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0) (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) :
    g.IntegralUnit hz₀ hl₀ ↔ ∃ c : Aˣ, normalizedConeTorsion g hz₀ hl₀ = ι c := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [normalizedConeTorsion, hc, ← mul_assoc, stageSign_mul_self, one_mul]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, normalizedConeTorsion, ← mul_assoc, stageSign_mul_self, one_mul]

end Normalization

section Volume

variable {F : Type} [Field F]

/-- Switch data retaining a prescribed nonzero strict volume factor. -/
def volumeSwitchData {ε σ : F} (hε : ε ≠ 0) (hσ : σ * σ = 1)
    {J : Matrix (Fin 2) (Fin 2) F} (hJ : J * J = 1) (hJdet : J.det = -1)
    {v : Fin 2 → F} (hv : v ≠ 0) (θ : F) (hθ : θ ≠ 0) (μF μS : F) : SwitchCoordData F :=
  let X := planeSwitchData hε hσ hJ hJdet hv μF μS
  { X with
    ω := θ • X.ω
    hω := by
      intro x
      change θ * X.ω x x = 0
      rw [X.hω x, mul_zero]
    hxw := by
      change θ * X.ω (bdryF ε σ J X.f X.s X.x) X.w ≠ 0
      exact mul_ne_zero hθ X.hxw
    hyw := by
      change θ * X.ω (bdryS ε σ J X.f X.s X.y) X.w' ≠ 0
      exact mul_ne_zero hθ X.hyw }

/-- The old coordinate keeps the strict volume in its denominator. -/
theorem volumeSwitchData_uF {ε σ : F} (hε : ε ≠ 0) (hσ : σ * σ = 1)
    {J : Matrix (Fin 2) (Fin 2) F} (hJ : J * J = 1) (hJdet : J.det = -1)
    {v : Fin 2 → F} (hv : v ≠ 0) (θ : F) (hθ : θ ≠ 0) (μF μS : F) :
    (volumeSwitchData hε hσ hJ hJdet hv θ hθ μF μS).uF = μF / (ε * θ) := by
  set X := volumeSwitchData hε hσ hJ hJdet hv θ hθ μF μS
  rw [SwitchCoordData.uF, coordF_eq (Pi.basisFun F (Fin 2)) X.hJ2 X.hfA X.hsA X.hsB X.hω
    X.μF X.hxw]
  change μF / (ε * (θ * dualVol (Pi.basisFun F (Fin 2)) _ _)) = _
  rw [dualVol_basis, mul_one]

/-- The new coordinate has the same strict volume denominator. -/
theorem volumeSwitchData_uS {ε σ : F} (hε : ε ≠ 0) (hσ : σ * σ = 1)
    {J : Matrix (Fin 2) (Fin 2) F} (hJ : J * J = 1) (hJdet : J.det = -1)
    {v : Fin 2 → F} (hv : v ≠ 0) (θ : F) (hθ : θ ≠ 0) (μF μS : F) :
    (volumeSwitchData hε hσ hJ hJdet hv θ hθ μF μS).uS = -μS / (σ * ε * θ) := by
  set X := volumeSwitchData hε hσ hJ hJdet hv θ hθ μF μS
  rw [SwitchCoordData.uS, coordS_eq (Pi.basisFun F (Fin 2)) X.hJ2 X.hJdet X.hfA X.hfB X.hsB X.hω
    X.μS X.hyw]
  change -μS / (σ * (ε * (θ * dualVol (Pi.basisFun F (Fin 2)) _ _))) = _
  rw [dualVol_basis, mul_one, mul_assoc]

end Volume

section Relative

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}
variable {S S' : TwoTermStage ι} {ε σ : F} {J : Matrix (Fin 2) (Fin 2) F} {v : Fin 2 → F}

/-- The two normalized comparison torsions differ by an integral unit.
This does not require either torsion to be individually unit-valued. -/
def RelativeConeUnit
    (g : StageMap S (oldMat ε v) v (Pi.single 0 1))
    (g' : StageMap S' (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1)) : Prop :=
  ∃ c : Aˣ,
    normalizedConeTorsion g' (newMat_hz ε σ J v) (newMat_hl ε σ J v) =
      ι c * normalizedConeTorsion g (oldMat_hz ε v) (oldMat_hl ε v)

/-- A common strict determinant factor proves the relative condition, without any unit
hypothesis on that common factor. -/
theorem relativeConeUnit_of_commonFactor
    (g : StageMap S (oldMat ε v) v (Pi.single 0 1))
    (g' : StageMap S' (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1))
    (θ : F) (a b : Aˣ)
    (hold : normalizedConeTorsion g (oldMat_hz ε v) (oldMat_hl ε v) = θ * ι a)
    (hnew : normalizedConeTorsion g' (newMat_hz ε σ J v) (newMat_hl ε σ J v) = θ * ι b) :
    RelativeConeUnit g g' := by
  refine ⟨b * a⁻¹, ?_⟩
  rw [hold, hnew, Units.val_mul, map_mul]
  have ha : ι ((a⁻¹ : Aˣ) : A) * ι (a : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc θ * ι (b : A) = θ * ι (b : A) *
      (ι ((a⁻¹ : Aˣ) : A) * ι (a : A)) := by rw [ha, mul_one]
    _ = _ := by ring

/-- The stronger, individual certificates imply the relative certificate. -/
theorem relativeConeUnit_of_integralUnits
    (g : StageMap S (oldMat ε v) v (Pi.single 0 1))
    (g' : StageMap S' (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1))
    (hg : g.IntegralUnit (oldMat_hz ε v) (oldMat_hl ε v))
    (hg' : g'.IntegralUnit (newMat_hz ε σ J v) (newMat_hl ε σ J v)) :
    RelativeConeUnit g g' := by
  obtain ⟨a, ha⟩ := (integralUnit_iff_normalized g _ _).1 hg
  obtain ⟨b, hb⟩ := (integralUnit_iff_normalized g' _ _).1 hg'
  exact relativeConeUnit_of_commonFactor g g' 1 a b (by simpa using ha) (by simpa using hb)

/-- A relative integral comparison supplies the existing coordinate-step consumer with the
original plane data. The strict volume, rather than the unit normalizations, carries the
common nonunit factor. -/
def coordStep_of_relativeConeUnit
    (g : StageMap S (oldMat ε v) v (Pi.single 0 1))
    (g' : StageMap S' (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1))
    (hε : ε ≠ 0) (hσ : σ * σ = 1) (hJ : J * J = 1) (hJdet : J.det = -1) (hv : v ≠ 0)
    (hS : S.u ≠ 0) (hSad : (S.D.map ι).adjugate ≠ 0)
    (hS' : S'.u ≠ 0) (hS'ad : (S'.D.map ι).adjugate ≠ 0)
    (H : RelativeConeUnit g g') : CoordStep ι S.u S'.u := by
  let c : Aˣ := Classical.choose H
  have hc := Classical.choose_spec H
  let θ := normalizedConeTorsion g (oldMat_hz ε v) (oldMat_hl ε v)
  have hθ : θ ≠ 0 := normalizedConeTorsion_ne_zero g _ _ hS hSad (oldMat_coord hε v)
    (neg_ne_zero.mpr (inv_ne_zero hε)) (oldMat_adjugate_ne_zero hε hv)
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul_eq_one hσ
  have hold : S.u = -ε⁻¹ * θ⁻¹ := stage_coord_eq_normalized g _ _ hS hSad (oldMat_coord hε v)
    (neg_ne_zero.mpr (inv_ne_zero hε)) (oldMat_adjugate_ne_zero hε hv)
  have hnew : S'.u = (σ * ε)⁻¹ * (ι (c : A) * θ)⁻¹ := by
    rw [stage_coord_eq_normalized g' (newMat_hz ε σ J v) (newMat_hl ε σ J v)
      hS' hS'ad (newMat_coord hε hσ0 J v)
      (inv_ne_zero (mul_ne_zero hσ0 hε))
      (newMat_adjugate_ne_zero hε hσ0 (mulVec_ne_zero_of_sq hJ hv)), hc]
  have hcinv : (ι (c : A))⁻¹ = ι ((c⁻¹ : Aˣ) : A) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul, Units.mul_inv, map_one]
  refine
    { X := volumeSwitchData hε hσ hJ hJdet hv θ hθ (-1) (-ι ((c⁻¹ : Aˣ) : A))
      mF := -1
      mS := -((c⁻¹ : Aˣ) : A)
      σ₀ := (sign_in_image ι hσ).choose
      hmF := isUnit_one.neg
      hmS := (Units.isUnit _).neg
      hμF := by change (-1 : F) = ι (-1 : A); simp
      hμS := by change -ι ((c⁻¹ : Aˣ) : A) = ι (-((c⁻¹ : Aˣ) : A)); simp
      hσ₀ := (sign_in_image ι hσ).choose_spec
      hu := ?_
      hu' := ?_ }
  · rw [volumeSwitchData_uF, hold]
    simp only [div_eq_mul_inv, mul_inv, neg_mul, one_mul]
  · rw [volumeSwitchData_uS, hnew]
    simp only [div_eq_mul_inv, mul_inv, hcinv, neg_neg]
    ring

/-- A common strict factor is enough for the coordinate step. -/
def coordStep_of_commonFactor
    (g : StageMap S (oldMat ε v) v (Pi.single 0 1))
    (g' : StageMap S' (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1))
    (hε : ε ≠ 0) (hσ : σ * σ = 1) (hJ : J * J = 1) (hJdet : J.det = -1) (hv : v ≠ 0)
    (hS : S.u ≠ 0) (hSad : (S.D.map ι).adjugate ≠ 0)
    (hS' : S'.u ≠ 0) (hS'ad : (S'.D.map ι).adjugate ≠ 0)
    (θ : F) (a b : Aˣ)
    (hold : normalizedConeTorsion g (oldMat_hz ε v) (oldMat_hl ε v) = θ * ι a)
    (hnew : normalizedConeTorsion g' (newMat_hz ε σ J v) (newMat_hl ε σ J v) = θ * ι b) :
    CoordStep ι S.u S'.u :=
  coordStep_of_relativeConeUnit g g' hε hσ hJ hJdet hv hS hSad hS' hS'ad
    (relativeConeUnit_of_commonFactor g g' θ a b hold hnew)

end Relative

section Summand

variable {F : Type} [Field F]
variable {E₀ E₁ E₂ E₃ : Type} [Fintype E₀] [Fintype E₁] [Fintype E₂] [Fintype E₃]
  [DecidableEq E₀] [DecidableEq E₁] [DecidableEq E₂] [DecidableEq E₃]

/-- The plane coordinate with a retained acyclic strict summand. -/
def planeCoordWithSummand (M : Matrix (Fin 2) (Fin 2) F) (z l : Fin 2 → F)
    (hz : (twoTerm M).d1 *ᵥ z = 0) (hl : l ᵥ* (twoTerm M).d1 = 0)
    (E : FourCx F E₀ E₁ E₂ E₃) (sE : E₀ ⊕ E₂ ≃ E₁ ⊕ E₃) : F :=
  kmCoord ((twoTerm M).sum E) (Sum.elim z 0) (Sum.elim l 0)
    ((twoTerm M).sum_hz E hz) ((twoTerm M).sum_hlam E hl) (sumOrient (σ₀ 2) sE)

/-- The strict summand contributes its complete torsion, not only its unit part. -/
theorem planeCoordWithSummand_eq (M : Matrix (Fin 2) (Fin 2) F) (z l : Fin 2 → F)
    (hz : (twoTerm M).d1 *ᵥ z = 0) (hl : l ᵥ* (twoTerm M).d1 = 0)
    (E : FourCx F E₀ E₁ E₂ E₃) (sE : E₀ ⊕ E₂ ≃ E₁ ⊕ E₃)
    (hE : Contraction E.toBased) {u : F} (hu : IsClassFunctionalCoord M z l u)
    (hC : Contraction ((twoTerm M).aug z l hz hl).toBased) :
    planeCoordWithSummand M z l hz hl E sE = u * torsion E.toBased sE := by
  unfold planeCoordWithSummand
  rw [kmCoord_sum _ _ _ _ _ _ hC hE, kmCoord_twoTerm _ _ _ _ _ _ hC hu]

/-- Adding the same generic acyclic strict summand on both sides preserves the switch relation.
No assertion that its torsion is an integral unit is needed. -/
theorem commonSummand_switch_relation {ε σ : F} (hε : ε ≠ 0) (hσ : σ * σ = 1)
    {J : Matrix (Fin 2) (Fin 2) F} (hJ : J * J = 1) {v : Fin 2 → F} (hv : v ≠ 0)
    (E : FourCx F E₀ E₁ E₂ E₃) (sE : E₀ ⊕ E₂ ≃ E₁ ⊕ E₃) (hE : Contraction E.toBased) :
    planeCoordWithSummand (oldMat ε v) v (Pi.single 0 1)
        (oldMat_hz ε v) (oldMat_hl ε v) E sE =
      -σ * planeCoordWithSummand (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1)
        (newMat_hz ε σ J v) (newMat_hl ε σ J v) E sE := by
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul_eq_one hσ
  obtain ⟨hC⟩ := contraction_aug_twoTerm _ _ _ _ (oldMat_hz ε v) (oldMat_hl ε v)
    (oldMat_coord hε v) (neg_ne_zero.mpr (inv_ne_zero hε)) (oldMat_adjugate_ne_zero hε hv)
  obtain ⟨hC'⟩ := contraction_aug_twoTerm _ _ _ _ (newMat_hz ε σ J v) (newMat_hl ε σ J v)
    (newMat_coord hε hσ0 J v) (inv_ne_zero (mul_ne_zero hσ0 hε))
    (newMat_adjugate_ne_zero hε hσ0 (mulVec_ne_zero_of_sq hJ hv))
  rw [planeCoordWithSummand_eq _ _ _ _ _ E sE hE (oldMat_coord hε v) hC,
    planeCoordWithSummand_eq _ _ _ _ _ E sE hE (newMat_coord hε hσ0 J v) hC', mul_inv,
    show σ⁻¹ = σ from inv_eq_of_mul_eq_one_right hσ]
  calc
    -ε⁻¹ * torsion E.toBased sE = -(σ * σ) * ε⁻¹ * torsion E.toBased sE := by
      rw [hσ, neg_one_mul]
    _ = _ := by ring

end Summand

set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true

end ZInQ.Contrib.RC53Assist.StageCone
