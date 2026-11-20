import ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiPrint
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.KatoHypV

/-! The abelian-kernel part of §0.6(ii). A commutator of two actual open
image lifts suffices; one does not identify the full commutator image. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open PrintsArith
open scoped commutatorElement TensorProduct

/-- A commutator restricts to the identity on each finite abelian extension. -/
theorem commutator_fixesAbelian (g h : GalQ) : FixesAbelian ⁅g, h⁆ := by
  intro F _ _ hab x
  let r : GalQ →* (F ≃ₐ[ℚ] F) := AlgEquiv.restrictNormalHom F
  have hr : r ⁅g, h⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hab (r g) (r h))
  have hx := DFunLike.congr_fun hr x
  have hval := congrArg (fun y : F => (y : Qbar)) hx
  simpa only [r, AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply] using hval

/-- Scaling the first basis coordinate by a unit and fixing the second. -/
def scaleFirst (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (u : ℤ_[2]ˣ) : TateMod E 2 ≃ₗ[ℤ_[2]] TateMod E 2 :=
  let b := (tateBasis E).equivFun
  (b.trans (LinearEquiv.piCongrRight
    fun i => LinearEquiv.smulOfUnit (if i = (0 : Fin 2) then u else 1))).trans b.symm

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

theorem scaleFirst_coord (u : ℤ_[2]ˣ) (i : Fin 2) (x : TateMod E 2) :
    (tateBasis E).coord i (scaleFirst E u x) =
      (if i = 0 then (u : ℤ_[2]) else 1) * (tateBasis E).coord i x := by
  rw [scaleFirst, LinearEquiv.trans_apply, Module.Basis.coord_equivFun_symm]
  by_cases hi : i = 0 <;>
    simp [LinearEquiv.piCongrRight_apply, LinearEquiv.trans_apply, hi, smul_eq_mul]

theorem scaleFirst_apply (u : ℤ_[2]ˣ) (x : TateMod E 2) :
    scaleFirst E u x = x + (((u : ℤ_[2]) - 1) * (tateBasis E).coord 0 x) •
      (tateBasis E) 0 := by
  apply (tateBasis E).equivFun.injective
  funext i
  change (tateBasis E).coord i (scaleFirst E u x) = (tateBasis E).coord i _
  rw [scaleFirst_coord, map_add, map_smul]
  fin_cases i
  · simp [Module.Basis.coord_apply, Module.Basis.repr_self]
    ring
  · simp [Module.Basis.coord_apply, Module.Basis.repr_self]

/-- Under Serre, an actual commutator has nonidentity upper-unipotent
2-adic action. This proves the integral image assertion over ℚᵃᵇ. -/
theorem serre_abelian_unipotent (hS : SerreThm3) (hCM : HasNoCM E) :
    ∃ (g τ : GalQ) (c : ℤ_[2]), c ≠ 0 ∧
      tateRep E 2 ⁅g, τ⁆ = (unip E c).toLinearMap := by
  obtain ⟨n, hn, h⟩ := serre_two_adic hS E hCM
  let c : ℤ_[2] := (2 : ℤ_[2]) ^ n
  let u : ℤ_[2]ˣ := (isUnit_one_add_two_pow (n := n) (by omega)).unit
  have hu : (u : ℤ_[2]) = 1 + c := IsUnit.unit_spec _
  obtain ⟨g, hg⟩ := h (scaleFirst E u) fun x =>
    ⟨(tateBasis E).coord 0 x • (tateBasis E) 0, by
      rw [scaleFirst_apply, hu, add_sub_cancel_left, mul_smul]⟩
  obtain ⟨τ, hτ⟩ := h (unip E c) fun x => ⟨nilN E x, unip_apply E c x⟩
  have hc : c ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨g, τ, c * c, mul_ne_zero hc hc, ?_⟩
  have hgrp : ⁅g, τ⁆ * (τ * g) = g * τ := by
    simp [commutatorElement_def, mul_assoc]
  have hrep := congrArg (tateRep E 2) hgrp
  simp only [map_mul, hg, hτ] at hrep
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := ((scaleFirst E u).trans (unip E c)).surjective y
  have hxy := DFunLike.congr_fun hrep x
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply] at hxy ⊢
  rw [hxy]
  have hD₁ : (tateBasis E).coord 1 (scaleFirst E u x) = (tateBasis E).coord 1 x := by
    rw [scaleFirst_coord]
    simp
  have hU₀ : (tateBasis E).coord 0 (unip E c x) =
      (tateBasis E).coord 0 x + c * (tateBasis E).coord 1 x := by
    simp [unip_apply, nilN_apply, smul_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self, smul_eq_mul]
  have hU₁ : (tateBasis E).coord 1 (unip E c (scaleFirst E u x)) =
      (tateBasis E).coord 1 x := by
    simp only [unip_apply, nilN_apply, map_add, map_smul, coord_one_basis_zero,
      smul_zero, add_zero, hD₁]
  rw [scaleFirst_apply E u (unip E c x), unip_apply E (c * c), nilN_apply, hU₀, hU₁,
    unip_apply E c (scaleFirst E u x), nilN_apply, hD₁, unip_apply E c x, nilN_apply,
    scaleFirst_apply E u x, hu]
  module

/-- The strengthened integral fixed-space statement (a rational fixed
space follows by flat base change). We use an actual commutator so every
quadratic character is trivial on it. -/
theorem serre_abelian_rankOne (hS : SerreThm3) (hCM : HasNoCM E)
    (χ : GalQ →* ℤˣ) :
    ∃ g : GalQ, FixesAbelian g ∧ χ g = 1 ∧
      Module.finrank ℤ_[2] (LinearMap.ker (tateRep E 2 g - 1)) = 1 := by
  obtain ⟨g, τ, c, hc, hρ⟩ := serre_abelian_unipotent E hS hCM
  have hχ : χ ⁅g, τ⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  refine ⟨⁅g, τ⁆, commutator_fixesAbelian g τ, hχ, ?_⟩
  rw [hρ, ker_unip_sub_one E hc, finrank_span_basis_zero]

/-- The rationalized Tate representation twisted by a quadratic character. -/
def rationalTwist (χ : GalQ →* ℤˣ) :
    Representation ℚ_[2] GalQ (ℚ_[2] ⊗[ℤ_[2]] TateMod E 2) where
  toFun g := (((χ g : ℤˣ) : ℤ) : ℚ_[2]) • (tateRep E 2 g).baseChange ℚ_[2]
  map_one' := by simp [LinearMap.baseChange_one]
  map_mul' g h := by
    simp [LinearMap.baseChange_mul, smul_smul, mul_comm]

/-- The rational fixed-space condition of §0.6(ii) for the genuine twist.
Use flatness of the fraction field to preserve the kernel dimension. -/
theorem kodaiUnipotent_of_serre (hS : SerreThm3) (hCM : HasNoCM E) (χ : GalQ →* ℤˣ) :
    KodaiUnipotent (rationalTwist E χ) := by
  obtain ⟨g, hab, hχ, hker⟩ := serre_abelian_rankOne E hS hCM χ
  refine ⟨g, hab, ?_⟩
  have : Module.Flat ℤ_[2] ℚ_[2] := IsLocalization.flat _ (nonZeroDivisors ℤ_[2])
  have heq : rationalTwist E χ g - 1 = (tateRep E 2 g - 1).baseChange ℚ_[2] := by
    change (((χ g : ℤˣ) : ℤ) : ℚ_[2]) • (tateRep E 2 g).baseChange ℚ_[2] - 1 = _
    simp [hχ, LinearMap.baseChange_one]
  rw [heq]
  change Module.finrank ℚ_[2] ↥((TensorProduct.AlgebraTensorModule.lTensor ℚ_[2] ℚ_[2])
    (tateRep E 2 g - 1)).ker = 1
  rw [← (LinearMap.tensorKerEquiv ℚ_[2] ℚ_[2] (tateRep E 2 g - 1)).finrank_eq,
    Module.finrank_baseChange, hker]

end ZInQ.Manuscript.RC.KatoP2
