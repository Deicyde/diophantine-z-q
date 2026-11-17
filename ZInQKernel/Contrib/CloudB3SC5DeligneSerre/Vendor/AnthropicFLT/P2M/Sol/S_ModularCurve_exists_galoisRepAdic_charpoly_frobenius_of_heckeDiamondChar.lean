/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar (git blob db69f92d6c4fba48df5528de1fed277833df718d, sha256 a6b8469220cd5657710a44963fbb1e2fd3c36bac5e1c28309cf50b939d088db7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Adic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_rationalRankTwoNebentypus_family
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_rep_tateModule_jOne_comm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jOne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeDiamondCommuteBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar.E1G1ES
end P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar.E1G1ES

namespace P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar

open Polynomial

open scoped TensorProduct
noncomputable section
namespace E1G1ES
open ModularCurve

set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false



variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]

scoped instance isMulCommutative_rationalHeckeAlgebraOne :
    IsMulCommutative (rationalHeckeAlgebraOne p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _ -- [port]
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing (rationalHeckeAlgebraOne p J) := inferInstance

scoped instance instSMulCommClassA : SMulCommClass (rationalHeckeAlgebraOne p J) (rationalHeckeAlgebraOne p J)
    (RationalTateModule p J) := inferInstance

scoped instance instAlgebraEndA : Algebra (rationalHeckeAlgebraOne p J)
    (Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) := inferInstance

scoped instance instModuleEndA : Module (rationalHeckeAlgebraOne p J)
    (Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) :=
  (instAlgebraEndA p J).toModule

scoped instance instSMulEndA : SMul (rationalHeckeAlgebraOne p J)
    (Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) :=
  (instAlgebraEndA p J).toSMul

theorem subalgebra_smul_def (a : rationalHeckeAlgebraOne p J) (v : RationalTateModule p J) :
    a • v = (a : Module.End ℚ_[p] (RationalTateModule p J)) v := rfl

theorem algebraMap_smul_eq (c : ℚ_[p]) (v : RationalTateModule p J) :
    (algebraMap ℚ_[p] (rationalHeckeAlgebraOne p J) c) • v = c • v := by
  rw [subalgebra_smul_def, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply]

def CommHyp [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J] : Prop :=
  ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (t : HeckeAlgOne) (x : TateModule p J),
      TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (TateModule.rep p J HeckeAlgOne t x)
        = TateModule.rep p J HeckeAlgOne t (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)

section GaloisLinear

variable [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]

theorem commute_of_comm (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (a : rationalHeckeAlgebraOne p J) :
    (a : Module.End ℚ_[p] (RationalTateModule p J)) * rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
      = rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ * a := by
  have hle : rationalHeckeAlgebraOne p J ≤
      Subalgebra.centralizer ℚ_[p] {rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    rw [rationalGaloisRep_apply, rationalHeckeRepOne_apply, ← LinearMap.baseChange_mul,
      ← LinearMap.baseChange_mul]
    exact congrArg _ (LinearMap.ext fun x => hcomm σ t x)
  have := (Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle a.2) _ rfl
  exact this.symm

def galA (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    RationalTateModule p J →ₗ[rationalHeckeAlgebraOne p J] RationalTateModule p J where
  toFun := rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
  map_add' := map_add _
  map_smul' a v := (LinearMap.congr_fun (commute_of_comm p J hcomm σ a) v).symm

@[scoped simp] theorem galA_apply (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : RationalTateModule p J) :
    galA p J hcomm σ v = rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v := rfl

def galAHom (hcomm : CommHyp p J) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J) where
  toFun := galA p J hcomm
  map_one' := LinearMap.ext fun v => by simp
  map_mul' σ τ := LinearMap.ext fun v => by simp

@[scoped simp] theorem galAHom_apply (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : RationalTateModule p J) :
    galAHom p J hcomm σ v = rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v := rfl

end GaloisLinear

section Transfer

variable (b : Module.Basis (Fin 2) (rationalHeckeAlgebraOne p J) (RationalTateModule p J))
variable {K : Type} [Field K] (Λ : rationalHeckeAlgebraOne p J →+* K)

def transfer :
    Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J) →+* Module.End K (Fin 2 → K) :=
  ((Matrix.toLinAlgEquiv' (R := K) (n := Fin 2)).toRingEquiv.toRingHom.comp
    (RingHom.mapMatrix Λ)).comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom

theorem transfer_apply (f : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) :
    transfer p J b Λ f = Matrix.toLin' ((LinearMap.toMatrix b b f).map Λ) := rfl

theorem transfer_smul (a : rationalHeckeAlgebraOne p J)
    (f : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) :
    transfer p J b Λ (a • f) = Λ a • transfer p J b Λ f := by
  rw [transfer_apply, transfer_apply, LinearEquiv.map_smul, ← LinearEquiv.map_smul]
  ext i j
  simp [Matrix.map_apply, smul_eq_mul]

def coordK : RationalTateModule p J →+ (Fin 2 → K) where
  toFun v i := Λ (b.repr v i)
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp

theorem coordK_apply (v : RationalTateModule p J) (i : Fin 2) :
    coordK p J b Λ v i = Λ (b.repr v i) := rfl

theorem coordK_smul (a : rationalHeckeAlgebraOne p J) (v : RationalTateModule p J) :
    coordK p J b Λ (a • v) = Λ a • coordK p J b Λ v := by
  ext i
  simp [coordK_apply, smul_eq_mul]

theorem coordK_basis (i : Fin 2) : coordK p J b Λ (b i) = Pi.single i 1 := by
  ext j
  rw [coordK_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem coordK_endo (f : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J))
    (v : RationalTateModule p J) :
    coordK p J b Λ (f v) = transfer p J b Λ f (coordK p J b Λ v) := by
  ext i
  rw [transfer_apply, Matrix.toLin'_apply, coordK_apply, ← LinearMap.toMatrix_mulVec_repr b b f v]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, coordK_apply, map_sum, map_mul]

theorem det_transfer (f : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) :
    LinearMap.det (transfer p J b Λ f) = Λ (LinearMap.det f) := by
  rw [transfer_apply, LinearMap.det_toLin', ← LinearMap.det_toMatrix b, RingHom.map_det]
  rfl

end Transfer

section Frobenius

variable [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
variable (b : Module.Basis (Fin 2) (rationalHeckeAlgebraOne p J) (RationalTateModule p J))
variable {K : Type} [Field K] (Λ : rationalHeckeAlgebraOne p J →+* K)

def rhoK (hcomm : CommHyp p J) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K (Fin 2 → K) :=
  (transfer p J b Λ).toMonoidHom.comp (galAHom p J hcomm)

theorem rhoK_apply (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    rhoK p J b Λ hcomm σ = transfer p J b Λ (galA p J hcomm σ) := rfl

def iotaK (x : TateModule p J) : Fin 2 → K := coordK p J b Λ ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x)

theorem iotaK_add (x y : TateModule p J) :
    iotaK p J b Λ (x + y) = iotaK p J b Λ x + iotaK p J b Λ y := by
  simp [iotaK, TensorProduct.tmul_add]

theorem iotaK_zero : iotaK p J b Λ 0 = 0 := by simp [iotaK]

theorem iotaK_sub (x y : TateModule p J) :
    iotaK p J b Λ (x - y) = iotaK p J b Λ x - iotaK p J b Λ y := by
  simp [iotaK, TensorProduct.tmul_sub]

theorem rhoK_iotaK (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : TateModule p J) :
    rhoK p J b Λ hcomm σ (iotaK p J b Λ x) = iotaK p J b Λ (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by
  rw [rhoK_apply, iotaK, iotaK, ← coordK_endo, galA_apply, rationalGaloisRep_tmul]

theorem galA_quadratic (hcomm : CommHyp p J) {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hES : ∀ x : TateModule p J,
      TateModule.rep p J HeckeAlgOne (diamondGen ℓ)
          (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
        - TateModule.rep p J HeckeAlgOne (heckeGenOne ⟨ℓ, hℓ⟩) (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
        + ℓ • x = 0) :
    rationalDiamondOne p J ℓ • (galA p J hcomm σ * galA p J hcomm σ)
      - rationalHeckeOne p J ⟨ℓ, hℓ⟩ • galA p J hcomm σ
      + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) = 0 := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, galA_apply, subalgebra_smul_def, coe_rationalDiamondOne, coe_rationalHeckeOne]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [Module.End.natCast_apply, rationalGaloisRep_tmul, rationalGaloisRep_tmul, rationalHeckeRepOne_tmul,
      rationalHeckeRepOne_tmul, tateHeckeRepOne_apply, tateHeckeRepOne_apply,
      ← Nat.cast_smul_eq_nsmul ℤ_[p], ← TensorProduct.tmul_smul,
      Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_sub, ← TensorProduct.tmul_add, hES x,
      TensorProduct.tmul_zero]
  | add v w hv hw =>
    have e : rationalHeckeRepOne p J (diamondGen ℓ)
          (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (v + w)))
        - rationalHeckeRepOne p J (heckeGenOne ⟨ℓ, hℓ⟩) (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (v + w))
        + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) (v + w)
        = (rationalHeckeRepOne p J (diamondGen ℓ)
              (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v))
            - rationalHeckeRepOne p J (heckeGenOne ⟨ℓ, hℓ⟩) (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
            + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) v)
          + (rationalHeckeRepOne p J (diamondGen ℓ)
              (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ w))
            - rationalHeckeRepOne p J (heckeGenOne ⟨ℓ, hℓ⟩) (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ w)
            + ((ℓ : ℕ) : Module.End (rationalHeckeAlgebraOne p J) (RationalTateModule p J)) w) := by
      simp only [map_add]
      abel
    rw [e, hv, hw, add_zero]

theorem rhoK_quadratic (hcomm : CommHyp p J) {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hES : ∀ x : TateModule p J,
      TateModule.rep p J HeckeAlgOne (diamondGen ℓ)
          (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
        - TateModule.rep p J HeckeAlgOne (heckeGenOne ⟨ℓ, hℓ⟩) (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
        + ℓ • x = 0) :
    Λ (rationalDiamondOne p J ℓ) • (rhoK p J b Λ hcomm σ * rhoK p J b Λ hcomm σ)
      - Λ (rationalHeckeOne p J ⟨ℓ, hℓ⟩) • rhoK p J b Λ hcomm σ
      + ((ℓ : ℕ) : Module.End K (Fin 2 → K)) = 0 := by
  have h := congrArg (transfer p J b Λ) (galA_quadratic p J hcomm hℓ σ hES)
  rwa [map_add, map_sub, transfer_smul, map_mul, transfer_smul, map_natCast, map_zero] at h

theorem rhoK_quadratic' (hcomm : CommHyp p J) {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hES : ∀ x : TateModule p J,
      TateModule.rep p J HeckeAlgOne (diamondGen ℓ)
          (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
        - TateModule.rep p J HeckeAlgOne (heckeGenOne ⟨ℓ, hℓ⟩) (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
        + ℓ • x = 0)
    (a' d' : K) (ha : Λ (rationalHeckeOne p J ⟨ℓ, hℓ⟩) = a')
    (hd : Λ (rationalDiamondOne p J ℓ) * d' = 1) :
    rhoK p J b Λ hcomm σ * rhoK p J b Λ hcomm σ - (d' * a') • rhoK p J b Λ hcomm σ
      + ((d' * (ℓ : K)) • (1 : Module.End K (Fin 2 → K))) = 0 := by
  have h := congrArg (fun f => d' • f) (rhoK_quadratic p J b Λ hcomm hℓ σ hES)
  simp only [smul_add, smul_sub, smul_smul, smul_zero] at h
  rw [mul_comm d' (Λ _), hd, one_smul, ha] at h
  have e : d' • ((ℓ : ℕ) : Module.End K (Fin 2 → K)) = (d' * (ℓ : K)) • (1 : Module.End K (Fin 2 → K)) := by
    rw [← smul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [e] at h
  exact h

theorem det_rhoK (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    LinearMap.det (rhoK p J b Λ hcomm σ)
      = Λ ((b.repr (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 0))) 0
              * (b.repr (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 1))) 1
            - (b.repr (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 1))) 0
              * (b.repr (rationalGaloisRep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (b 0))) 1) := by
  rw [rhoK_apply, det_transfer, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, galA_apply]

end Frobenius

section Lattice

variable [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
variable (b : Module.Basis (Fin 2) (rationalHeckeAlgebraOne p J) (RationalTateModule p J))
variable {K : Type} [Field K] (Λ : rationalHeckeAlgebraOne p J →+* K)
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O K]
  [IsFractionRing O K] [Algebra ℤ_[p] O]

def lattice : Submodule O (Fin 2 → K) := Submodule.span O (Set.range (iotaK p J b Λ))

theorem iotaK_mem (x : TateModule p J) : iotaK p J b Λ x ∈ lattice p J b Λ O :=
  Submodule.subset_span ⟨x, rfl⟩

def Compat : Prop :=
  ∀ c : ℤ_[p], Λ (algebraMap ℚ_[p] (rationalHeckeAlgebraOne p J) (c : ℚ_[p]))
    = algebraMap O K (algebraMap ℤ_[p] O c)

theorem iotaK_smul (hc : Compat p J Λ O) (c : ℤ_[p]) (x : TateModule p J) :
    iotaK p J b Λ (c • x) = (algebraMap ℤ_[p] O c) • iotaK p J b Λ x := by
  rw [iotaK, iotaK, TensorProduct.tmul_smul, ← algebraMap_smul ℚ_[p] c, ← algebraMap_smul_eq,
    coordK_smul, show algebraMap ℤ_[p] ℚ_[p] c = (c : ℚ_[p]) from rfl, hc, algebraMap_smul]

theorem lattice_stable (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    ∀ v ∈ lattice p J b Λ O, rhoK p J b Λ hcomm σ v ∈ lattice p J b Λ O := by
  intro v hv
  have : lattice p J b Λ O ≤ (lattice p J b Λ O).comap ((rhoK p J b Λ hcomm σ).restrictScalars O) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.coe_restrictScalars, rhoK_iotaK]
    exact iotaK_mem p J b Λ O _
  exact this hv

def rhoL (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : lattice p J b Λ O →ₗ[O] lattice p J b Λ O :=
  ((rhoK p J b Λ hcomm σ).restrictScalars O).restrict (lattice_stable p J b Λ O hcomm σ)

@[scoped simp] theorem coe_rhoL (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : lattice p J b Λ O) :
    ((rhoL p J b Λ O hcomm σ v : lattice p J b Λ O) : Fin 2 → K) = rhoK p J b Λ hcomm σ v := rfl

def rhoLHom (hcomm : CommHyp p J) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O (lattice p J b Λ O) where
  toFun := rhoL p J b Λ O hcomm
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' σ τ := LinearMap.ext fun v => Subtype.ext (by simp)

@[scoped simp] theorem rhoLHom_apply (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    rhoLHom p J b Λ O hcomm σ = rhoL p J b Λ O hcomm σ := rfl

theorem eq_top_of_forall_iotaK_mem (N : Submodule O (lattice p J b Λ O))
    (h : ∀ x, ⟨iotaK p J b Λ x, iotaK_mem p J b Λ O x⟩ ∈ N) : N = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    exact h x
  | zero => exact N.zero_mem
  | add u w hu hw ihu ihw => exact N.add_mem ihu ihw
  | smul c w hw ih => exact N.smul_mem c ih

theorem lattice_finite [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    Module.Finite O (lattice p J b Λ O) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := TateModule p J)
  have hsub : Set.range (iotaK p J b Λ) ⊆ Submodule.span O (iotaK p J b Λ '' S) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span ℤ_[p] (S : Set (TateModule p J)) := hS ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [iotaK_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [iotaK_add]; exact add_mem hy hz
    | smul c y _ hy => rw [iotaK_smul p J b Λ O hc]; exact Submodule.smul_mem _ _ hy
  rw [Module.Finite.iff_fg, Submodule.fg_def]
  refine ⟨iotaK p J b Λ '' S, S.finite_toSet.image _, le_antisymm ?_ ?_⟩
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · exact Submodule.span_le.mpr hsub

scoped instance : Module.IsTorsionFree O (Fin 2 → K) := by
  haveI : Module.IsTorsionFree O K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective O K)
  infer_instance

theorem lattice_free [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    Module.Free O (lattice p J b Λ O) := by
  haveI := lattice_finite p J b Λ O hc
  infer_instance

theorem coordK_mem_span (v : RationalTateModule p J) :
    coordK p J b Λ v ∈ Submodule.span K (Set.range (iotaK p J b Λ)) := by
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c x =>
    have : c ⊗ₜ[ℤ_[p]] x = (algebraMap ℚ_[p] (rationalHeckeAlgebraOne p J) c) • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) := by
      rw [algebraMap_smul_eq, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, coordK_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add v w hv hw => rw [map_add]; exact add_mem hv hw

theorem span_K_range_iotaK : Submodule.span K (Set.range (iotaK p J b Λ)) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro v -
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : Pi.single i (v i) = v i • (Pi.single i (1 : K) : Fin 2 → K) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, ← coordK_basis p J b Λ]
  exact Submodule.smul_mem _ _ (coordK_mem_span p J b Λ _)

theorem lattice_le_span_K [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    letI := lattice_free p J b Λ O hc
    ((lattice p J b Λ O : Submodule O (Fin 2 → K)) : Set (Fin 2 → K))
      ⊆ Submodule.span K (Set.range fun i => ((Module.Free.chooseBasis O (lattice p J b Λ O) i
          : lattice p J b Λ O) : Fin 2 → K)) := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  intro z hz
  set f := Module.Free.chooseBasis O (lattice p J b Λ O)
  have hz' := f.sum_repr ⟨z, hz⟩
  have : z = ∑ i, (f.repr ⟨z, hz⟩ i) • ((f i : lattice p J b Λ O) : Fin 2 → K) := by
    conv_lhs => rw [show z = ((⟨z, hz⟩ : lattice p J b Λ O) : Fin 2 → K) from rfl, ← hz']
    rw [Submodule.coe_sum]
    rfl
  rw [SetLike.mem_coe, this]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← algebraMap_smul K]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def basisK [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    letI := lattice_free p J b Λ O hc
    Module.Basis (Module.Free.ChooseBasisIndex O (lattice p J b Λ O)) K (Fin 2 → K) :=
  letI := lattice_free p J b Λ O hc
  Module.Basis.mk
    (v := fun i => ((Module.Free.chooseBasis O (lattice p J b Λ O) i : lattice p J b Λ O) : Fin 2 → K))
    (((Module.Free.chooseBasis O (lattice p J b Λ O)).linearIndependent.map'
        (lattice p J b Λ O).subtype (Submodule.ker_subtype _)).localization K (nonZeroDivisors O))
    (by
      rw [← span_K_range_iotaK p J b Λ, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact lattice_le_span_K p J b Λ O hc (iotaK_mem p J b Λ O x))

theorem basisK_apply [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) (i) :
    letI := lattice_free p J b Λ O hc
    basisK p J b Λ O hc i = ((Module.Free.chooseBasis O (lattice p J b Λ O) i : lattice p J b Λ O) : Fin 2 → K) := by
  simp [basisK]

theorem finrank_lattice [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) :
    Module.finrank O (lattice p J b Λ O) = 2 := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  have h1 := Module.finrank_eq_card_basis (basisK p J b Λ O hc)
  rw [Module.finrank_fin_fun] at h1
  rw [Module.finrank_eq_card_chooseBasisIndex, ← h1]

theorem basisK_repr [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (z : lattice p J b Λ O) (i) :
    letI := lattice_free p J b Λ O hc
    (basisK p J b Λ O hc).repr (z : Fin 2 → K) i
      = algebraMap O K ((Module.Free.chooseBasis O (lattice p J b Λ O)).repr z i) := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  set f := Module.Free.chooseBasis O (lattice p J b Λ O)
  have hz : (z : Fin 2 → K) = ∑ j, algebraMap O K (f.repr z j) • basisK p J b Λ O hc j := by
    conv_lhs => rw [← f.sum_repr z]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [basisK_apply, algebraMap_smul, Submodule.coe_smul_of_tower]
  rw [hz, Module.Basis.repr_sum_self]

theorem algebraMap_det_rhoL [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    algebraMap O K (LinearMap.det (rhoL p J b Λ O hcomm σ)) = LinearMap.det (rhoK p J b Λ hcomm σ) := by
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  classical
  set f := Module.Free.chooseBasis O (lattice p J b Λ O)
  rw [← LinearMap.det_toMatrix f, ← LinearMap.det_toMatrix (basisK p J b Λ O hc), RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    basisK_apply, ← coe_rhoL, basisK_repr p J b Λ O hc]

def ContHyp : Prop :=
  ∀ m : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ x ∈ L, σ x = x) → ∀ P : J, ((p ^ m : ℕ) : ℤ) • P = 0 → σ • P = P

theorem rhoL_sub_apply (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : lattice p J b Λ O) :
    (((rhoL p J b Λ O hcomm σ - 1) v : lattice p J b Λ O) : Fin 2 → K)
      = rhoK p J b Λ hcomm σ v - v := rfl

theorem rhoL_continuous [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (hcont : ContHyp p J)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    GaloisActionIsAdicContinuous O (rhoLHom p J b Λ O hcomm) := by
  intro n
  obtain ⟨L, hL, hfix⟩ := hcont n
  refine ⟨L, hL, fun σ hσ => ?_⟩
  suffices h : Submodule.comap (rhoL p J b Λ O hcomm σ - 1)
      ((IsLocalRing.maximalIdeal O ^ n) • (⊤ : Submodule O (lattice p J b Λ O))) = ⊤ by
    intro v
    have hv : v ∈ Submodule.comap (rhoL p J b Λ O hcomm σ - 1)
        ((IsLocalRing.maximalIdeal O ^ n) • (⊤ : Submodule O (lattice p J b Λ O))) := by
      rw [h]; exact Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.sub_apply, Module.End.one_apply] at hv
    exact hv
  refine eq_top_of_forall_iotaK_mem p J b Λ O _ fun x => ?_
  rw [Submodule.mem_comap]
  have hmem : TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x - x
      ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] (TateModule p J)) :=
    TateModule.rep_sub_mem_of_forall_torsionBy σ n
      (fun m hm => hfix σ hσ m ((Submodule.mem_torsionBy_iff _ _).mp hm)) x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  have hval : (((rhoL p J b Λ O hcomm σ - 1) ⟨iotaK p J b Λ x, iotaK_mem p J b Λ O x⟩
        : lattice p J b Λ O) : Fin 2 → K)
      = ((((p : O) ^ n) • (⟨iotaK p J b Λ y, iotaK_mem p J b Λ O y⟩ : lattice p J b Λ O)
        : lattice p J b Λ O) : Fin 2 → K) := by
    rw [rhoL_sub_apply, Submodule.coe_smul, rhoK_iotaK, ← iotaK_sub, ← hy,
      iotaK_smul p J b Λ O hc, map_pow, map_natCast]
  rw [Subtype.ext hval]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hpm n) Submodule.mem_top

theorem rhoL_eq_one (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hfix : ∀ x : TateModule p J, TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x = x) :
    rhoL p J b Λ O hcomm σ = 1 := by
  have h := eq_top_of_forall_iotaK_mem p J b Λ O (LinearMap.ker (rhoL p J b Λ O hcomm σ - 1))
    fun x => by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [rhoL_sub_apply, rhoK_iotaK, hfix, sub_self]
      rfl
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ LinearMap.ker (rhoL p J b Λ O hcomm σ - 1) := h ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
  exact hv

theorem rhoL_quadratic (hcomm : CommHyp p J) {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hES : ∀ x : TateModule p J,
      TateModule.rep p J HeckeAlgOne (diamondGen ℓ)
          (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
        - TateModule.rep p J HeckeAlgOne (heckeGenOne ⟨ℓ, hℓ⟩) (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
        + ℓ • x = 0)
    (a d : O) (ha : Λ (rationalHeckeOne p J ⟨ℓ, hℓ⟩) = algebraMap O K a)
    (hd : Λ (rationalDiamondOne p J ℓ) * algebraMap O K d = 1) :
    rhoL p J b Λ O hcomm σ * rhoL p J b Λ O hcomm σ - (d * a) • rhoL p J b Λ O hcomm σ
      + algebraMap O (Module.End O (lattice p J b Λ O)) (d * (ℓ : O)) = 0 := by
  have hK := rhoK_quadratic' p J b Λ hcomm hℓ σ hES _ _ ha hd
  refine LinearMap.ext fun v => Subtype.ext ?_
  have := LinearMap.congr_fun hK (v : Fin 2 → K)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, Module.End.one_apply] at this
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, Module.algebraMap_end_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_zero, coe_rhoL, Submodule.coe_smul_of_tower]
  rw [← algebraMap_smul K (d * a), ← algebraMap_smul K (d * (ℓ : O)), map_mul, map_mul, map_natCast]
  exact this

theorem det_rhoL [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (d : O)
    (hd : LinearMap.det (rhoK p J b Λ hcomm σ) = algebraMap O K d) :
    LinearMap.det (rhoL p J b Λ O hcomm σ) = d :=
  IsFractionRing.injective O K (by rw [algebraMap_det_rhoL p J b Λ O hc, hd])

def adicRep [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O) (hcomm : CommHyp p J)
    (hcont : ContHyp p J) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) : GaloisRepAdic O :=
  letI := lattice_free p J b Λ O hc
  letI := lattice_finite p J b Λ O hc
  { V := lattice p J b Λ O
    finrank_eq := finrank_lattice p J b Λ O hc
    ρ := rhoLHom p J b Λ O hcomm
    isAdicContinuous := rhoL_continuous p J b Λ O hc hcomm hcont hpm }

@[scoped simp] theorem adicRep_ρ [Module.Finite ℤ_[p] (TateModule p J)] (hc : Compat p J Λ O)
    (hcomm : CommHyp p J) (hcont : ContHyp p J) (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) : (adicRep p J b Λ O hc hcomm hcont hpm).ρ σ = rhoL p J b Λ O hcomm σ := rfl

end Lattice

section TraceId

open Polynomial

variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]

theorem eq_zero_of_smul_id_eq_zero (hV : 0 < Module.finrank O V) (c : O)
    (hc : c • (LinearMap.id : Module.End O V) = 0) : c = 0 := by
  classical
  nontriviality O
  let b := Module.Free.chooseBasis O V
  haveI : Nonempty (Module.Free.ChooseBasisIndex O V) := by
    rw [Module.finrank_eq_card_chooseBasisIndex] at hV
    exact Fintype.card_pos_iff.mp hV
  obtain ⟨i⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex O V)›
  have h1 : c • b i = 0 := by
    have := LinearMap.congr_fun hc (b i)
    simpa using this
  have h2 := congrArg (fun v => b.repr v i) h1
  simpa using h2

theorem charpoly_eq_of_quadratic_of_det (hV : Module.finrank O V = 2)
    (f : Module.End O V) (hf : IsUnit f) (t d : O)
    (hq : f * f - t • f + algebraMap O (Module.End O V) d = 0) (hdet : LinearMap.det f = d) :
    f.charpoly = X ^ 2 - C t * X + C d := by
  nontriviality O
  have hdeg : f.charpoly.natDegree = 2 := by rw [LinearMap.charpoly_natDegree, hV]
  have hmonic := f.charpoly_monic
  have hc0 : f.charpoly.coeff 0 = d := by
    have h := LinearMap.det_eq_sign_charpoly_coeff f
    rw [hV] at h
    rw [← hdet, h]
    ring
  set c₁ := f.charpoly.coeff 1 with hc₁
  have hshape : f.charpoly = X ^ 2 + C c₁ * X + C d := by
    apply Polynomial.ext
    intro n
    rcases n with _ | _ | _ | n
    · simp [hc0]
    · simp [hc₁]
    · have : f.charpoly.coeff 2 = 1 := by
        have := hmonic.leadingCoeff
        rwa [Polynomial.leadingCoeff, hdeg] at this
      simp [this]
    · have hlt : f.charpoly.natDegree < n + 3 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp
  have hCH : f * f + c₁ • f + algebraMap O (Module.End O V) d = 0 := by
    have h := LinearMap.aeval_self_charpoly f
    rw [hshape] at h
    simpa [sq, Algebra.smul_def] using h
  have hdiff : (t + c₁) • f = 0 := by
    have := sub_eq_zero.mpr (hCH.trans hq.symm)
    have e : f * f + c₁ • f + algebraMap O (Module.End O V) d
        - (f * f - t • f + algebraMap O (Module.End O V) d) = (t + c₁) • f := by
      rw [add_smul]; abel
    rw [e] at this
    exact this
  obtain ⟨u, rfl⟩ := hf
  have hid : (t + c₁) • (LinearMap.id : Module.End O V) = 0 := by
    have : ((t + c₁) • (u : Module.End O V)) * (↑u⁻¹ : Module.End O V) = 0 := by
      rw [hdiff, zero_mul]
    rwa [smul_mul_assoc, Units.mul_inv] at this
  have hpos : 0 < Module.finrank O V := by rw [hV]; exact two_pos
  have htc : t + c₁ = 0 := eq_zero_of_smul_id_eq_zero hpos _ hid
  have : c₁ = -t := by linear_combination htc
  rw [hshape, this, C_neg]
  ring

end TraceId

section MainCharpoly

open Polynomial

variable [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]

theorem main_charpoly [Module.Finite ℤ_[p] (TateModule p J)] (N : ℕ)
    (hcomm : CommHyp p J)
    (hi : RationalRankTwoNebentypusOf (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    (hiii : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ → ∀ x : TateModule p J,
          TateModule.rep p J HeckeAlgOne (diamondGen ℓ)
              (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
            - TateModule.rep p J HeckeAlgOne (heckeGenOne ⟨ℓ, hℓ⟩) (TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
            + ℓ • x = 0)
    (hv : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N * p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : TateModule p J, TateModule.rep p J (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x = x)
    (hcont : ContHyp p J)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (Λ : rationalHeckeAlgebraOne p J →+* K)
    (hc : Compat p J Λ O)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    ∃ ρ : GaloisRepAdic O,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * p → ∀ a d : O,
        Λ (rationalHeckeOne p J ⟨ℓ, hℓ⟩) = algebraMap O K a →
        Λ (rationalDiamondOne p J ℓ) * algebraMap O K d = 1 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (d * a) * X + C (d * (ℓ : O))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p → ρ.IsUnramifiedAt ℓ) := by
  obtain ⟨b, hb⟩ := hi
  refine ⟨adicRep p J b Λ O hc hcomm hcont hpm, ?_, ?_⟩
  · intro ℓ hℓ hℓNp a d ha hd A hA σ hσ
    have hq := rhoL_quadratic p J b Λ O hcomm hℓ σ (hiii ℓ hℓ hℓNp A hA σ hσ) a d ha hd
    have hdK : LinearMap.det (rhoK p J b Λ hcomm σ) = algebraMap O K (d * (ℓ : O)) := by
      have h1 := congrArg Λ (hb ℓ hℓ hℓNp A hA σ hσ)
      rw [map_mul, map_natCast, ← det_rhoK p J b Λ hcomm σ] at h1
      have h2 := congrArg (fun z => algebraMap O K d * z) h1
      beta_reduce at h2
      rw [← mul_assoc, mul_comm (algebraMap O K d), hd, one_mul] at h2
      rw [h2, map_mul, map_natCast]
    have hdet : LinearMap.det (rhoL p J b Λ O hcomm σ) = d * (ℓ : O) :=
      det_rhoL p J b Λ O hc hcomm σ _ hdK
    rw [adicRep_ρ]
    refine charpoly_eq_of_quadratic_of_det (adicRep p J b Λ O hc hcomm hcont hpm).finrank_eq
      (rhoL p J b Λ O hcomm σ) ?_ (d * a) (d * (ℓ : O)) hq hdet
    rw [← rhoLHom_apply]
    exact (Group.isUnit σ).map (rhoLHom p J b Λ O hcomm)
  · intro ℓ hℓ hℓNp A hA σ hσ
    exact rhoL_eq_one p J b Λ O hcomm σ (hv ℓ hℓ hℓNp A hA σ hσ)

end MainCharpoly

end E1G1ES
open scoped _root_.P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar.E1G1ES

open Polynomial in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (i₀ : ℤ_[p] →+* O) (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* K),
      (∀ c : ℤ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) (c : ℚ_[p]))
          = algebraMap O K (i₀ c)) →
      ∃ ρ : GaloisRepAdic O,
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * p → ∀ a d : O,
          Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) = algebraMap O K a →
          Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * algebraMap O K d = 1 →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (d * a) * X + C (d * (ℓ : O))) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M * p → ρ.IsUnramifiedAt ℓ) := by
  letI := ModularCurve.heckeModuleOneBar M
  intro Λ hΛ
  letI : Algebra ℤ_[p] O := i₀.toAlgebra
  have hp : p.Prime := Fact.out
  have hcb := ModularCurve.heckeDiamondCommuteBar M
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JOne M)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jOne M p
  have hcomm : E1G1ES.CommHyp p (ModularCurve.JOne M) := fun σ t x =>
    ModularCurve.rep_tateModule_jOne_comm M p hcb σ t x
  have hi : ModularCurve.RationalRankTwoNebentypus M p :=
    ModularCurve.rationalRankTwoNebentypus_family M p (Nat.pos_of_ne_zero (NeZero.ne M)) hp
  have hcont : E1G1ES.ContHyp p (ModularCurve.JOne M) := fun m =>
    ModularCurve.JOne.exists_finiteDimensional_smul_eq_self_of_torsion M (p ^ m) (pow_pos hp.pos m)
  have hc : E1G1ES.Compat p (ModularCurve.JOne M) Λ O := fun c => hΛ c
  exact E1G1ES.main_charpoly p (ModularCurve.JOne M) M hcomm hi
    (fun ℓ hℓ hℓNp A hA σ hσ x =>
      ModularCurve.frobeniusQuadratic_tateModule_jOne M p hcb hℓ hℓNp A hA σ hσ x)
    (fun ℓ hℓ hℓNp A hA σ hσ x =>
      ModularCurve.rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn M p hℓ hℓNp A hA σ hσ x)
    hcont O K Λ hc hpO
