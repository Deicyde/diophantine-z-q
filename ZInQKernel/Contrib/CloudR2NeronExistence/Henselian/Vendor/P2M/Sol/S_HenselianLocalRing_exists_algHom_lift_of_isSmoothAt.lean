import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt.lean
Original Git blob: 520adc087db24407343992c3d1ba3f49eb8f6ff1
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_etale
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open IsLocalRing TensorProduct
h77_open "IsLocalRing TensorProduct"
open scoped _root_.TensorProduct

namespace HenselSmoothLift
h77_bridge_namespace

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

theorem exists_lift_of_isStandardEtale_mvPolynomial
    {n : ℕ} (A : Type u) [CommRing A] [Algebra R A]
    [Algebra (MvPolynomial (Fin n) R) A] [IsScalarTower R (MvPolynomial (Fin n) R) A]
    [Algebra.IsStandardEtale (MvPolynomial (Fin n) R) A]
    (φ : A →ₐ[R] ResidueField R) :
    ∃ ψ : A →ₐ[R] R, ∀ a, algebraMap R (ResidueField R) (ψ a) = φ a := by

  let θ : MvPolynomial (Fin n) R →ₐ[R] ResidueField R :=
    φ.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) A)
  choose c hc using fun i : Fin n => residue_surjective (R := R) (θ (MvPolynomial.X i))
  let θ' : MvPolynomial (Fin n) R →ₐ[R] R := MvPolynomial.aeval c
  have hθ : ∀ r, algebraMap R (ResidueField R) (θ' r) = θ r := by
    intro r
    have h : (Algebra.ofId R (ResidueField R)).comp θ' = θ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [θ', hc]
    simpa using congrArg (fun g => g r) h

  letI iR : Algebra (MvPolynomial (Fin n) R) R := θ'.toRingHom.toAlgebra
  letI iK : Algebra (MvPolynomial (Fin n) R) (ResidueField R) :=
    ((algebraMap R (ResidueField R)).comp θ'.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin n) R) R (ResidueField R) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let φ' : A →ₐ[MvPolynomial (Fin n) R] ResidueField R :=
    { φ.toRingHom with
      commutes' := fun r => by
        change φ (algebraMap (MvPolynomial (Fin n) R) A r) =
          algebraMap R (ResidueField R) (θ' r)
        exact (hθ r).symm }

  let T : Type u := TensorProduct (MvPolynomial (Fin n) R) R A
  let φT : T →ₐ[R] ResidueField R :=
    Algebra.TensorProduct.lift (Algebra.ofId R (ResidueField R)) φ' (fun _ _ => Commute.all _ _)
  haveI : Algebra.Etale R T := inferInstance
  obtain ⟨ψT, hψT⟩ := HenselianLocalRing.exists_algHom_lift_of_etale T φT

  let χ : A →+* R :=
    ψT.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        A →ₐ[MvPolynomial (Fin n) R] T).toRingHom
  have hχ : ∀ a, χ a = ψT ((1 : R) ⊗ₜ[MvPolynomial (Fin n) R] a) := fun a => rfl
  have h1 : ∀ r : R, ((1 : R) ⊗ₜ[MvPolynomial (Fin n) R] algebraMap R A r : T) =
      algebraMap R T r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) A r,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    congr 1
    change θ' (algebraMap R (MvPolynomial (Fin n) R) r) • (1 : R) = r
    rw [θ'.commutes, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, mul_one]
  let ψ : A →ₐ[R] R :=
    { χ with
      commutes' := fun r => by
        change χ (algebraMap R A r) = r
        rw [hχ, h1, ψT.commutes, Algebra.algebraMap_self, RingHom.id_apply] }
  refine ⟨ψ, fun a => ?_⟩
  change algebraMap R (ResidueField R) (χ a) = φ a
  rw [hχ, hψT]
  change Algebra.TensorProduct.lift _ _ _ ((1 : R) ⊗ₜ[MvPolynomial (Fin n) R] a) = φ a
  rw [Algebra.TensorProduct.lift_tmul]
  simp [φ']

theorem exists_lift_of_isSmoothAt
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (φ : S →ₐ[R] ResidueField R)
    [(RingHom.ker φ).IsPrime] [Algebra.IsSmoothAt R (RingHom.ker φ)] :
    ∃ ψ : S →ₐ[R] R, ∀ s, algebraMap R (ResidueField R) (ψ s) = φ s := by
  obtain ⟨f, hf, n, iA, iT, iE⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := RingHom.ker φ)
  have hu : ∀ y : Submonoid.powers f, IsUnit (φ y) := by
    rintro ⟨y, k, rfl⟩
    rw [map_pow]
    refine IsUnit.pow _ (Ne.isUnit ?_)
    simpa [RingHom.mem_ker] using hf
  let φf : Localization.Away f →ₐ[R] ResidueField R :=
    IsLocalization.liftAlgHom (M := Submonoid.powers f) hu
  have hφf : ∀ s, φf (algebraMap S (Localization.Away f) s) = φ s := fun s => by
    simp [φf, IsLocalization.liftAlgHom_apply]
  obtain ⟨ψf, hψf⟩ :=
    @exists_lift_of_isStandardEtale_mvPolynomial R _ _ n (Localization.Away f) _ _ iA iT iE φf
  refine ⟨ψf.comp (IsScalarTower.toAlgHom R S (Localization.Away f)), fun s => ?_⟩
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hψf, hφf]

theorem exists_lift_of_smooth
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, ∀ s, algebraMap R (ResidueField R) (ψ s) = φ s := by
  haveI := RingHom.ker_isPrime φ
  exact exists_lift_of_isSmoothAt S φ

end HenselSmoothLift

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R)
    [(RingHom.ker φ).IsPrime] [Algebra.IsSmoothAt R (RingHom.ker φ)] :
    ∃ ψ : S →ₐ[R] R, ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s :=
  HenselSmoothLift.exists_lift_of_isSmoothAt S φ


end P2MW.S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
