import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus.lean
Original Git blob: 59db418ca3c62f8f41b5a8a960d977aa96664b94
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AffineDilatation_exists_algHom_isLocalization_map
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AffineDilatation_isSMulRegular_and_map_eq_span_singleton
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_Algebra_exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

open KaehlerDifferential IsLocalRing

noncomputable section

namespace NeronJacobiSkeleton
h77_bridge_namespace

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X)

abbrev globalAlgebra : Algebra R Γ(X, ⊤) :=
  (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

abbrev globalPointAlgebra : Algebra Γ(X, ⊤) R' :=
  ((Scheme.stalkClosedPointTo a).hom.comp
    (X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R')) trivial).hom).toAlgebra

theorem smoothnessDefect_eq_length_torsion_global [IsAffine X] :
    smoothnessDefect f a =
      (letI : Algebra R Γ(X, ⊤) := globalAlgebra f
       letI : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
       Module.length R' (Submodule.torsion R' (R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]))) := by
  rw [smoothnessDefect_def]

  set x : X := a (IsLocalRing.closedPoint R') with hx
  letI iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  letI iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  letI iRO : Algebra R (X.presheaf.stalk x) := stalkAlgebra f x
  letI iOR' : Algebra (X.presheaf.stalk x) R' := pointAlgebra a
  letI iAO : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  haveI : IsScalarTower R Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, ⊤) (X.presheaf.stalk x) R' :=
    IsScalarTower.of_algebraMap_eq' rfl

  haveI : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  haveI : Algebra.FormallyEtale Γ(X, ⊤) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization
      (((isAffineOpen_top X).primeIdealOf (⟨x, trivial⟩ : (⊤ : X.Opens))).asIdeal.primeCompl)

  let e₁ : (X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(X, ⊤) (X.presheaf.stalk x)
  let e₂ : R' ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] ≃ₗ[R']
      R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) :=
    (e₁.symm.baseChange (X.presheaf.stalk x) R' _ _)
  let e₃ : R' ⊗[X.presheaf.stalk x] ((X.presheaf.stalk x) ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R]) ≃ₗ[R']
      R' ⊗[Γ(X, ⊤)] Ω[Γ(X, ⊤)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(X, ⊤) (X.presheaf.stalk x) R' R' Ω[Γ(X, ⊤)⁄R]
  exact length_torsion_eq_of_equiv' (e₂.trans e₃)
where

  length_torsion_eq_of_equiv' {S : Type u} [CommRing S] {M M' : Type u}
      [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M'] (e : M ≃ₗ[S] M') :
      Module.length S (Submodule.torsion S M) = Module.length S (Submodule.torsion S M') := by
    have : (Submodule.torsion S M).map (e : M →ₗ[S] M') = Submodule.torsion S M' := by
      ext y
      simp only [Submodule.mem_map, Submodule.mem_torsion_iff]
      constructor
      · rintro ⟨x, ⟨a, ha⟩, rfl⟩
        refine ⟨a, ?_⟩
        change (a : S) • (e : M →ₗ[S] M') x = 0
        change (a : S) • x = 0 at ha
        rw [← map_smul, ha, map_zero]
      · rintro ⟨a, ha⟩
        refine ⟨e.symm y, ⟨a, ?_⟩, by simp⟩
        change (a : S) • e.symm y = 0
        change (a : S) • y = 0 at ha
        rw [← map_smul, ha, map_zero]
    rw [← this]
    exact (e.submoduleMap (Submodule.torsion S M)).length_eq

theorem algebraMap_globalPointAlgebra_globalAlgebra [Algebra R R']
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R'))) (r : R) :
    (letI : Algebra R Γ(X, ⊤) := globalAlgebra f
     letI : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
     algebraMap Γ(X, ⊤) R' (algebraMap R Γ(X, ⊤) r)) = algebraMap R R' r := by
  letI iRA : Algebra R Γ(X, ⊤) := globalAlgebra f
  letI iAR' : Algebra Γ(X, ⊤) R' := globalPointAlgebra a
  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint R')) trivial).hom
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r

  have h1 := Scheme.Hom.germ_stalkMap_apply f ⊤ (a (IsLocalRing.closedPoint R')) trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

  change (Scheme.stalkClosedPointTo a).hom ((X.presheaf.germ (f ⁻¹ᵁ ⊤) (a (IsLocalRing.closedPoint R')) trivial).hom
    ((f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R R' r
  rw [← h1]

  rw [← CommRingCat.comp_apply, ← Scheme.stalkClosedPointTo_comp]
  have key : ∀ (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      g = Spec.map (CommRingCat.ofHom (algebraMap R R')) → ∀ s,
      (Scheme.stalkClosedPointTo g).hom
        (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (g (IsLocalRing.closedPoint R')) trivial).hom s) =
        algebraMap R R' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by
    rintro g rfl s
    have h3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap R R'))
    have := congrArg (fun φ : (Spec (CommRingCat.of R)).presheaf.obj (Opposite.op ⊤) ⟶ CommRingCat.of R' =>
      φ.hom s) h3
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  refine (key (a ≫ f) ha _).trans ?_
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem smoothnessDefect_Spec_eq {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (φ : A →+* R') :
    smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom φ)) =
      (letI : Algebra A R' := φ.toAlgebra
       Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R]))) := by
  rw [smoothnessDefect_eq_length_torsion_global]
  set Γ' : Type u := Γ(Spec (CommRingCat.of A), ⊤) with hΓ
  letI iRΓ : Algebra R Γ(Spec (CommRingCat.of A), ⊤) :=
    globalAlgebra (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  letI iΓR' : Algebra Γ(Spec (CommRingCat.of A), ⊤) R' := globalPointAlgebra (Spec.map (CommRingCat.ofHom φ))
  letI iAR' : Algebra A R' := φ.toAlgebra
  letI iΓA : Algebra Γ(Spec (CommRingCat.of A), ⊤) A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
  haveI : IsScalarTower R Γ(Spec (CommRingCat.of A), ⊤) A := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext; intro r
    change algebraMap R A r = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
      ← CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id]
    rfl)
  haveI : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) A R' := IsScalarTower.of_algebraMap_eq' (by
    change ((Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ))).hom.comp
      ((Spec (CommRingCat.of A)).presheaf.germ ⊤ _ trivial).hom) =
      φ.comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    rw [← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo_Spec]
    rfl)
  haveI : IsLocalization.Away (1 : Γ(Spec (CommRingCat.of A), ⊤)) A :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
  haveI : Algebra.FormallyEtale Γ(Spec (CommRingCat.of A), ⊤) A :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : Γ(Spec (CommRingCat.of A), ⊤)))
  let e₁ : A ⊗[Γ(Spec (CommRingCat.of A), ⊤)] Ω[Γ(Spec (CommRingCat.of A), ⊤)⁄R] ≃ₗ[A] Ω[A⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Γ(Spec (CommRingCat.of A), ⊤) A
  let e₂ := (e₁.symm.baseChange A R' _ _)
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(Spec (CommRingCat.of A), ⊤) A R' R'
    Ω[Γ(Spec (CommRingCat.of A), ⊤)⁄R]
  exact (smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' (e₂.trans e₃)).symm

theorem length_torsion_baseChange_kaehler_eq_of_formallyEtale
    (R : Type u) [CommRing R] (A S R' : Type u) [CommRing A] [CommRing S] [CommRing R']
    [Algebra R A] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra A R'] [Algebra S R'] [IsScalarTower A S R'] [Algebra.FormallyEtale A S] :
    Module.length R' (Submodule.torsion R' (R' ⊗[S] Ω[S⁄R])) =
      Module.length R' (Submodule.torsion R' (R' ⊗[A] Ω[A⁄R])) := by
  let e₁ : S ⊗[A] Ω[A⁄R] ≃ₗ[S] Ω[S⁄R] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S
  let e₂ := (e₁.symm.baseChange S R' _ _)
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange A S R' R' Ω[A⁄R]
  exact smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' (e₂.trans e₃)

theorem length_torsion_quotient_mono_of_forall_exists_smul_mem
    {S : Type u} [CommRing S] [IsDomain S] {M : Type u} [AddCommGroup M] [Module S M]
    (N₁ N₂ : Submodule S M) (hle : N₁ ≤ N₂) (htor : ∀ x ∈ N₂, ∃ s : S, s ≠ 0 ∧ s • x ∈ N₁) :
    Module.length S (Submodule.torsion S (M ⧸ N₂)) ≤ Module.length S (Submodule.torsion S (M ⧸ N₁)) := by

  let q : (M ⧸ N₁) →ₗ[S] (M ⧸ N₂) := Submodule.factor hle
  have hq : ∀ y : M ⧸ N₂, y ∈ Submodule.torsion S (M ⧸ N₂) →
      ∃ x ∈ Submodule.torsion S (M ⧸ N₁), q x = y := by
    intro y hy
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N₂ y
    obtain ⟨⟨a, ha⟩, hay⟩ := (Submodule.mem_torsion_iff _).mp hy
    change (a : S) • (Submodule.Quotient.mk m : M ⧸ N₂) = 0 at hay
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hay
    obtain ⟨s, hs, hsm⟩ := htor _ hay
    refine ⟨Submodule.Quotient.mk m, ?_, rfl⟩
    refine (Submodule.mem_torsion_iff _).mpr ⟨⟨s * a, mul_ne_zero hs (nonZeroDivisors.ne_zero ha) |>
      mem_nonZeroDivisors_of_ne_zero⟩, ?_⟩
    change (s * (a : S)) • (Submodule.Quotient.mk m : M ⧸ N₁) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul]
    exact hsm
  let q' : Submodule.torsion S (M ⧸ N₁) →ₗ[S] Submodule.torsion S (M ⧸ N₂) :=
    (q.restrict fun x hx => by
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp hx
      exact (Submodule.mem_torsion_iff _).mpr ⟨a, by
        change (a : S) • q x = 0; rw [← map_smul]; change q ((a : S) • x) = 0
        rw [show (a : S) • (x : M ⧸ N₁) = 0 from ha, map_zero]⟩)
  have hq' : Function.Surjective q' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hq y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Module.length_le_of_surjective q' hq'

theorem one_tmul_smul_eq {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] {M : Type u} [AddCommGroup M]
    [Module S M] (c : S) (m : M) :
    ((1 : T) ⊗ₜ[S] (c • m) : T ⊗[S] M) = algebraMap S T c • ((1 : T) ⊗ₜ[S] m) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]

private theorem transported_detection_fixed
    {R0 A0 C0 Ag0 : Type u} [CommRing R0] [IsDomain R0] [IsDiscreteValuationRing R0]
    [CommRing A0] [Algebra R0 A0] [CommRing C0] [Algebra R0 C0]
    (g : A0) [CommRing Ag0] [Algebra A0 Ag0] [IsLocalization.Away g Ag0]
    [Algebra R0 Ag0] [IsScalarTower R0 A0 Ag0] [Algebra C0 Ag0] [IsScalarTower R0 C0 Ag0]
    (J0 : Ideal A0) (JC0 : Ideal C0)
    (hJC0 : (J0.map (algebraMap A0 Ag0)).comap (algebraMap C0 Ag0) = JC0)
    (hN0 : ∀ a : A0,
      (∀ (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R0 S]
        [IsLocalHom (algebraMap R0 S)], IsIndexOneExtension R0 S →
        ∀ c : A0 →ₐ[R0] S, J0 ≤ (IsLocalRing.maximalIdeal S).comap c →
          a ∈ (IsLocalRing.maximalIdeal S).comap c) → a ∈ J0) :
    ∀ c0 : C0,
      (∀ (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R0 S]
        [IsLocalHom (algebraMap R0 S)], IsIndexOneExtension R0 S →
        ∀ c : C0 →ₐ[R0] S, RingHom.ker (algebraMap C0 Ag0) ≤ RingHom.ker c.toRingHom →
          JC0 ≤ (IsLocalRing.maximalIdeal S).comap c → c0 ∈ (IsLocalRing.maximalIdeal S).comap c) →
      c0 ∈ JC0 := by
  intro c0 hc0
  rw [← hJC0, Ideal.mem_comap]
  obtain ⟨⟨a0, ⟨_, ⟨m, rfl⟩⟩⟩, ha0⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) (algebraMap C0 Ag0 c0)
  have hclaim : a0 * g ∈ J0 := by
    apply hN0
    intro S _ _ _ _ _ hS c hJc
    by_cases hcg : c g ∈ IsLocalRing.maximalIdeal S
    · exact Ideal.mem_comap.mpr (by rw [map_mul]; exact Ideal.mul_mem_left _ _ hcg)
    · have hu : IsUnit (c.toRingHom g) := IsLocalRing.notMem_maximalIdeal.mp hcg
      let cg : Ag0 →+* S := IsLocalization.Away.lift g (g := c.toRingHom) hu
      have hcg_eq : ∀ a, cg (algebraMap A0 Ag0 a) = c a := IsLocalization.Away.lift_eq g hu
      let ct : C0 →ₐ[R0] S := AlgHom.mk (cg.comp (algebraMap C0 Ag0)) (fun r => by
        change cg (algebraMap C0 Ag0 (algebraMap R0 C0 r)) = algebraMap R0 S r
        rw [← IsScalarTower.algebraMap_apply R0 C0 Ag0, IsScalarTower.algebraMap_apply R0 A0 Ag0,
          hcg_eq, AlgHom.commutes])
      have hker : RingHom.ker (algebraMap C0 Ag0) ≤ RingHom.ker ct.toRingHom := by
        intro x hx
        simp only [RingHom.mem_ker] at hx ⊢
        change cg (algebraMap C0 Ag0 x) = 0
        rw [hx, map_zero]
      have hJle : JC0 ≤ (IsLocalRing.maximalIdeal S).comap ct := by
        rw [← hJC0]
        intro x hx
        rw [Ideal.mem_comap] at hx ⊢
        change cg (algebraMap C0 Ag0 x) ∈ IsLocalRing.maximalIdeal S
        have hm : J0.map (algebraMap A0 Ag0) ≤ (IsLocalRing.maximalIdeal S).comap cg := by
          rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
          intro a ha
          rw [Ideal.mem_comap, RingHom.comp_apply, hcg_eq]
          exact hJc ha
        exact hm hx
      have h1 := hc0 S hS ct hker hJle
      rw [Ideal.mem_comap] at h1
      change cg (algebraMap C0 Ag0 c0) ∈ IsLocalRing.maximalIdeal S at h1
      rw [← ha0] at h1
      have h2 : cg (IsLocalization.mk' Ag0 a0 (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)) *
          cg (algebraMap A0 Ag0 (g ^ m)) = c a0 := by
        rw [← map_mul, IsLocalization.mk'_spec, hcg_eq]
      rw [Ideal.mem_comap, map_mul, ← h2, mul_assoc]
      exact Ideal.mul_mem_right _ _ h1
  have h3 : algebraMap C0 Ag0 c0 =
      algebraMap A0 Ag0 (a0 * g) * IsLocalization.mk' Ag0 1 (⟨g ^ (m + 1), m + 1, rfl⟩ : Submonoid.powers g) := by
    rw [← ha0, ← IsLocalization.mk'_one (M := Submonoid.powers g) Ag0, ← IsLocalization.mk'_mul]
    rw [IsLocalization.mk'_eq_iff_eq]
    simp only [one_mul, mul_one]
    congr 1
    ring
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hclaim)

private theorem derivative_image_mem_fixed
    {R0 C0 T0 B0 S0 : Type u} [CommRing R0] [CommRing C0] [CommRing T0]
    [CommRing B0] [CommRing S0] [Algebra R0 T0] [Algebra T0 S0]
    (σ : C0 →+* T0) (θ : T0 →+* B0) (φ : B0 →+* S0)
    (hχ : ∀ x : T0, algebraMap T0 S0 x = φ (θ x))
    (I : Ideal C0) (a : T0) (r : R0) (ha : a ^ 2 = algebraMap R0 T0 r)
    (fp : I → T0) (hfp : ∀ f : I, a ^ 2 * fp f = σ (f : C0))
    (hθI : ∀ f : I, θ (σ (f : C0)) = 0)
    (N : Submodule S0 (S0 ⊗[T0] Ω[T0⁄R0]))
    (hgen : ∀ f : I, (1 : S0) ⊗ₜ[T0] D R0 T0 (fp f) ∈ N) :
    ∀ x ∈ I.map σ, θ x = 0 ∧ ((1 : S0) ⊗ₜ[T0] D R0 T0 x) ∈ N := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => θ x = 0 ∧ ((1 : S0) ⊗ₜ[T0] D R0 T0 x) ∈ N)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨f, hf, rfl⟩
    refine ⟨hθI ⟨f, hf⟩, ?_⟩
    rw [← hfp ⟨f, hf⟩, Derivation.leibniz, ha, Derivation.map_algebraMap,
      smul_zero, add_zero, one_tmul_smul_eq]
    exact N.smul_mem _ (hgen ⟨f, hf⟩)
  · exact ⟨map_zero _, by rw [map_zero, TensorProduct.tmul_zero]; exact N.zero_mem⟩
  · rintro x y - - ⟨hx0, hx⟩ ⟨hy0, hy⟩
    exact ⟨by rw [map_add, hx0, hy0, add_zero], by rw [map_add, TensorProduct.tmul_add]; exact N.add_mem hx hy⟩
  · rintro c x - ⟨hx0, hx⟩
    refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], ?_⟩
    rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add, one_tmul_smul_eq, one_tmul_smul_eq]
    have hχx : algebraMap T0 S0 x = 0 := by rw [hχ, hx0, map_zero]
    rw [hχx, zero_smul, add_zero]
    exact N.smul_mem _ hx

private theorem derivative_kernel_saturation_fixed
    {R0 T0 B0 S0 : Type u} [CommRing R0] [CommRing T0] [CommRing B0]
    [CommRing S0] [IsDomain S0] [Algebra R0 T0] [Algebra T0 S0]
    (π0 : R0) (θ : T0 →+* B0) (φ : B0 →+* S0)
    (hχ : ∀ x : T0, algebraMap T0 S0 x = φ (θ x))
    (I0 : Ideal T0)
    (hpow : ∀ x : T0, θ x = 0 → ∃ ν : ℕ, (algebraMap R0 T0 π0) ^ ν * x ∈ I0)
    (hπ : algebraMap T0 S0 (algebraMap R0 T0 π0) ≠ 0)
    (N : Submodule S0 (S0 ⊗[T0] Ω[T0⁄R0]))
    (hderiv : ∀ x ∈ I0, ((1 : S0) ⊗ₜ[T0] D R0 T0 x) ∈ N) :
    ∀ x ∈ Submodule.span S0 (Set.range fun f : RingHom.ker θ =>
      (1 : S0) ⊗ₜ[T0] D R0 T0 (f : T0)), ∃ s : S0, s ≠ 0 ∧ s • x ∈ N := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => ∃ s : S0, s ≠ 0 ∧ s • x ∈ N) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨⟨f, hf⟩, rfl⟩
    have h0 : θ f = 0 := RingHom.mem_ker.mp hf
    obtain ⟨ν, hν⟩ := hpow f h0
    refine ⟨(algebraMap T0 S0 (algebraMap R0 T0 π0)) ^ ν, pow_ne_zero ν hπ, ?_⟩
    have h1 := hderiv _ hν
    rw [Derivation.leibniz, TensorProduct.tmul_add, one_tmul_smul_eq, one_tmul_smul_eq, map_pow] at h1
    have h2 : D R0 T0 ((algebraMap R0 T0 π0) ^ ν) = 0 := by
      rw [← map_pow]
      exact Derivation.map_algebraMap _ _
    rw [h2, TensorProduct.tmul_zero, smul_zero, add_zero] at h1
    exact h1
  · exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
  · rintro x y - - ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    exact N.add_mem (by rw [mul_comm, mul_smul]; exact N.smul_mem t hsx)
      (by rw [mul_smul]; exact N.smul_mem s hty)
  · rintro a x - ⟨s, hs, hsx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact N.smul_mem _ hsx

private theorem block_basis_comparison_fixed
    {S0 M0 N0 : Type u} [CommRing S0] [AddCommGroup M0] [Module S0 M0]
    [AddCommGroup N0] [Module S0 N0] (π0 : S0) (r n : ℕ)
    (b : Module.Basis (Fin r ⊕ Fin n) S0 M0) (b' : Module.Basis (Fin r ⊕ Fin n) S0 N0)
    (Φ : M0 →ₗ[S0] N0)
    (hy : ∀ i, Φ (b (Sum.inl i)) = b' (Sum.inl i))
    (hz : ∀ j, Φ (b (Sum.inr j)) = π0 • b' (Sum.inr j)) :
    let e0 : (Fin r ⊕ Fin n → S0) ≃ₗ[S0] ((Fin r → S0) × (Fin n → S0)) :=
      LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin n) S0 S0
    let κ := b.equivFun.trans e0
    let κ' := b'.equivFun.trans e0
    let Dm := (LinearMap.id : (Fin r → S0) →ₗ[S0] (Fin r → S0)).prodMap
      (π0 • (LinearMap.id : (Fin n → S0) →ₗ[S0] (Fin n → S0)))
    κ'.toLinearMap.comp Φ = Dm.comp κ.toLinearMap := by
  let e0 : (Fin r ⊕ Fin n → S0) ≃ₗ[S0] ((Fin r → S0) × (Fin n → S0)) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin n) S0 S0
  let κ := b.equivFun.trans e0
  let κ' := b'.equivFun.trans e0
  let Dm := (LinearMap.id : (Fin r → S0) →ₗ[S0] (Fin r → S0)).prodMap
    (π0 • (LinearMap.id : (Fin n → S0) →ₗ[S0] (Fin n → S0)))
  have he0 : ∀ f : Fin r ⊕ Fin n → S0, e0 f = (fun i => f (Sum.inl i), fun j => f (Sum.inr j)) := fun f => rfl
  have hDm : ∀ (u : Fin r → S0) (w : Fin n → S0), Dm (u, w) = (u, π0 • w) := fun u w => rfl
  refine b.ext fun k => ?_
  rcases k with i | j
  · change κ' (Φ (b (Sum.inl i))) = Dm (κ (b (Sum.inl i)))
    rw [hy]
    change e0 (b'.equivFun (b' (Sum.inl i))) = Dm (e0 (b.equivFun (b (Sum.inl i))))
    refine Prod.ext (funext fun i' => ?_) (funext fun j' => ?_)
    · simp [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDm, Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]
    · simp [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDm, Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]
  · change κ' (Φ (b (Sum.inr j))) = Dm (κ (b (Sum.inr j)))
    rw [hz, map_smul]
    change π0 • e0 (b'.equivFun (b' (Sum.inr j))) = Dm (e0 (b.equivFun (b (Sum.inr j))))
    refine Prod.ext (funext fun i' => ?_) (funext fun j' => ?_)
    · simp [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDm, Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]
    · simp [Module.Basis.equivFun_apply, Module.Basis.repr_self, he0, hDm, Finsupp.single_apply, Prod.smul_mk, Pi.smul_apply, smul_ite]

private theorem dvr_diagonal_length_comparison_fixed
    {S0 M0 N0 : Type u} [CommRing S0] [IsDomain S0] [IsDiscreteValuationRing S0]
    [AddCommGroup M0] [Module S0 M0] [AddCommGroup N0] [Module S0 N0]
    (π0 : S0) (hπ0 : Irreducible π0) (r n : ℕ)
    (κ : M0 ≃ₗ[S0] ((Fin r → S0) × (Fin n → S0)))
    (κ' : N0 ≃ₗ[S0] ((Fin r → S0) × (Fin n → S0))) (Φ : M0 →ₗ[S0] N0)
    (I : Submodule S0 M0) (J : Submodule S0 N0) (Jfull : Submodule S0 N0)
    (hmono : Module.length S0 (Submodule.torsion S0 (N0 ⧸ Jfull)) ≤
      Module.length S0 (Submodule.torsion S0 (N0 ⧸ J)))
    (hmap : I.map Φ = (Ideal.span {π0 ^ 2} : Ideal S0) • J)
    (hdiag : κ'.toLinearMap.comp Φ =
      ((LinearMap.id : (Fin r → S0) →ₗ[S0] (Fin r → S0)).prodMap
        (π0 • (LinearMap.id : (Fin n → S0) →ₗ[S0] (Fin n → S0)))).comp κ.toLinearMap) :
    Module.length S0 (Submodule.torsion S0 (N0 ⧸ Jfull)) + 1 ≤
      max 1 (Module.length S0 (Submodule.torsion S0 (M0 ⧸ I))) := by
  classical
  let Dm : ((Fin r → S0) × (Fin n → S0)) →ₗ[S0] ((Fin r → S0) × (Fin n → S0)) :=
    (LinearMap.id : (Fin r → S0) →ₗ[S0] (Fin r → S0)).prodMap
      (π0 • (LinearMap.id : (Fin n → S0) →ₗ[S0] (Fin n → S0)))
  let I2 : Ideal S0 := Ideal.span {π0 ^ 2}
  have hNcDm : (I.map κ.toLinearMap).map Dm = I2 • J.map κ'.toLinearMap := by
    rw [← Submodule.map_comp, ← hdiag, Submodule.map_comp, hmap, Submodule.map_smul'']
  let Fsub : Submodule S0 ((Fin r → S0) × (Fin n → S0)) :=
    (⊤ : Submodule S0 (Fin r → S0)).prod ((Ideal.span {π0} : Ideal S0) • ⊤)
  have hDm_mem : ∀ v : ((Fin r → S0) × (Fin n → S0)), Dm v ∈ Fsub := by
    rintro ⟨u, w⟩
    refine ⟨trivial, ?_⟩
    change π0 • w ∈ (Ideal.span {π0} : Ideal S0) • (⊤ : Submodule S0 (Fin n → S0))
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hDm_inj : Function.Injective Dm := by
    rintro ⟨u, w⟩ ⟨u', w'⟩ h
    simp only [Dm, LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have hw : w = w' := smul_right_injective (Fin n → S0) hπ0.ne_zero h2
    rw [hw]
  have hDm_surj : ∀ y ∈ Fsub, ∃ v, Dm v = y := by
    rintro ⟨u, w'⟩ ⟨-, hw'⟩
    change w' ∈ (Ideal.span {π0} : Ideal S0) • (⊤ : Submodule S0 (Fin n → S0)) at hw'
    rw [Submodule.ideal_span_singleton_smul] at hw'
    obtain ⟨w, -, rfl⟩ := hw'
    exact ⟨(u, w), rfl⟩
  let Dm' : ((Fin r → S0) × (Fin n → S0)) ≃ₗ[S0] Fsub :=
    LinearEquiv.ofBijective (Dm.codRestrict Fsub hDm_mem)
      ⟨fun a b h => hDm_inj (congrArg Subtype.val h), fun y => by
        obtain ⟨v, hv⟩ := hDm_surj y.1 y.2
        exact ⟨v, Subtype.ext hv⟩⟩
  have hJhyp : I2 • J.map κ'.toLinearMap ≤ Fsub := by
    rw [← hNcDm]
    rintro _ ⟨v, -, rfl⟩
    exact hDm_mem v
  have hJ := IsDiscreteValuationRing.length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
    π0 hπ0 r n (J.map κ'.toLinearMap) hJhyp
  have eq1 : Module.length S0 (Submodule.torsion S0 (N0 ⧸ J)) =
      Module.length S0 (Submodule.torsion S0 (((Fin r → S0) × (Fin n → S0)) ⧸ J.map κ'.toLinearMap)) :=
    smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' (Submodule.Quotient.equiv _ _ κ' rfl)
  have hmapDm' : I.map (κ.trans Dm').toLinearMap =
      (I2 • J.map κ'.toLinearMap).comap Fsub.subtype := by
    rw [← hNcDm]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨κ x, Submodule.mem_map_of_mem hx, rfl⟩
    · rintro ⟨v, ⟨x, hx, rfl⟩, hv⟩
      refine ⟨x, hx, Subtype.ext ?_⟩
      change Dm (κ x) = Fsub.subtype y
      exact hv
  have eq2 : Module.length S0 (Submodule.torsion S0 (M0 ⧸ I)) =
      Module.length S0 (Submodule.torsion S0 (Fsub ⧸ (I2 • J.map κ'.toLinearMap).comap Fsub.subtype)) :=
    smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv'
      (Submodule.Quotient.equiv _ _ (κ.trans Dm') hmapDm')
  have key : Module.length S0 (Submodule.torsion S0 (N0 ⧸ J)) +
      Module.finrank S0 (J.map κ'.toLinearMap) ≤ Module.length S0 (Submodule.torsion S0 (M0 ⧸ I)) := by
    rw [eq1, eq2]
    exact hJ
  by_cases hρ : Module.finrank S0 (J.map κ'.toLinearMap) = 0
  · have hbot : J.map κ'.toLinearMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.mp hρ) ⟨x, hx⟩
      have h' : a • x = 0 := congrArg Subtype.val hax
      exact (smul_eq_zero.mp h').resolve_left ha
    have h0 : Module.length S0 (Submodule.torsion S0
        (((Fin r → S0) × (Fin n → S0)) ⧸ J.map κ'.toLinearMap)) = 0 := by
      rw [hbot]
      have e := Submodule.quotEquivOfEqBot (⊥ : Submodule S0 ((Fin r → S0) × (Fin n → S0))) rfl
      rw [smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' e,
        Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance]
      exact Module.length_bot
    have h0' : Module.length S0 (Submodule.torsion S0 (N0 ⧸ Jfull)) = 0 :=
      le_antisymm (hmono.trans (by rw [eq1, h0])) bot_le
    rw [h0', zero_add]
    exact le_max_left _ _
  · have h1 : (1 : ℕ∞) ≤ Module.finrank S0 (J.map κ'.toLinearMap) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hρ
    calc Module.length S0 (Submodule.torsion S0 (N0 ⧸ Jfull)) + 1
        ≤ Module.length S0 (Submodule.torsion S0 (N0 ⧸ J)) + Module.finrank S0 (J.map κ'.toLinearMap) :=
          add_le_add hmono h1
      _ ≤ Module.length S0 (Submodule.torsion S0 (M0 ⧸ I)) := key
      _ ≤ _ := le_max_right _ _

private theorem localization_point_compatibility_fixed
    {A0 Ag0 A1 B0 S0 : Type u} [CommRing A0] [CommRing Ag0] [CommRing A1]
    [CommRing B0] [CommRing S0] (g : A0) [Algebra A0 Ag0] [IsLocalization.Away g Ag0]
    [Algebra A0 A1] [Algebra A0 B0] [Algebra Ag0 B0] [Algebra A1 B0]
    [IsScalarTower A0 Ag0 B0] [IsScalarTower A0 A1 B0]
    (φ : A0 →+* S0) (φg : Ag0 →+* S0) (φ1 : A1 →+* S0) (φB : B0 →+* S0)
    (hφg : ∀ a, φg (algebraMap A0 Ag0 a) = φ a)
    (hφ1 : ∀ a, φ1 (algebraMap A0 A1 a) = φ a)
    (hφB : ∀ a, φB (algebraMap A1 B0 a) = φ1 a) :
    φB.comp (algebraMap Ag0 B0) = φg := by
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  ext a
  simp only [RingHom.comp_apply]
  rw [hφg, ← IsScalarTower.algebraMap_apply A0 Ag0 B0,
    IsScalarTower.algebraMap_apply A0 A1 B0, hφB, hφ1]

private theorem regular_kernel_lift_zero_fixed
    {C0 D0 B0 : Type u} [CommRing C0] [CommRing D0] [CommRing B0] [Algebra C0 B0]
    (θ : D0 →+* B0) (a : D0) (c : C0) (ha : θ a = algebraMap C0 B0 c)
    (hreg : IsSMulRegular B0 c) {ι : Type u} (fp : ι → D0) (s : ι → D0)
    (hfp : ∀ i, a ^ 2 * fp i = s i) (hs : ∀ i, θ (s i) = 0) :
    ∀ i, θ (fp i) = 0 := by
  intro i
  have h1 : θ (a ^ 2 * fp i) = 0 := by rw [hfp, hs]
  rw [map_mul, map_pow, ha] at h1
  have h2 : c ^ 2 • θ (fp i) = 0 := by rw [Algebra.smul_def, map_pow]; exact h1
  exact (hreg.pow 2) (show c ^ 2 • θ (fp i) = c ^ 2 • (0 : B0) by rw [h2, smul_zero])

private theorem span_generator_image_fixed
    {S0 M0 N0 : Type u} [CommRing S0] [AddCommGroup M0] [Module S0 M0]
    [AddCommGroup N0] [Module S0 N0] {ι : Type u}
    (u : ι → M0) (v : ι → N0) (Φ : M0 →ₗ[S0] N0) (a : S0)
    (hΦ : ∀ i, Φ (u i) = a • v i) :
    (Submodule.span S0 (Set.range u)).map Φ =
      (Ideal.span {a} : Ideal S0) • Submodule.span S0 (Set.range v) := by
  apply le_antisymm
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [hΦ]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.smul_le]
    rintro c hc x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    rw [mul_smul]
    refine Submodule.smul_mem _ t ?_
    have hle : Submodule.span S0 (Set.range v) ≤
        ((Submodule.span S0 (Set.range u)).map Φ).comap (a • LinearMap.id) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      change a • v i ∈ (Submodule.span S0 (Set.range u)).map Φ
      rw [← hΦ i]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] using hle hx

private theorem tensor_kernel_diagonal_comparison_fixed
    {R0 C0 D0 B0 S0 : Type u} [CommRing R0] [CommRing C0] [CommRing D0] [CommRing B0]
    [CommRing S0] [IsDomain S0] [IsDiscreteValuationRing S0]
    [Algebra R0 C0] [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0]
    [Algebra C0 S0] [Algebra D0 S0] [IsScalarTower C0 D0 S0]
    (π0 : R0) (πS : S0) (hπS : Irreducible πS)
    (hπmap : algebraMap D0 S0 (algebraMap R0 D0 π0) = πS)
    (θ : D0 →+* B0) (φB : B0 →+* S0) (hχ : ∀ x, algebraMap D0 S0 x = φB (θ x))
    (I : Ideal C0) (fp : I → D0)
    (hfp : ∀ f : I, (algebraMap R0 D0 π0) ^ 2 * fp f = algebraMap C0 D0 (f : C0))
    (hθI : ∀ f : I, θ (algebraMap C0 D0 (f : C0)) = 0)
    (hθfp : ∀ f : I, θ (fp f) = 0)
    (hpow : ∀ x, θ x = 0 → ∃ ν : ℕ, (algebraMap R0 D0 π0) ^ ν * x ∈ I.map (algebraMap C0 D0))
    (r n : ℕ) (b : Module.Basis (Fin r ⊕ Fin n) C0 Ω[C0⁄R0])
    (b' : Module.Basis (Fin r ⊕ Fin n) D0 Ω[D0⁄R0])
    (hy : ∀ i, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inl i)) = b' (Sum.inl i))
    (hz : ∀ j, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inr j)) =
      algebraMap R0 D0 π0 • b' (Sum.inr j)) :
    let N := Submodule.span S0 (Set.range fun f : I => (1 : S0) ⊗ₜ[C0] D R0 C0 (f : C0))
    let Nfull := Submodule.span S0 (Set.range fun f : RingHom.ker θ => (1 : S0) ⊗ₜ[D0] D R0 D0 (f : D0))
    Module.length S0 (Submodule.torsion S0 ((S0 ⊗[D0] Ω[D0⁄R0]) ⧸ Nfull)) + 1 ≤
      max 1 (Module.length S0 (Submodule.torsion S0 ((S0 ⊗[C0] Ω[C0⁄R0]) ⧸ N))) := by
  classical
  let N := Submodule.span S0 (Set.range fun f : I => (1 : S0) ⊗ₜ[C0] D R0 C0 (f : C0))
  let Nfull := Submodule.span S0 (Set.range fun f : RingHom.ker θ => (1 : S0) ⊗ₜ[D0] D R0 D0 (f : D0))
  let Nsmall := Submodule.span S0 (Set.range fun f : I => (1 : S0) ⊗ₜ[D0] D R0 D0 (fp f))
  have hNle : Nsmall ≤ Nfull := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    exact Submodule.subset_span ⟨⟨fp f, RingHom.mem_ker.mpr (hθfp f)⟩, rfl⟩
  have ha2 : (algebraMap R0 D0 π0) ^ 2 = algebraMap R0 D0 (π0 ^ 2) := by rw [map_pow]
  have hIC : ∀ x ∈ I.map (algebraMap C0 D0), θ x = 0 ∧ ((1 : S0) ⊗ₜ[D0] D R0 D0 x) ∈ Nsmall :=
    derivative_image_mem_fixed (algebraMap C0 D0) θ φB hχ I
      (algebraMap R0 D0 π0) (π0 ^ 2) ha2 fp hfp hθI Nsmall
      (fun f => Submodule.subset_span ⟨f, rfl⟩)
  have htors : ∀ x ∈ Nfull, ∃ s : S0, s ≠ 0 ∧ s • x ∈ Nsmall :=
    derivative_kernel_saturation_fixed π0 θ φB hχ (I.map (algebraMap C0 D0))
      hpow (by rw [hπmap]; exact hπS.ne_zero) Nsmall (fun x hx => (hIC x hx).2)
  have hmono : Module.length S0 (Submodule.torsion S0 ((S0 ⊗[D0] Ω[D0⁄R0]) ⧸ Nfull)) ≤
      Module.length S0 (Submodule.torsion S0 ((S0 ⊗[D0] Ω[D0⁄R0]) ⧸ Nsmall)) :=
    length_torsion_quotient_mono_of_forall_exists_smul_mem Nsmall Nfull hNle htors
  let bF := Algebra.TensorProduct.basis S0 b
  let bF' := Algebra.TensorProduct.basis S0 b'
  let e0 : (Fin r ⊕ Fin n → S0) ≃ₗ[S0] ((Fin r → S0) × (Fin n → S0)) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin n) S0 S0
  let κ := bF.equivFun.trans e0
  let κ' := bF'.equivFun.trans e0
  let Dm := (LinearMap.id : (Fin r → S0) →ₗ[S0] (Fin r → S0)).prodMap
    (πS • (LinearMap.id : (Fin n → S0) →ₗ[S0] (Fin n → S0)))
  let Φ : (S0 ⊗[C0] Ω[C0⁄R0]) →ₗ[S0] (S0 ⊗[D0] Ω[D0⁄R0]) :=
    ((KaehlerDifferential.mapBaseChange R0 C0 D0).baseChange S0).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange C0 D0 S0 S0 Ω[C0⁄R0]).symm.toLinearMap
  have hΦ : ∀ m : Ω[C0⁄R0], Φ ((1 : S0) ⊗ₜ[C0] m) = (1 : S0) ⊗ₜ[D0] KaehlerDifferential.map R0 R0 C0 D0 m := by
    intro m
    change ((KaehlerDifferential.mapBaseChange R0 C0 D0).baseChange S0)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange C0 D0 S0 S0 Ω[C0⁄R0]).symm ((1 : S0) ⊗ₜ[C0] m)) = _
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      KaehlerDifferential.mapBaseChange_tmul]
    exact congrArg ((1 : S0) ⊗ₜ[D0] ·) (one_smul D0 ((KaehlerDifferential.map R0 R0 C0 D0) m))
  have hFy : ∀ i, Φ (bF (Sum.inl i)) = bF' (Sum.inl i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, hΦ, hy, (Algebra.TensorProduct.basis_apply b' _).symm]
  have hFz : ∀ j, Φ (bF (Sum.inr j)) = πS • bF' (Sum.inr j) := by
    intro j
    rw [Algebra.TensorProduct.basis_apply, hΦ, hz, one_tmul_smul_eq, hπmap,
      (Algebra.TensorProduct.basis_apply b' _).symm]
  have hKC : κ'.toLinearMap.comp Φ = Dm.comp κ.toLinearMap :=
    block_basis_comparison_fixed πS r n bF bF' Φ hFy hFz
  have hΦgen : ∀ f : I, Φ ((1 : S0) ⊗ₜ[C0] D R0 C0 (f : C0)) =
      (πS ^ 2) • ((1 : S0) ⊗ₜ[D0] D R0 D0 (fp f)) := by
    intro f
    rw [hΦ, KaehlerDifferential.map_D, ← hfp f, Derivation.leibniz, ha2, Derivation.map_algebraMap,
      smul_zero, add_zero, ← ha2, one_tmul_smul_eq, map_pow, hπmap]
  have hNΦ : N.map Φ = (Ideal.span {πS ^ 2} : Ideal S0) • Nsmall :=
    span_generator_image_fixed _ _ Φ (πS ^ 2) hΦgen
  exact dvr_diagonal_length_comparison_fixed πS hπS r n κ κ' Φ N Nsmall Nfull hmono hNΦ hKC

private theorem localization_point_units_fixed
    {A0 A1 S0 : Type u} [CommRing A0] [CommRing A1] [CommRing S0] [Algebra A0 A1]
    (g : A0) (φ : A0 →+* S0) (φ1 : A1 →+* S0)
    (hφ1 : ∀ a, φ1 (algebraMap A0 A1 a) = φ a) (hg : IsUnit (φ g)) :
    ∀ s : Algebra.algebraMapSubmonoid A1 (Submonoid.powers g), IsUnit (φ1 s) := by
  rintro ⟨_, ⟨s, ⟨k, rfl⟩, rfl⟩⟩
  change IsUnit (φ1 (algebraMap A0 A1 (g ^ k)))
  rw [hφ1, map_pow]
  exact hg.pow k

private theorem scalar_tower_triangle_fixed
    {R0 C0 D0 B0 : Type u} [CommRing R0] [CommRing C0] [CommRing D0] [CommRing B0]
    [Algebra R0 C0] [Algebra C0 D0] [Algebra R0 D0] [Algebra R0 B0] [Algebra C0 B0] [Algebra D0 B0]
    [IsScalarTower R0 C0 D0] [IsScalarTower C0 D0 B0] [IsScalarTower R0 C0 B0] :
    IsScalarTower R0 D0 B0 :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R0 C0 D0, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq C0 D0 B0, IsScalarTower.algebraMap_eq R0 C0 B0])

private theorem scalar_tower_compatible_map_fixed
    {R0 A0 A1 B0 : Type u} [CommRing R0] [CommRing A0] [CommRing A1] [CommRing B0]
    [Algebra R0 A0] [Algebra A0 A1] [Algebra R0 A1] [Algebra R0 B0] [Algebra A0 B0] [Algebra A1 B0]
    [IsScalarTower R0 A0 A1] [IsScalarTower R0 A0 B0]
    (hl : (algebraMap A1 B0).comp (algebraMap A0 A1) = algebraMap A0 B0) :
    IsScalarTower R0 A1 B0 :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R0 A0 A1, ← RingHom.comp_assoc, hl,
      ← IsScalarTower.algebraMap_eq R0 A0 B0])

private theorem defect_localization_point_fixed
    {R0 A0 T0 S0 : Type u} [CommRing R0] [CommRing A0] [CommRing T0]
    [CommRing S0] [IsLocalRing S0] [Algebra R0 A0] [Algebra R0 T0] [Algebra A0 T0]
    [IsScalarTower R0 A0 T0] [Algebra.FormallyEtale A0 T0]
    (φ : A0 →+* S0) (ψ : T0 →+* S0) (hψ : ∀ a, ψ (algebraMap A0 T0 a) = φ a) :
    smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R0 A0))) (Spec.map (CommRingCat.ofHom φ)) =
      (letI : Algebra T0 S0 := ψ.toAlgebra
       Module.length S0 (Submodule.torsion S0 (S0 ⊗[T0] Ω[T0⁄R0]))) := by
  letI : Algebra A0 S0 := φ.toAlgebra
  letI : Algebra T0 S0 := ψ.toAlgebra
  haveI : IsScalarTower A0 T0 S0 := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hψ a).symm)
  rw [smoothnessDefect_Spec_eq]
  exact (length_torsion_baseChange_kaehler_eq_of_formallyEtale R0 A0 T0 S0).symm

private theorem exists_square_ideal_lift_fixed
    {C0 D0 : Type u} [CommRing C0] [CommRing D0] (σ : C0 →+* D0)
    (I J : Ideal C0) (hIJ : I ≤ J ^ 2) (a : D0) (hJ : J.map σ = Ideal.span {a}) :
    ∀ f : I, ∃ f' : D0, a ^ 2 * f' = σ (f : C0) := by
  rintro ⟨f, hf⟩
  have h1 : σ f ∈ (J.map σ) ^ 2 := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hIJ hf)
  rw [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
  obtain ⟨f', hf'⟩ := h1
  exact ⟨f', by rw [mul_comm]; exact hf'⟩

private theorem point_algebra_triangle_fixed
    {C0 D0 Ag0 B0 S0 : Type u} [CommRing C0] [CommRing D0] [CommRing Ag0]
    [CommRing B0] [CommRing S0] [Algebra C0 D0] [Algebra C0 Ag0] [Algebra C0 B0]
    [Algebra Ag0 B0] [IsScalarTower C0 Ag0 B0]
    (θ : D0 →ₐ[C0] B0) (φg : Ag0 →+* S0) (φB : B0 →+* S0)
    (hφBAg : φB.comp (algebraMap Ag0 B0) = φg) :
    (φB.comp θ.toRingHom).comp (algebraMap C0 D0) = φg.comp (algebraMap C0 Ag0) := by
  ext c
  change φB (θ (algebraMap C0 D0 c)) = φg (algebraMap C0 Ag0 c)
  rw [θ.commutes, IsScalarTower.algebraMap_apply C0 Ag0 B0, ← RingHom.comp_apply, hφBAg]

private theorem coefficient_base_commutes_fixed
    {R0 A0 C0 Ag0 D0 S0 : Type u} [CommRing R0] [CommRing A0] [CommRing C0]
    [CommRing Ag0] [CommRing D0] [CommRing S0]
    [Algebra R0 A0] [Algebra R0 C0] [Algebra R0 Ag0] [Algebra A0 Ag0] [Algebra C0 Ag0]
    [IsScalarTower R0 A0 Ag0] [IsScalarTower R0 C0 Ag0]
    [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0] [Algebra D0 S0] [Algebra R0 S0]
    (φ : A0 →ₐ[R0] S0) (φg : Ag0 →+* S0) (hφg : ∀ a, φg (algebraMap A0 Ag0 a) = φ a)
    (hψ : ∀ c, algebraMap D0 S0 (algebraMap C0 D0 c) = φg (algebraMap C0 Ag0 c)) :
    ∀ r : R0, algebraMap D0 S0 (algebraMap R0 D0 r) = algebraMap R0 S0 r := by
  intro r
  rw [IsScalarTower.algebraMap_apply R0 C0 D0 r, hψ,
    ← IsScalarTower.algebraMap_apply R0 C0 Ag0, IsScalarTower.algebraMap_apply R0 A0 Ag0, hφg,
    AlgHom.commutes]

private theorem uniformizer_point_irreducible_fixed
    {R0 S0 : Type u} [CommRing R0] [IsLocalRing R0] [CommRing S0] [IsDomain S0]
    [IsDiscreteValuationRing S0] [Algebra R0 S0]
    (π0 : R0) (hπ0 : IsLocalRing.maximalIdeal R0 = Ideal.span {π0})
    (hmap : Ideal.map (algebraMap R0 S0) (IsLocalRing.maximalIdeal R0) = IsLocalRing.maximalIdeal S0) :
    Irreducible (algebraMap R0 S0 π0) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmap, hπ0, Ideal.map_span, Set.image_singleton]

private theorem localized_tensor_quotient_comparison_fixed
    {R0 C0 D0 Ag0 B0 S0 : Type u} [CommRing R0] [CommRing C0] [CommRing D0]
    [CommRing Ag0] [CommRing B0] [CommRing S0] [IsDomain S0] [IsDiscreteValuationRing S0]
    [Algebra R0 C0] [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0]
    [Algebra R0 Ag0] [Algebra C0 Ag0] [IsScalarTower R0 C0 Ag0]
    [Algebra R0 B0] [Algebra D0 B0] [IsScalarTower R0 D0 B0]
    [Algebra C0 S0] [Algebra D0 S0] [Algebra Ag0 S0] [Algebra B0 S0]
    [IsScalarTower C0 Ag0 S0] [IsScalarTower D0 B0 S0] [IsScalarTower C0 D0 S0]
    (hC : Function.Surjective (algebraMap C0 Ag0)) (hD : Function.Surjective (algebraMap D0 B0))
    (π0 : R0) (πS : S0) (hπS : Irreducible πS)
    (hπmap : algebraMap D0 S0 (algebraMap R0 D0 π0) = πS)
    (fp : RingHom.ker (algebraMap C0 Ag0) → D0)
    (hfp : ∀ f : RingHom.ker (algebraMap C0 Ag0),
      (algebraMap R0 D0 π0) ^ 2 * fp f = algebraMap C0 D0 (f : C0))
    (hθI : ∀ f : RingHom.ker (algebraMap C0 Ag0),
      algebraMap D0 B0 (algebraMap C0 D0 (f : C0)) = 0)
    (hθfp : ∀ f : RingHom.ker (algebraMap C0 Ag0), algebraMap D0 B0 (fp f) = 0)
    (hpow : ∀ x, algebraMap D0 B0 x = 0 → ∃ ν : ℕ, (algebraMap R0 D0 π0) ^ ν * x ∈
      (RingHom.ker (algebraMap C0 Ag0)).map (algebraMap C0 D0))
    (r n : ℕ) (b : Module.Basis (Fin r ⊕ Fin n) C0 Ω[C0⁄R0])
    (b' : Module.Basis (Fin r ⊕ Fin n) D0 Ω[D0⁄R0])
    (hy : ∀ i, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inl i)) = b' (Sum.inl i))
    (hz : ∀ j, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inr j)) = algebraMap R0 D0 π0 • b' (Sum.inr j)) :
    Module.length S0 (Submodule.torsion S0 (S0 ⊗[B0] Ω[B0⁄R0])) + 1 ≤
      max 1 (Module.length S0 (Submodule.torsion S0 (S0 ⊗[Ag0] Ω[Ag0⁄R0]))) := by
  obtain ⟨eF⟩ := KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
    (R := R0) (C := C0) (A := Ag0) (R' := S0) hC
  obtain ⟨eF'⟩ := KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
    (R := R0) (C := D0) (A := B0) (R' := S0) hD
  rw [smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' eF,
    smoothnessDefect_eq_length_torsion_global.length_torsion_eq_of_equiv' eF']
  exact tensor_kernel_diagonal_comparison_fixed π0 πS hπS hπmap (algebraMap D0 B0) (algebraMap B0 S0)
    (fun x => IsScalarTower.algebraMap_apply D0 B0 S0 x) (RingHom.ker (algebraMap C0 Ag0)) fp hfp
    hθI hθfp hpow r n b b' hy hz

private theorem charted_kernel_le_ideal_fixed
    {A0 C0 Ag0 : Type u} [CommRing A0] [CommRing C0] [CommRing Ag0]
    (τ : A0 →+* Ag0) (σ : C0 →+* Ag0) (J : Ideal A0) (JC : Ideal C0)
    (hJC : (J.map τ).comap σ = JC) : RingHom.ker σ ≤ JC := by
  rw [← hJC]
  intro c hc
  simp only [Ideal.mem_comap, RingHom.mem_ker] at hc ⊢
  rw [hc]
  exact Ideal.zero_mem _

private theorem charted_ideal_image_fixed
    {A0 C0 Ag0 : Type u} [CommRing A0] [CommRing C0] [CommRing Ag0]
    (τ : A0 →+* Ag0) (σ : C0 →+* Ag0) (hσ : Function.Surjective σ)
    (J : Ideal A0) (JC : Ideal C0) (hJC : (J.map τ).comap σ = JC) :
    JC.map σ = J.map τ := by
  rw [← hJC, Ideal.map_comap_of_surjective _ hσ]

private theorem charted_kernel_square_fixed
    {R0 A0 C0 Ag0 : Type u} [CommRing R0] [IsDomain R0] [IsDiscreteValuationRing R0]
    [CommRing A0] [CommRing C0] [CommRing Ag0]
    [Algebra R0 A0] [Algebra R0 C0] [Algebra R0 Ag0]
    (g : A0) [Algebra A0 Ag0] [IsLocalization.Away g Ag0] [Algebra C0 Ag0]
    [IsScalarTower R0 A0 Ag0] [IsScalarTower R0 C0 Ag0]
    (π0 : R0) (hπ0 : IsLocalRing.maximalIdeal R0 = Ideal.span {π0})
    (J : Ideal A0) (n : ℕ) (z : Fin n → C0)
    (hσ : Function.Surjective (algebraMap C0 Ag0))
    (hJC : (J.map (algebraMap A0 Ag0)).comap (algebraMap C0 Ag0) =
      Ideal.span (insert (algebraMap R0 C0 π0) (Set.range z)))
    (hlin : LinearIndependent (C0 ⧸ Ideal.span (insert (algebraMap R0 C0 π0) (Set.range z)))
      fun j : Fin n => (1 : C0 ⧸ Ideal.span (insert (algebraMap R0 C0 π0) (Set.range z))) ⊗ₜ[C0]
        D R0 Ag0 (algebraMap C0 Ag0 (z j)))
    (hN : ∀ a : A0,
      (∀ (S : Type u) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R0 S]
        [IsLocalHom (algebraMap R0 S)], IsIndexOneExtension R0 S →
        ∀ c : A0 →ₐ[R0] S, J ≤ (IsLocalRing.maximalIdeal S).comap c →
          a ∈ (IsLocalRing.maximalIdeal S).comap c) → a ∈ J) :
    RingHom.ker (algebraMap C0 Ag0) ≤ Ideal.span (insert (algebraMap R0 C0 π0) (Set.range z)) ^ 2 := by
  let JC : Ideal C0 := Ideal.span (insert (algebraMap R0 C0 π0) (Set.range z))
  have hNC := transported_detection_fixed (R0 := R0) (A0 := A0) (C0 := C0) (Ag0 := Ag0) g J JC hJC hN
  have hIJ := charted_kernel_le_ideal_fixed (algebraMap A0 Ag0) (algebraMap C0 Ag0) J JC hJC
  exact NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne π0 hπ0 hσ z hIJ hlin hNC

private theorem dilatation_kernel_presentation_fixed
    {R0 A0 C0 Ag0 : Type u} [CommRing R0] [CommRing A0] [CommRing C0] [CommRing Ag0]
    [Algebra R0 A0] [Algebra R0 C0] [Algebra R0 Ag0] [Algebra A0 Ag0] [Algebra C0 Ag0]
    [IsScalarTower R0 A0 Ag0] [IsScalarTower R0 C0 Ag0]
    (π0 : R0) (J : Ideal A0) (JC : Ideal C0)
    (hσ : Function.Surjective (algebraMap C0 Ag0))
    (hmap : JC.map (algebraMap C0 Ag0) = J.map (algebraMap A0 Ag0)) :
    ∃ θ : AffineDilatation.Ring JC (algebraMap R0 C0 π0) →ₐ[C0]
        AffineDilatation.Ring (J.map (algebraMap A0 Ag0)) (algebraMap A0 Ag0 (algebraMap R0 A0 π0)),
      Function.Surjective θ ∧ ∀ x, θ x = 0 ↔ ∃ ν : ℕ, (algebraMap R0 _ π0) ^ ν * x ∈
        (RingHom.ker (algebraMap C0 Ag0)).map (algebraMap C0 (AffineDilatation.Ring JC (algebraMap R0 C0 π0))) := by
  have h := AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective (R := R0) π0 (C := C0) (A := Ag0) hσ JC
  rw [hmap, IsScalarTower.algebraMap_apply R0 A0 Ag0 π0] at h
  exact h

private theorem smooth_chart_witness_fixed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R])) :
    ∃ (g : A) (_ : g ∉ 𝔭) (r n : ℕ) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.Smooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R]),
        (∀ i, b (Sum.inl i) = D R C (y i)) ∧ (∀ j, b (Sum.inr j) = D R C (z j)) ∧
        Ideal.comap (algebraMap C (Localization.Away g)) (J.map (algebraMap A (Localization.Away g))) =
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ∧
        LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
          fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
            D R (Localization.Away g) (algebraMap C (Localization.Away g) (z j)) :=
  Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span
    π hπ J hπJ 𝔭 𝔮 h𝔮 hsmooth hfree

private theorem kernel_image_zero_fixed
    {C0 D0 Ag0 B0 : Type u} [CommRing C0] [CommRing D0] [CommRing Ag0] [CommRing B0]
    [Algebra C0 D0] [Algebra C0 Ag0] [Algebra C0 B0] [Algebra Ag0 B0]
    [IsScalarTower C0 Ag0 B0] (θ : D0 →ₐ[C0] B0) :
    ∀ f : RingHom.ker (algebraMap C0 Ag0), θ (algebraMap C0 D0 (f : C0)) = 0 := by
  rintro ⟨f, hf⟩
  rw [θ.commutes, IsScalarTower.algebraMap_apply C0 Ag0 B0, RingHom.mem_ker.mp hf, map_zero]

private theorem basis_derivative_map_left_fixed
    {R0 C0 D0 : Type u} [CommRing R0] [CommRing C0] [CommRing D0]
    [Algebra R0 C0] [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0]
    {r n : ℕ} (y : Fin r → C0)
    (b : Module.Basis (Fin r ⊕ Fin n) C0 Ω[C0⁄R0])
    (b' : Module.Basis (Fin r ⊕ Fin n) D0 Ω[D0⁄R0])
    (hby : ∀ i, b (Sum.inl i) = D R0 C0 (y i))
    (hby' : ∀ i, b' (Sum.inl i) = D R0 D0 (algebraMap C0 D0 (y i))) :
    ∀ i, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inl i)) = b' (Sum.inl i) := by
  intro i
  rw [hby, KaehlerDifferential.map_D, hby']

private theorem basis_derivative_map_right_fixed
    {R0 C0 D0 : Type u} [CommRing R0] [CommRing C0] [CommRing D0]
    [Algebra R0 C0] [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0]
    (π0 : R0) {r n : ℕ} (z : Fin n → C0)
    (b : Module.Basis (Fin r ⊕ Fin n) C0 Ω[C0⁄R0])
    (b' : Module.Basis (Fin r ⊕ Fin n) D0 Ω[D0⁄R0])
    (hbz : ∀ j, b (Sum.inr j) = D R0 C0 (z j))
    (hbz' : ∀ j, algebraMap R0 D0 π0 • b' (Sum.inr j) = D R0 D0 (algebraMap C0 D0 (z j))) :
    ∀ j, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inr j)) =
      algebraMap R0 D0 π0 • b' (Sum.inr j) := by
  intro j
  rw [hbz, KaehlerDifferential.map_D, hbz']

private theorem away_point_component_fixed
    {A0 Ag0 S0 : Type u} [CommRing A0] [CommRing Ag0] [CommRing S0]
    (g : A0) [Algebra A0 Ag0] [IsLocalization.Away g Ag0]
    (φ : A0 →+* S0) (hg : IsUnit (φ g)) :
    ∀ a, (IsLocalization.Away.lift g (g := φ) hg : Ag0 →+* S0) (algebraMap A0 Ag0 a) = φ a :=
  fun a => IsLocalization.Away.lift_eq g hg a

private theorem extension_map_point_tower_fixed
    {A0 B0 S0 : Type u} [CommRing A0] [CommRing B0] [CommRing S0] [Algebra A0 B0]
    (f : A0 →+* S0) (g : B0 →+* S0) (hfg : ∀ a, g (algebraMap A0 B0 a) = f a) :
    letI : Algebra A0 S0 := f.toAlgebra;
    letI : Algebra B0 S0 := g.toAlgebra;
    IsScalarTower A0 B0 S0 := by
  letI : Algebra A0 S0 := f.toAlgebra
  letI : Algebra B0 S0 := g.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (hfg a).symm)

private theorem scalar_image_through_chart_fixed
    {R0 A0 C0 Ag0 D0 B0 : Type u} [CommRing R0] [CommRing A0] [CommRing C0]
    [CommRing Ag0] [CommRing D0] [CommRing B0]
    [Algebra R0 A0] [Algebra A0 Ag0] [Algebra R0 Ag0] [IsScalarTower R0 A0 Ag0]
    [Algebra R0 C0] [Algebra C0 D0] [Algebra R0 D0] [IsScalarTower R0 C0 D0]
    [Algebra C0 B0] [Algebra R0 B0] [IsScalarTower R0 C0 B0]
    [Algebra Ag0 B0] [IsScalarTower R0 Ag0 B0] (θ : D0 →ₐ[C0] B0) (π0 : R0) :
    θ (algebraMap R0 D0 π0) = algebraMap Ag0 B0 (algebraMap A0 Ag0 (algebraMap R0 A0 π0)) := by
  rw [IsScalarTower.algebraMap_apply R0 C0 D0 π0, θ.commutes,
    ← IsScalarTower.algebraMap_apply R0 C0 B0, IsScalarTower.algebraMap_apply R0 Ag0 B0,
    IsScalarTower.algebraMap_apply R0 A0 Ag0]

private theorem principal_image_base_scalar_fixed
    {R0 C0 D0 : Type u} [CommRing R0] [CommRing C0] [CommRing D0]
    [Algebra R0 C0] [Algebra C0 D0] [Algebra R0 D0] [IsScalarTower R0 C0 D0]
    (π0 : R0) (J : Ideal C0)
    (hJ : J.map (algebraMap C0 D0) = Ideal.span {algebraMap C0 D0 (algebraMap R0 C0 π0)}) :
    J.map (algebraMap C0 D0) = Ideal.span {algebraMap R0 D0 π0} := by
  rw [hJ, ← IsScalarTower.algebraMap_apply R0 C0 D0 π0]

private theorem localization_point_square_rows_fixed
    {A0 Ag0 A1 C0 D0 B0 S0 : Type u} [CommRing A0] [CommRing Ag0] [CommRing A1]
    [CommRing C0] [CommRing D0] [CommRing B0] [CommRing S0]
    (g : A0) [Algebra A0 Ag0] [IsLocalization.Away g Ag0]
    [Algebra A0 A1] [Algebra A0 B0] [Algebra Ag0 B0] [Algebra A1 B0]
    [IsScalarTower A0 Ag0 B0]
    [Algebra C0 D0] [Algebra C0 Ag0] [Algebra C0 B0] [IsScalarTower C0 Ag0 B0]
    (φ : A0 →+* S0) (φg : Ag0 →+* S0) (φ1 : A1 →+* S0) (φB : B0 →+* S0)
    (θ : D0 →ₐ[C0] B0)
    (hl : (algebraMap A1 B0).comp (algebraMap A0 A1) = algebraMap A0 B0)
    (hφg : ∀ a, φg (algebraMap A0 Ag0 a) = φ a)
    (hφ1 : ∀ a, φ1 (algebraMap A0 A1 a) = φ a)
    (hφB : ∀ a, φB (algebraMap A1 B0 a) = φ1 a) :
    (φB.comp (algebraMap Ag0 B0) = φg) ∧
      ((φB.comp θ.toRingHom).comp (algebraMap C0 D0) = φg.comp (algebraMap C0 Ag0)) ∧
      (letI : Algebra A0 S0 := φ.toAlgebra; letI : Algebra Ag0 S0 := φg.toAlgebra;
       IsScalarTower A0 Ag0 S0) ∧
      (letI : Algebra A1 S0 := φ1.toAlgebra; letI : Algebra B0 S0 := φB.toAlgebra;
       IsScalarTower A1 B0 S0) ∧
      (letI : Algebra C0 S0 := (φg.comp (algebraMap C0 Ag0)).toAlgebra;
       letI : Algebra D0 S0 := (φB.comp θ.toRingHom).toAlgebra;
       IsScalarTower C0 D0 S0) := by
  haveI : IsScalarTower A0 A1 B0 := IsScalarTower.of_algebraMap_eq' hl.symm
  have hAg := localization_point_compatibility_fixed g φ φg φ1 φB hφg hφ1 hφB
  have hCD := point_algebra_triangle_fixed θ φg φB hAg
  exact ⟨hAg, hCD, extension_map_point_tower_fixed φ φg hφg,
    extension_map_point_tower_fixed φ1 φB hφB,
    extension_map_point_tower_fixed (φg.comp (algebraMap C0 Ag0)) (φB.comp θ.toRingHom)
      (fun c => RingHom.congr_fun hCD c)⟩

private theorem kernel_lift_rows_fixed
    {R0 A0 C0 Ag0 D0 B0 : Type u} [CommRing R0] [CommRing A0] [CommRing C0]
    [CommRing Ag0] [CommRing D0] [CommRing B0]
    [Algebra R0 A0] [Algebra A0 Ag0] [Algebra R0 Ag0] [IsScalarTower R0 A0 Ag0]
    [Algebra R0 C0] [Algebra C0 D0] [Algebra R0 D0] [IsScalarTower R0 C0 D0]
    [Algebra C0 Ag0] [Algebra C0 B0] [Algebra R0 B0] [IsScalarTower R0 C0 B0]
    [Algebra Ag0 B0] [IsScalarTower C0 Ag0 B0] [IsScalarTower R0 Ag0 B0]
    (θ : D0 →ₐ[C0] B0) (π0 : R0)
    (hreg : IsSMulRegular B0 (algebraMap A0 Ag0 (algebraMap R0 A0 π0)))
    (fp : RingHom.ker (algebraMap C0 Ag0) → D0)
    (hfp : ∀ f : RingHom.ker (algebraMap C0 Ag0),
      (algebraMap R0 D0 π0) ^ 2 * fp f = algebraMap C0 D0 (f : C0)) :
    (∀ f : RingHom.ker (algebraMap C0 Ag0), θ (algebraMap C0 D0 (f : C0)) = 0) ∧
      (∀ f : RingHom.ker (algebraMap C0 Ag0), θ (fp f) = 0) := by
  have hzero := kernel_image_zero_fixed (C0 := C0) (D0 := D0) (Ag0 := Ag0) (B0 := B0) θ
  have hπB := scalar_image_through_chart_fixed
    (R0 := R0) (A0 := A0) (C0 := C0) (Ag0 := Ag0) (D0 := D0) (B0 := B0) θ π0
  exact ⟨hzero, regular_kernel_lift_zero_fixed (C0 := Ag0) θ.toRingHom
    (algebraMap R0 D0 π0) (algebraMap A0 Ag0 (algebraMap R0 A0 π0)) hπB hreg fp
    (fun f => algebraMap C0 D0 (f : C0)) hfp hzero⟩

private theorem point_base_uniformizer_rows_fixed
    {R0 A0 C0 Ag0 D0 S0 : Type u} [CommRing R0] [IsLocalRing R0]
    [CommRing A0] [CommRing C0] [CommRing Ag0] [CommRing D0] [CommRing S0]
    [IsDomain S0] [IsDiscreteValuationRing S0]
    [Algebra R0 A0] [Algebra R0 C0] [Algebra R0 Ag0] [Algebra A0 Ag0] [Algebra C0 Ag0]
    [IsScalarTower R0 A0 Ag0] [IsScalarTower R0 C0 Ag0]
    [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0] [Algebra D0 S0] [Algebra R0 S0]
    (φ : A0 →ₐ[R0] S0) (φg : Ag0 →+* S0) (hφg : ∀ a, φg (algebraMap A0 Ag0 a) = φ a)
    (hψ : ∀ c, algebraMap D0 S0 (algebraMap C0 D0 c) = φg (algebraMap C0 Ag0 c))
    (π0 : R0) (hπ0 : IsLocalRing.maximalIdeal R0 = Ideal.span {π0})
    (hmap : Ideal.map (algebraMap R0 S0) (IsLocalRing.maximalIdeal R0) = IsLocalRing.maximalIdeal S0) :
    (∀ r : R0, algebraMap D0 S0 (algebraMap R0 D0 r) = algebraMap R0 S0 r) ∧
      Irreducible (algebraMap R0 S0 π0) ∧
      algebraMap D0 S0 (algebraMap R0 D0 π0) = algebraMap R0 S0 π0 := by
  have hbase := coefficient_base_commutes_fixed
    (R0 := R0) (A0 := A0) (C0 := C0) (Ag0 := Ag0) (D0 := D0) (S0 := S0) φ φg hφg hψ
  exact ⟨hbase, uniformizer_point_irreducible_fixed π0 hπ0 hmap, hbase π0⟩

private theorem basis_map_rows_fixed
    {R0 C0 D0 : Type u} [CommRing R0] [CommRing C0] [CommRing D0]
    [Algebra R0 C0] [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0]
    (π0 : R0) {r n : ℕ} (y : Fin r → C0) (z : Fin n → C0)
    (b : Module.Basis (Fin r ⊕ Fin n) C0 Ω[C0⁄R0])
    (b' : Module.Basis (Fin r ⊕ Fin n) D0 Ω[D0⁄R0])
    (hby : ∀ i, b (Sum.inl i) = D R0 C0 (y i))
    (hbz : ∀ j, b (Sum.inr j) = D R0 C0 (z j))
    (hby' : ∀ i, b' (Sum.inl i) = D R0 D0 (algebraMap C0 D0 (y i)))
    (hbz' : ∀ j, algebraMap R0 D0 π0 • b' (Sum.inr j) = D R0 D0 (algebraMap C0 D0 (z j))) :
    (∀ i, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inl i)) = b' (Sum.inl i)) ∧
      (∀ j, KaehlerDifferential.map R0 R0 C0 D0 (b (Sum.inr j)) = algebraMap R0 D0 π0 • b' (Sum.inr j)) :=
  ⟨basis_derivative_map_left_fixed y b b' hby hby',
    basis_derivative_map_right_fixed π0 z b b' hbz hbz'⟩

private theorem scalar_regular_to_internal_mul_fixed
    {U0 B0 : Type u} [CommRing U0] [CommRing B0] [Algebra U0 B0]
    (c : U0) (hreg : IsSMulRegular B0 c) :
    Function.Injective (fun x : B0 => algebraMap U0 B0 c * x) := by
  intro x y hxy
  apply hreg
  simpa only [Algebra.smul_def] using hxy

private theorem chart_ring_square_fixed
    {C0 U0 D0 B0 : Type u} [CommRing C0] [CommRing U0] [CommRing D0] [CommRing B0]
    [Algebra C0 D0] [Algebra C0 U0] [Algebra C0 B0] [Algebra U0 B0]
    [IsScalarTower C0 U0 B0] (θ : D0 →ₐ[C0] B0) :
    θ.toRingHom.comp (algebraMap C0 D0) = (algebraMap U0 B0).comp (algebraMap C0 U0) :=
  RingHom.ext fun c => (θ.commutes c).trans (IsScalarTower.algebraMap_apply C0 U0 B0 c)

private theorem kernel_lift_ring_rows_fixed
    {C0 U0 D0 B0 : Type u} [CommRing C0] [CommRing U0] [CommRing D0] [CommRing B0]
    (σ : C0 →+* U0) (τ : U0 →+* B0) (ι : C0 →+* D0) (θ : D0 →+* B0)
    (a : D0) (b : B0) (hsquare : θ.comp ι = τ.comp σ) (hscalar : θ a = b)
    (hmul : Function.Injective (fun x : B0 => b * x))
    (fp : RingHom.ker σ → D0)
    (hfp : ∀ f : RingHom.ker σ, a ^ 2 * fp f = ι (f : C0)) :
    (∀ f : RingHom.ker σ, θ (ι (f : C0)) = 0) ∧
      (∀ f : RingHom.ker σ, θ (fp f) = 0) := by
  have hzero : ∀ f : RingHom.ker σ, θ (ι (f : C0)) = 0 := by
    intro f
    have h := RingHom.congr_fun hsquare (f : C0)
    simpa only [RingHom.comp_apply, RingHom.mem_ker.mp f.property, map_zero] using h
  refine ⟨hzero, ?_⟩
  intro f
  have h2 : b ^ 2 * θ (fp f) = 0 := by
    simpa only [map_mul, map_pow, hscalar, hzero f] using congrArg θ (hfp f)
  have hassoc : b * (b * θ (fp f)) = 0 := by
    simpa only [pow_two, mul_assoc] using h2
  have h1 : b * θ (fp f) = 0 := hmul (hassoc.trans (mul_zero b).symm)
  exact hmul (h1.trans (mul_zero b).symm)

private theorem kernel_lift_internal_ring_interface_fixed
    {R0 A0 C0 Ag0 D0 B0 : Type u} [CommRing R0] [CommRing A0] [CommRing C0]
    [CommRing Ag0] [CommRing D0] [CommRing B0]
    [Algebra R0 A0] [Algebra A0 Ag0] [Algebra R0 Ag0] [IsScalarTower R0 A0 Ag0]
    [Algebra R0 C0] [Algebra C0 D0] [Algebra R0 D0] [IsScalarTower R0 C0 D0]
    [Algebra C0 Ag0] [Algebra C0 B0] [Algebra R0 B0] [IsScalarTower R0 C0 B0]
    [Algebra Ag0 B0] [IsScalarTower C0 Ag0 B0] [IsScalarTower R0 Ag0 B0]
    (θ : D0 →ₐ[C0] B0) (π0 : R0)
    (hreg : IsSMulRegular B0 (algebraMap A0 Ag0 (algebraMap R0 A0 π0)))
    (fp : RingHom.ker (algebraMap C0 Ag0) → D0)
    (hfp : ∀ f : RingHom.ker (algebraMap C0 Ag0),
      (algebraMap R0 D0 π0) ^ 2 * fp f = algebraMap C0 D0 (f : C0)) :
    (∀ f : RingHom.ker (algebraMap C0 Ag0), θ (algebraMap C0 D0 (f : C0)) = 0) ∧
      (∀ f : RingHom.ker (algebraMap C0 Ag0), θ (fp f) = 0) := by
  have hsquare := chart_ring_square_fixed (C0 := C0) (U0 := Ag0) (D0 := D0) (B0 := B0) θ
  have hscalar := scalar_image_through_chart_fixed
    (R0 := R0) (A0 := A0) (C0 := C0) (Ag0 := Ag0) (D0 := D0) (B0 := B0) θ π0
  have hmul := scalar_regular_to_internal_mul_fixed
    (U0 := Ag0) (B0 := B0) (algebraMap A0 Ag0 (algebraMap R0 A0 π0)) hreg
  exact kernel_lift_ring_rows_fixed (algebraMap C0 Ag0) (algebraMap Ag0 B0)
    (algebraMap C0 D0) θ.toRingHom (algebraMap R0 D0 π0)
    (algebraMap Ag0 B0 (algebraMap A0 Ag0 (algebraMap R0 A0 π0))) hsquare hscalar hmul fp hfp

/-- The two point defects through the localizations `A → A_g` and `A′ → B`, both formally étale:
each equals the torsion length of the base-changed Kähler module of the localization. -/
private theorem point_defect_identities_fixed
    {R0 A0 Ag0 A1 B0 S0 : Type u} [CommRing R0] [CommRing A0] [CommRing Ag0] [CommRing A1]
    [CommRing B0] [CommRing S0] [IsLocalRing S0]
    [Algebra R0 A0] [Algebra R0 Ag0] [Algebra A0 Ag0] [IsScalarTower R0 A0 Ag0]
    (g : A0) [IsLocalization.Away g Ag0]
    [Algebra R0 A1] [Algebra A0 A1] [IsScalarTower R0 A0 A1]
    [Algebra R0 B0] [Algebra A0 B0] [IsScalarTower R0 A0 B0]
    (lam : A1 →ₐ[A0] B0)
    (hlam : @IsLocalization _ _ (Algebra.algebraMapSubmonoid A1 (Submonoid.powers g)) B0 _
      lam.toRingHom.toAlgebra)
    (φ : A0 →+* S0) (φg : Ag0 →+* S0) (hφg : ∀ a, φg (algebraMap A0 Ag0 a) = φ a)
    (φ1 : A1 →+* S0) (φB : B0 →+* S0)
    (hφB : letI : Algebra A1 B0 := lam.toRingHom.toAlgebra; ∀ a, φB (algebraMap A1 B0 a) = φ1 a) :
    smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R0 A0))) (Spec.map (CommRingCat.ofHom φ)) =
        (letI : Algebra Ag0 S0 := φg.toAlgebra
         Module.length S0 (Submodule.torsion S0 (S0 ⊗[Ag0] Ω[Ag0⁄R0]))) ∧
      smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R0 A1))) (Spec.map (CommRingCat.ofHom φ1)) =
        (letI : Algebra B0 S0 := φB.toAlgebra
         Module.length S0 (Submodule.torsion S0 (S0 ⊗[B0] Ω[B0⁄R0]))) := by
  letI iA1B : Algebra A1 B0 := lam.toRingHom.toAlgebra
  have hφB' : ∀ a, φB (algebraMap A1 B0 a) = φ1 a := hφB
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A1 (Submonoid.powers g)) B0 := hlam
  haveI : Algebra.FormallyEtale A1 B0 :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid A1 (Submonoid.powers g))
  haveI : IsScalarTower R0 A1 B0 := scalar_tower_compatible_map_fixed (R0 := R0) (A0 := A0) (A1 := A1)
    (B0 := B0) lam.comp_algebraMap
  haveI : Algebra.FormallyEtale A0 Ag0 := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g)
  exact ⟨defect_localization_point_fixed (R0 := R0) (A0 := A0) (T0 := Ag0) (S0 := S0) φ φg hφg,
    defect_localization_point_fixed (R0 := R0) (A0 := A1) (T0 := B0) (S0 := S0) φ1 φB hφB'⟩

/-- The charted torsion-length inequality: for the localized chart `C → A_g` and its dilatation
`C′ → B`, the torsion length over `B` plus one is at most `max 1` of the torsion length over `A_g`,
both base-changed along the point. -/
private theorem charted_torsion_length_fixed
    {R0 A0 C0 Ag0 A1 D0 B0 S0 : Type u} [CommRing R0] [IsLocalRing R0] [CommRing A0] [CommRing C0]
    [CommRing Ag0] [CommRing A1] [CommRing D0] [CommRing B0]
    [CommRing S0] [IsDomain S0] [IsDiscreteValuationRing S0]
    [Algebra R0 A0] [Algebra R0 C0] [Algebra R0 Ag0] [Algebra A0 Ag0] [Algebra C0 Ag0]
    [IsScalarTower R0 A0 Ag0] [IsScalarTower R0 C0 Ag0]
    (g : A0) [IsLocalization.Away g Ag0]
    [Algebra R0 A1] [Algebra A0 A1]
    [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0]
    [Algebra R0 B0] [Algebra A0 B0] [Algebra C0 B0] [Algebra Ag0 B0]
    [IsScalarTower R0 C0 B0] [IsScalarTower R0 Ag0 B0] [IsScalarTower A0 Ag0 B0] [IsScalarTower C0 Ag0 B0]
    [Algebra R0 S0]
    (φ : A0 →ₐ[R0] S0) (φg : Ag0 →+* S0) (hφg : ∀ a, φg (algebraMap A0 Ag0 a) = φ a)
    (φ' : A1 →ₐ[R0] S0) (hφ' : ∀ a, φ' (algebraMap A0 A1 a) = φ a)
    (lam : A1 →ₐ[A0] B0) (φB : B0 →+* S0)
    (hφB : letI : Algebra A1 B0 := lam.toRingHom.toAlgebra; ∀ a, φB (algebraMap A1 B0 a) = φ' a)
    (π0 : R0) (hπ0 : IsLocalRing.maximalIdeal R0 = Ideal.span {π0})
    (hmap : Ideal.map (algebraMap R0 S0) (IsLocalRing.maximalIdeal R0) = IsLocalRing.maximalIdeal S0)
    (θ : D0 →ₐ[C0] B0) (hθs : Function.Surjective θ)
    (hθk : ∀ x, θ x = 0 ↔ ∃ ν : ℕ, (algebraMap R0 D0 π0) ^ ν * x ∈
      (RingHom.ker (algebraMap C0 Ag0)).map (algebraMap C0 D0))
    (hσ : Function.Surjective (algebraMap C0 Ag0))
    (JC : Ideal C0) (hIJ2 : RingHom.ker (algebraMap C0 Ag0) ≤ JC ^ 2)
    (hJC' : JC.map (algebraMap C0 D0) = Ideal.span {algebraMap C0 D0 (algebraMap R0 C0 π0)})
    (hregB : IsSMulRegular B0 (algebraMap A0 Ag0 (algebraMap R0 A0 π0)))
    (r n : ℕ) (y : Fin r → C0) (z : Fin n → C0) (b : Module.Basis (Fin r ⊕ Fin n) C0 Ω[C0⁄R0])
    (b' : Module.Basis (Fin r ⊕ Fin n) D0 Ω[D0⁄R0])
    (hby : ∀ i, b (Sum.inl i) = D R0 C0 (y i)) (hbz : ∀ j, b (Sum.inr j) = D R0 C0 (z j))
    (hb'y : ∀ i, b' (Sum.inl i) = D R0 D0 (algebraMap C0 D0 (y i)))
    (hb'z : ∀ j, algebraMap R0 D0 π0 • b' (Sum.inr j) = D R0 D0 (algebraMap C0 D0 (z j))) :
    (letI : Algebra B0 S0 := φB.toAlgebra
     Module.length S0 (Submodule.torsion S0 (S0 ⊗[B0] Ω[B0⁄R0]))) + 1 ≤
      max 1 (letI : Algebra Ag0 S0 := φg.toAlgebra
        Module.length S0 (Submodule.torsion S0 (S0 ⊗[Ag0] Ω[Ag0⁄R0]))) := by
  classical
  letI iA1B : Algebra A1 B0 := lam.toRingHom.toAlgebra
  have hφB' : ∀ a, φB (algebraMap A1 B0 a) = φ' a := hφB
  obtain ⟨hφBAg, hψ_ring, hpointAg, hpointA1B, hpointCD⟩ := localization_point_square_rows_fixed
    (A0 := A0) (Ag0 := Ag0) (A1 := A1) (C0 := C0) (D0 := D0) (B0 := B0) (S0 := S0)
    g φ.toRingHom φg φ'.toRingHom φB θ lam.comp_algebraMap hφg hφ' hφB'

  letI iAgS : Algebra Ag0 S0 := φg.toAlgebra
  letI iAS : Algebra A0 S0 := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A0 Ag0 S0 := hpointAg
  letI iCS : Algebra C0 S0 := (φg.comp (algebraMap C0 Ag0)).toAlgebra
  haveI : IsScalarTower C0 Ag0 S0 := IsScalarTower.of_algebraMap_eq' rfl

  letI iDB : Algebra D0 B0 := θ.toRingHom.toAlgebra
  haveI : IsScalarTower C0 D0 B0 := IsScalarTower.of_algebraMap_eq' (θ.comp_algebraMap).symm
  haveI : IsScalarTower R0 D0 B0 := scalar_tower_triangle_fixed (R0 := R0) (C0 := C0) (D0 := D0) (B0 := B0)

  letI iBS : Algebra B0 S0 := φB.toAlgebra
  letI iA1S : Algebra A1 S0 := φ'.toRingHom.toAlgebra
  haveI : IsScalarTower A1 B0 S0 := hpointA1B
  letI iDS : Algebra D0 S0 := (φB.comp θ.toRingHom).toAlgebra
  haveI : IsScalarTower D0 B0 S0 := IsScalarTower.of_algebraMap_eq' rfl

  have hψ : ∀ c : C0, algebraMap D0 S0 (algebraMap C0 D0 c) = algebraMap C0 S0 c :=
    fun c => RingHom.congr_fun hψ_ring c

  set πD : D0 := algebraMap R0 D0 π0 with hπD
  have hex : ∀ f : RingHom.ker (algebraMap C0 Ag0), ∃ f' : D0, πD ^ 2 * f' = algebraMap C0 D0 (f : C0) := by
    exact exists_square_ideal_lift_fixed (algebraMap C0 D0) (RingHom.ker (algebraMap C0 Ag0)) JC hIJ2 πD
      (principal_image_base_scalar_fixed (R0 := R0) (C0 := C0) (D0 := D0) π0 JC hJC')
  choose fp hfp using hex
  obtain ⟨hθι, hθfp⟩ := kernel_lift_internal_ring_interface_fixed
    (R0 := R0) (A0 := A0) (C0 := C0) (Ag0 := Ag0) (D0 := D0) (B0 := B0) θ π0 hregB fp
    (fun f => by rw [← hπD]; exact hfp f)

  obtain ⟨hRD, hπSirr, hψπ⟩ := point_base_uniformizer_rows_fixed
    (R0 := R0) (A0 := A0) (C0 := C0) (Ag0 := Ag0) (D0 := D0) (S0 := S0)
    φ φg hφg hψ π0 hπ0 hmap
  set πS : S0 := algebraMap R0 S0 π0 with hπSdef
  haveI : IsScalarTower C0 D0 S0 := hpointCD
  obtain ⟨hmap_y, hmap_z⟩ := basis_map_rows_fixed π0 y z b b' hby hbz hb'y hb'z
  exact localized_tensor_quotient_comparison_fixed (R0 := R0) (C0 := C0) (D0 := D0) (Ag0 := Ag0)
    (B0 := B0) (S0 := S0) hσ hθs π0 πS hπSirr hψπ fp
    (fun f => by rw [← hπD]; exact hfp f) hθι hθfp (fun x hx => (hθk x).mp hx)
    r n b b' hmap_y hmap_z

/-- The defect inequality for the affine dilatation, transported from the two point-defect
identities and the charted torsion-length inequality. -/
private theorem charted_dilatation_defect_fixed
    {R0 A0 C0 Ag0 A1 D0 B0 S0 : Type u} [CommRing R0] [IsLocalRing R0] [CommRing A0] [CommRing C0]
    [CommRing Ag0] [CommRing A1] [CommRing D0] [CommRing B0]
    [CommRing S0] [IsDomain S0] [IsDiscreteValuationRing S0]
    [Algebra R0 A0] [Algebra R0 C0] [Algebra R0 Ag0] [Algebra A0 Ag0] [Algebra C0 Ag0]
    [IsScalarTower R0 A0 Ag0] [IsScalarTower R0 C0 Ag0]
    (g : A0) [IsLocalization.Away g Ag0]
    [Algebra R0 A1] [Algebra A0 A1] [IsScalarTower R0 A0 A1]
    [Algebra R0 D0] [Algebra C0 D0] [IsScalarTower R0 C0 D0]
    [Algebra R0 B0] [Algebra A0 B0] [Algebra C0 B0] [Algebra Ag0 B0]
    [IsScalarTower R0 A0 B0] [IsScalarTower R0 C0 B0] [IsScalarTower R0 Ag0 B0]
    [IsScalarTower A0 Ag0 B0] [IsScalarTower C0 Ag0 B0]
    [Algebra R0 S0]
    (φ : A0 →ₐ[R0] S0) (φg : Ag0 →+* S0) (hφg : ∀ a, φg (algebraMap A0 Ag0 a) = φ a)
    (φ' : A1 →ₐ[R0] S0) (hφ' : ∀ a, φ' (algebraMap A0 A1 a) = φ a)
    (lam : A1 →ₐ[A0] B0)
    (hlam : @IsLocalization _ _ (Algebra.algebraMapSubmonoid A1 (Submonoid.powers g)) B0 _
      lam.toRingHom.toAlgebra)
    (φB : B0 →+* S0)
    (hφB : letI : Algebra A1 B0 := lam.toRingHom.toAlgebra; ∀ a, φB (algebraMap A1 B0 a) = φ' a)
    (π0 : R0) (hπ0 : IsLocalRing.maximalIdeal R0 = Ideal.span {π0})
    (hmap : Ideal.map (algebraMap R0 S0) (IsLocalRing.maximalIdeal R0) = IsLocalRing.maximalIdeal S0)
    (θ : D0 →ₐ[C0] B0) (hθs : Function.Surjective θ)
    (hθk : ∀ x, θ x = 0 ↔ ∃ ν : ℕ, (algebraMap R0 D0 π0) ^ ν * x ∈
      (RingHom.ker (algebraMap C0 Ag0)).map (algebraMap C0 D0))
    (hσ : Function.Surjective (algebraMap C0 Ag0))
    (JC : Ideal C0) (hIJ2 : RingHom.ker (algebraMap C0 Ag0) ≤ JC ^ 2)
    (hJC' : JC.map (algebraMap C0 D0) = Ideal.span {algebraMap C0 D0 (algebraMap R0 C0 π0)})
    (hregB : IsSMulRegular B0 (algebraMap A0 Ag0 (algebraMap R0 A0 π0)))
    (r n : ℕ) (y : Fin r → C0) (z : Fin n → C0) (b : Module.Basis (Fin r ⊕ Fin n) C0 Ω[C0⁄R0])
    (b' : Module.Basis (Fin r ⊕ Fin n) D0 Ω[D0⁄R0])
    (hby : ∀ i, b (Sum.inl i) = D R0 C0 (y i)) (hbz : ∀ j, b (Sum.inr j) = D R0 C0 (z j))
    (hb'y : ∀ i, b' (Sum.inl i) = D R0 D0 (algebraMap C0 D0 (y i)))
    (hb'z : ∀ j, algebraMap R0 D0 π0 • b' (Sum.inr j) = D R0 D0 (algebraMap C0 D0 (z j))) :
    smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R0 A1)))
        (Spec.map (CommRingCat.ofHom φ'.toRingHom)) + 1 ≤
      max 1 (smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R0 A0)))
        (Spec.map (CommRingCat.ofHom φ.toRingHom))) := by
  obtain ⟨hδφ, hδφ'⟩ := point_defect_identities_fixed (R0 := R0) (A0 := A0) (Ag0 := Ag0) (A1 := A1)
    (B0 := B0) (S0 := S0) g lam hlam φ.toRingHom φg hφg φ'.toRingHom φB hφB
  rw [hδφ, hδφ']
  exact charted_torsion_length_fixed (R0 := R0) (A0 := A0) (C0 := C0) (Ag0 := Ag0) (A1 := A1) (D0 := D0)
    (B0 := B0) (S0 := S0) g φ φg hφg φ' hφ' lam φB hφB π0 hπ0 hmap θ hθs hθk hσ JC hIJ2 hJC' hregB
    r n y z b b' hby hbz hb'y hb'z

end NeronJacobiSkeleton

end



open NeronJacobiSkeleton in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J)]
    (hN : ∀ g : A,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : A →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (hR' : IsIndexOneExtension R R')
    (φ : A →ₐ[R] R') (hgen : PrimeSpectrum.comap φ.toRingHom (⊥ : PrimeSpectrum R') ∈ Algebra.smoothLocus R A)
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = (IsLocalRing.maximalIdeal R').comap φ)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈
      Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    (φ' : AffineDilatation.Ring J (algebraMap R A π) →ₐ[R] R')
    (hφ' : ∀ a : A, φ' (algebraMap A (AffineDilatation.Ring J (algebraMap R A π)) a) = φ a) :
    smoothnessDefect
        (Spec.map (CommRingCat.ofHom (algebraMap R (AffineDilatation.Ring J (algebraMap R A π)))))
        (Spec.map (CommRingCat.ofHom φ'.toRingHom)) + 1 ≤
      max 1 (smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φ.toRingHom)))  := by
  classical

  let 𝔭 : Ideal A := (IsLocalRing.maximalIdeal R').comap φ.toRingHom
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have h𝔮' : 𝔮.comap (Ideal.Quotient.mk J) = 𝔭 := h𝔮

  obtain ⟨g, hg, r, n, C, iC, iRC, iCAg, iT, hCsm, hθ, y, z, b, hby, hbz, hJC, hlin⟩ :=
    smooth_chart_witness_fixed π hπ J hπJ 𝔭 𝔮 h𝔮' hsmooth hfree
  letI := iC; letI := iRC; letI := iCAg; haveI := iT
  set Ag : Type u := Localization.Away g with hAg

  have hgunit : IsUnit (φ g) := IsLocalRing.notMem_maximalIdeal.mp hg
  let φg : Ag →+* R' := IsLocalization.Away.lift g (g := φ.toRingHom) hgunit
  have hφg : ∀ a : A, φg (algebraMap A Ag a) = φ a :=
    away_point_component_fixed (A0 := A) (Ag0 := Ag) (S0 := R') g φ.toRingHom hgunit

  set JC : Ideal C := Ideal.span (insert (algebraMap R C π) (Set.range z)) with hJCdef
  have hπJC : algebraMap R C π ∈ JC := Ideal.subset_span (Set.mem_insert _ _)

  have hIJ2 : RingHom.ker (algebraMap C Ag) ≤ JC ^ 2 :=
    charted_kernel_square_fixed (R0 := R) (A0 := A) (C0 := C) (Ag0 := Ag)
      g π hπ J n z hθ hJC hlin hN

  obtain ⟨b', hb'y, hb'z⟩ :=
    AffineDilatation.exists_basis_kaehlerDifferential_of_smooth_of_basis π hπ y z b hby hbz

  obtain ⟨θ', hθ's, hθ'k⟩ :=
    AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective (R := R) π (C := C) (A := Ag) hθ JC

  have hImap : JC.map (algebraMap C Ag) = J.map (algebraMap A Ag) := by
    exact charted_ideal_image_fixed (algebraMap A Ag) (algebraMap C Ag) hθ J JC hJC
  have hπeq : algebraMap R Ag π = algebraMap A Ag (algebraMap R A π) := IsScalarTower.algebraMap_apply R A Ag π
  have h5 := dilatation_kernel_presentation_fixed (R0 := R) (A0 := A) (C0 := C) (Ag0 := Ag) π J JC hθ hImap
  clear θ' hθ's hθ'k
  obtain ⟨θ', hθ's, hθ'k⟩ := h5
  obtain ⟨lam, hlam⟩ := AffineDilatation.exists_algHom_isLocalization_map J (algebraMap R A π) hπJ
    (Submonoid.powers g) Ag

  let A' : Type u := AffineDilatation.Ring J (algebraMap R A π)
  let B : Type u := AffineDilatation.Ring (J.map (algebraMap A Ag)) (algebraMap A Ag (algebraMap R A π))
  let C' : Type u := AffineDilatation.Ring JC (algebraMap R C π)

  letI iA'B : Algebra A' B := lam.toRingHom.toAlgebra
  haveI hlam' : IsLocalization (Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) B := hlam
  haveI : Algebra.FormallyEtale A' B := Algebra.FormallyEtale.of_isLocalization
    (Algebra.algebraMapSubmonoid A' (Submonoid.powers g))
  have hunits : ∀ s : Algebra.algebraMapSubmonoid A' (Submonoid.powers g), IsUnit (φ'.toRingHom s) := by
    exact localization_point_units_fixed g φ.toRingHom φ'.toRingHom hφ' hgunit
  let φB : B →+* R' := IsLocalization.lift (M := Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) hunits
  have hφB : ∀ a' : A', φB (algebraMap A' B a') = φ' a' :=
    fun a' => IsLocalization.lift_eq (M := Algebra.algebraMapSubmonoid A' (Submonoid.powers g)) hunits a'
  obtain ⟨hregC', hJC'⟩ := AffineDilatation.isSMulRegular_and_map_eq_span_singleton JC (algebraMap R C π) hπJC
  have hπJ' : algebraMap A Ag (algebraMap R A π) ∈ J.map (algebraMap A Ag) := Ideal.mem_map_of_mem _ hπJ
  obtain ⟨hregB, -⟩ := AffineDilatation.isSMulRegular_and_map_eq_span_singleton (J.map (algebraMap A Ag))
    (algebraMap A Ag (algebraMap R A π)) hπJ'
  exact charted_dilatation_defect_fixed (R0 := R) (A0 := A) (C0 := C) (Ag0 := Ag) (A1 := A') (D0 := C')
    (B0 := B) (S0 := R') g φ φg hφg φ' hφ' lam hlam φB hφB π hπ hR'.map_maximalIdeal θ' hθ's hθ'k hθ
    JC hIJ2 hJC' hregB r n y z b b' hby hbz hb'y hb'z


end P2MW.S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
