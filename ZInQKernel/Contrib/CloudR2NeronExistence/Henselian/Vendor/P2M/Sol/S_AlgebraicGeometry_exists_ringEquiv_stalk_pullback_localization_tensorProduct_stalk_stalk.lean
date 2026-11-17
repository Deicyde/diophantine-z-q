import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.lean
Original Git blob: 4c95dcd1e354b36c580fd5ec11fe1271fa98063d
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct

namespace FibreStalkBCRight
h77_bridge_namespace

variable {A S R L : Type*} [CommRing A] [CommRing S] [CommRing R] [CommRing L]
  [Algebra A S] [Algebra A R] [Algebra A L] [Algebra R L] [IsScalarTower A R L]

@[reducible] noncomputable def tensorAlgebra : Algebra (S ⊗[A] R) (S ⊗[A] L) :=
  (Algebra.TensorProduct.map (AlgHom.id A S) (IsScalarTower.toAlgHom A R L)).toRingHom.toAlgebra

attribute [local instance] tensorAlgebra

theorem algebraMap_tensor_tmul (s : S) (r : R) :
    algebraMap (S ⊗[A] R) (S ⊗[A] L) (s ⊗ₜ r) = s ⊗ₜ algebraMap R L r := rfl

theorem isScalarTower_tensor : IsScalarTower S (S ⊗[A] R) (S ⊗[A] L) :=
  IsScalarTower.of_algebraMap_eq (R := S) (S := S ⊗[A] R) (A := S ⊗[A] L) fun s => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, algebraMap_tensor_tmul, map_one]

theorem isLocalization_tensor (M : Submonoid R) [IsLocalization M L] :
    IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R))) (S ⊗[A] L) := by
  haveI := isScalarTower_tensor (A := A) (S := S) (R := R) (L := L)
  refine IsLocalization.tensorProduct_tensorProduct_right A S M L ?_
  ext r
  rfl

theorem core (𝔭 : Ideal R) [𝔭.IsPrime] [IsLocalization.AtPrime L 𝔭]
    (𝔔 : Ideal (S ⊗[A] R)) [h𝔔 : 𝔔.IsPrime]
    (hQp : 𝔔.comap (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R)).toRingHom = 𝔭)
    (Tq : Type*) [CommRing Tq] [Algebra (S ⊗[A] R) Tq] [IsLocalization.AtPrime Tq 𝔔]
    (φ : L →+* Tq) (hφ : ∀ r : R, φ (algebraMap R L r) = algebraMap (S ⊗[A] R) Tq (1 ⊗ₜ r)) :
    ∃ (𝔮 : Ideal (S ⊗[A] L)) (_ : 𝔮.IsPrime) (e : Tq ≃+* Localization.AtPrime 𝔮),
      (∀ s : S, e (algebraMap (S ⊗[A] R) Tq (s ⊗ₜ[A] (1 : R))) =
        algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ l : L, e (φ l) = algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) ((1 : S) ⊗ₜ[A] l)) := by
  haveI := isScalarTower_tensor (A := A) (S := S) (R := R) (L := L)
  set T := S ⊗[A] R
  set M : Submonoid T := 𝔭.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := R)) with hM
  haveI hloc : IsLocalization M (S ⊗[A] L) := isLocalization_tensor 𝔭.primeCompl

  have hdisj : Disjoint (M : Set T) (𝔔 : Set T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    apply hr
    rw [← hQp]
    exact hrQ

  let 𝔮 : Ideal (S ⊗[A] L) := 𝔔.map (algebraMap T (S ⊗[A] L))
  haveI h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (S ⊗[A] L) 𝔔 h𝔔 hdisj
  have hunder : 𝔮.comap (algebraMap T (S ⊗[A] L)) = 𝔔 :=
    IsLocalization.under_map_of_isPrime_disjoint M (S ⊗[A] L) h𝔔 hdisj

  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) (𝔮.comap (algebraMap T (S ⊗[A] L))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔮) 𝔮
  have hN : 𝔔.primeCompl = (Ideal.comap (algebraMap T (S ⊗[A] L)) 𝔮).primeCompl := by
    ext x
    change x ∉ 𝔔 ↔ x ∉ Ideal.comap (algebraMap T (S ⊗[A] L)) 𝔮
    rw [hunder]
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) 𝔔 := by
    change IsLocalization 𝔔.primeCompl (Localization.AtPrime 𝔮)
    rw [hN]
    exact this
  let e : Tq ≃ₐ[T] Localization.AtPrime 𝔮 := IsLocalization.algEquiv 𝔔.primeCompl Tq (Localization.AtPrime 𝔮)
  refine ⟨𝔮, h𝔮, e.toRingEquiv, ?_, ?_⟩
  ·
    intro s
    change e (algebraMap T Tq (s ⊗ₜ[A] (1 : R))) = _
    rw [e.commutes (s ⊗ₜ[A] (1 : R)), IsScalarTower.algebraMap_apply T (S ⊗[A] L) (Localization.AtPrime 𝔮),
      algebraMap_tensor_tmul, map_one]
  ·
    intro l
    suffices h : (e.toRingEquiv.toRingHom.comp φ) =
        (algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮)).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := L)).toRingHom by
      exact congrArg (fun f : L →+* Localization.AtPrime 𝔮 => f l) h
    refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
    ext r
    change e (φ (algebraMap R L r)) = algebraMap (S ⊗[A] L) (Localization.AtPrime 𝔮) ((1 : S) ⊗ₜ[A] algebraMap R L r)
    rw [hφ, ← algebraMap_tensor_tmul, ← IsScalarTower.algebraMap_apply]
    exact e.commutes ((1 : S) ⊗ₜ r)

end FibreStalkBCRight

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace StalkPB
h77_bridge_namespace

variable {R : Type u} [CommRing R] {X Z : Scheme.{u}}
  (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) (U : Z.Opens) (hU : IsAffineOpen U)

@[reducible] def algU : Algebra R Γ(Z, U) :=
  ((z.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra

lemma isoSpec_hom_algU : letI := algU z U
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U))) = U.ι ≫ z := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec z (isAffineOpen_top _) hU (le_top : U ≤ z ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← IsAffineOpen.isoSpec_inv_ι] at h
  change hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ z.appLE ⊤ U le_top).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_comp, h, Category.assoc, Iso.hom_inv_id_assoc]

omit U hU in
lemma algebraMap_stalk_eq {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) (y : Y) [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) (r : R) :
    algebraMap R (Y.presheaf.stalk y) r =
      Y.presheaf.germ ⊤ y trivial (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) := by
  have h1 : Y.fromSpecStalk y ≫ g ≫ (Spec (CommRingCat.of R)).toSpecΓ =
      Spec.map (g.appTop ≫ Y.presheaf.germ ⊤ y trivial) := by
    rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
  rw [← Category.assoc, halg, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Spec.map_inj] at h1

  have h2 := congrArg (fun φ : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Y.presheaf.stalk y =>
    φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  erw [Iso.inv_hom_id_apply] at h2
  exact h2

omit U hU in
lemma fe_wrapper (k : Type u) [CommRing k] [Algebra R k] (g : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap R k)))
    (x : ↥(pullback f g))
    [inst : Algebra R (X.presheaf.stalk ((pullback.fst f g).base x))]
    (hinst : inst = ((X.presheaf.germ ⊤ ((pullback.fst f g).base x) trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra) :
    ∃ (𝔮 : Ideal ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k)) (_ : 𝔮.IsPrime)
      (e : (pullback f g).presheaf.stalk x ≃+* Localization.AtPrime 𝔮),
      (∀ s : X.presheaf.stalk ((pullback.fst f g).base x),
        e (((pullback.fst f g).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[R] 1)) ∧
      (∀ c : k,
        e ((pullback f g).presheaf.germ ⊤ x trivial ((pullback.snd f g).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
          algebraMap ((X.presheaf.stalk ((pullback.fst f g).base x)) ⊗[R] k) (Localization.AtPrime 𝔮) (1 ⊗ₜ[R] c)) := by
  subst hg hinst
  obtain ⟨𝔮, h𝔮, e, -, h1, h2⟩ :=
    AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd X f k x
  exact ⟨𝔮, h𝔮, e, h1, h2⟩

variable [Algebra R Γ(Z, U)]
  (hφU : hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U))) = U.ι ≫ z)

include hφU

def φ : Spec Γ(Z, U) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, U)))

lemma fromSpec_φ : (hU.isoSpec.inv ≫ U.ι) ≫ z = φ (R := R) U := by
  rw [Category.assoc, ← hφU, Iso.inv_hom_id_assoc]; rfl

def jmap : pullback (φ (R := R) U) f ⟶ pullback z f :=
  pullback.map (φ (R := R) U) f z f (hU.isoSpec.inv ≫ U.ι) (𝟙 X) (𝟙 _)
    (by rw [Category.comp_id, fromSpec_φ z U hU hφU]) (by simp)

def j : pullback f (φ (R := R) U) ⟶ pullback z f := (pullbackSymmetry f (φ (R := R) U)).hom ≫ jmap z f U hU hφU

scoped instance : IsOpenImmersion (jmap z f U hU hφU) := by unfold jmap; infer_instance
scoped instance : IsOpenImmersion (j z f U hU hφU) := by unfold j; infer_instance

lemma j_fst : j z f U hU hφU ≫ pullback.fst z f = pullback.snd f (φ (R := R) U) ≫ hU.isoSpec.inv ≫ U.ι := by
  simp only [j, jmap, pullback.map, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]

lemma j_snd : j z f U hU hφU ≫ pullback.snd z f = pullback.fst f (φ (R := R) U) := by
  simp only [j, jmap, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [pullbackSymmetry_hom_comp_snd]

lemma exists_j_eq (p : ↥(pullback z f)) (hpU : (pullback.fst z f).base p ∈ U) :
    ∃ q, (j z f U hU hφU).base q = p := by
  have : p ∈ Set.range (jmap z f U hU hφU).base := by
    unfold jmap
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · change (pullback.fst z f).base p ∈ Set.range (hU.isoSpec.inv ≫ U.ι).base
      rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.range_fromSpec]
      exact hpU
    · change (pullback.snd z f).base p ∈ Set.range (𝟙 X : X ⟶ X).base
      simp
  obtain ⟨q', hq'⟩ := this
  refine ⟨(pullbackSymmetry f (φ (R := R) U)).inv.base q', ?_⟩
  unfold j
  change ((pullbackSymmetry f (φ (R := R) U)).inv ≫ (pullbackSymmetry f (φ (R := R) U)).hom ≫ jmap z f U hU hφU).base q' = p
  rw [Iso.inv_hom_id_assoc]
  exact hq'

/-
DEFAULT-LIMIT SIBLING RE-PROOF (2026-11-17).
The original affine chart and imported germ-snd theorem are retained. Heavy
stalk calculations use atomic schemes/maps and fixed rings in separate
commands. The original R-algebras are preserved by their actual halg rows;
no new cast, alias, field, model, localization or coherence premise is added.
-/
section DefaultProofBlocks
omit hφU

private theorem canonical_stalk_scalar_row
    {X0 : Scheme.{u}} (f0 : X0 ⟶ Spec (CommRingCat.of R)) (x0 x1 : X0)
    (hxx : x0 = x1) [Algebra R (X0.presheaf.stalk x0)]
    (halg : X0.fromSpecStalk x0 ≫ f0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (X0.presheaf.stalk x0)))) :
    letI : Algebra R (X0.presheaf.stalk x1) :=
      ((X0.presheaf.germ ⊤ x1 trivial).hom.comp
        (f0.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∀ r : R, (X0.presheaf.stalkCongr (.of_eq hxx)).hom
      (algebraMap R (X0.presheaf.stalk x0) r) =
        algebraMap R (X0.presheaf.stalk x1) r := by
  letI : Algebra R (X0.presheaf.stalk x1) :=
    ((X0.presheaf.germ ⊤ x1 trivial).hom.comp
      (f0.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  intro r
  rw [algebraMap_stalk_eq f0 x0 halg r]
  change (X0.presheaf.germ ⊤ x0 trivial ≫
    X0.presheaf.stalkSpecializes (specializes_of_eq hxx.symm))
      (f0.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  rfl
private theorem chart_stalk_naturality
    (Y V X0 : Scheme.{u}) (j0 : V ⟶ Y) (τ : Y ⟶ X0) (π : V ⟶ X0)
    (hτ : j0 ≫ τ = π) (q : V) :
    ∀ t : X0.presheaf.stalk (τ.base (j0.base q)),
      j0.stalkMap q ((τ.stalkMap (j0.base q)).hom t) =
        (π.stalkMap q).hom ((X0.presheaf.stalkCongr (.of_eq
          (congrArg (fun m : V ⟶ X0 => m.base q) hτ))).hom t) := by
  intro t
  have h := Scheme.Hom.stalkMap_congr_hom (j0 ≫ τ) π hτ q
  rw [Scheme.Hom.stalkMap_comp] at h
  exact CategoryTheory.ConcreteCategory.congr_hom h t

private theorem affine_chart_germ
    (Z0 Y V : Scheme.{u}) (U0 : Z0.Opens) (hU0 : IsAffineOpen U0)
    (ρ : Y ⟶ Z0) (σ : V ⟶ Spec Γ(Z0, U0)) (j0 : V ⟶ Y) (q : V)
    (hpU : ρ.base (j0.base q) ∈ U0)
    (hρ : j0 ≫ ρ = σ ≫ hU0.fromSpec) :
    ∀ a : Γ(Z0, U0), (j0.stalkMap q).hom
      ((ρ.stalkMap (j0.base q)).hom ((Z0.presheaf.germ U0 _ hpU).hom a)) =
        V.presheaf.germ ⊤ q trivial
          (σ.appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z0, U0))).inv a)) := by
  intro a
  have E2 : j0.stalkMap q (Y.presheaf.germ (ρ ⁻¹ᵁ U0)
      (j0.base q) hpU (ρ.app U0 a)) =
      V.presheaf.germ ⊤ q trivial
        (σ.appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z0, U0))).inv a)) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    have t := CategoryTheory.ConcreteCategory.congr_hom (Scheme.Hom.congr_app hρ U0) a
    rw [Scheme.Hom.comp_app] at t
    erw [CommRingCat.comp_apply, CommRingCat.comp_apply] at t
    erw [t, TopCat.Presheaf.germ_res_apply]
    rw [Scheme.Hom.comp_app, IsAffineOpen.fromSpec_app_self]
    erw [CommRingCat.comp_apply, CommRingCat.comp_apply]
    have n := CategoryTheory.ConcreteCategory.congr_hom
      (σ.naturality (eqToHom hU0.fromSpec_preimage_self).op)
      ((Scheme.ΓSpecIso Γ(Z0, U0)).inv a)
    erw [CommRingCat.comp_apply, CommRingCat.comp_apply] at n
    erw [n, TopCat.Presheaf.germ_res_apply]
    rfl
  have g1 := CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.germ_stalkMap ρ U0 (j0.base q) hpU) a
  exact (congrArg (fun y => (j0.stalkMap q).hom y) g1).trans E2

private theorem affine_germ_scalar_tower
    {Z0 : Scheme.{u}} (z0 : Z0 ⟶ Spec (CommRingCat.of R))
    (U0 : Z0.Opens) (ζ : Z0) (hζ : ζ ∈ U0)
    [Algebra R Γ(Z0, U0)] [Algebra R (Z0.presheaf.stalk ζ)]
    (halgZ : Z0.fromSpecStalk ζ ≫ z0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z0.presheaf.stalk ζ))))
    (halgU : ∀ r : R, algebraMap R Γ(Z0, U0) r =
      (z0.appLE ⊤ U0 le_top) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) :
    letI : Algebra Γ(Z0, U0) (Z0.presheaf.stalk ζ) :=
      (Z0.presheaf.germ U0 ζ hζ).hom.toAlgebra
    IsScalarTower R Γ(Z0, U0) (Z0.presheaf.stalk ζ) := by
  letI : Algebra Γ(Z0, U0) (Z0.presheaf.stalk ζ) :=
    (Z0.presheaf.germ U0 ζ hζ).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [algebraMap_stalk_eq z0 ζ halgZ r, halgU r]
  change _ = Z0.presheaf.germ U0 ζ hζ
    ((z0.app ⊤ ≫ Z0.presheaf.map (homOfLE le_top).op)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
  rw [CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

private theorem composed_units_iff
    {L0 V0 W0 Q0 : Type u} [CommRing L0] [CommRing V0] [CommRing W0] [CommRing Q0]
    [IsLocalRing L0] [IsLocalRing V0] [IsLocalRing W0]
    (a : L0 →+* V0) [IsLocalHom a] (b : V0 →+* W0) [IsLocalHom b]
    (e : W0 ≃+* Q0) :
    ∀ l : L0, IsUnit (e (b (a l))) ↔ IsUnit l := by
  intro l
  have he : ∀ w : W0, IsUnit (e w) ↔ IsUnit w := fun w =>
    ⟨fun h => by simpa using h.map e.symm, fun h => h.map e⟩
  exact (he _).trans ((isUnit_map_iff b _).trans (isUnit_map_iff a l))

private theorem right_prime_comap
    {A0 B0 S0 L0 : Type u} [CommRing A0] [CommRing B0] [CommRing S0] [CommRing L0]
    [Algebra A0 B0] [Algebra A0 S0] [Algebra A0 L0] [Algebra B0 L0]
    [IsScalarTower A0 B0 L0] (P : Ideal B0) [P.IsPrime] [IsLocalization.AtPrime L0 P]
    (Q : Ideal (S0 ⊗[A0] B0)) [Q.IsPrime] (φL : L0 →+* Localization.AtPrime Q)
    (hφL : ∀ a : B0, φL (algebraMap B0 L0 a) =
      algebraMap (S0 ⊗[A0] B0) (Localization.AtPrime Q) ((1 : S0) ⊗ₜ[A0] a))
    (hUnits : ∀ l : L0, IsUnit (φL l) ↔ IsUnit l) :
    Q.comap (Algebra.TensorProduct.includeRight
      (R := A0) (A := S0) (B := B0)).toRingHom = P := by
  ext a
  rw [Ideal.mem_comap]
  change ((1 : S0) ⊗ₜ[A0] a ∈ Q) ↔ a ∈ P
  have h1 : ((1 : S0) ⊗ₜ[A0] a ∈ Q) ↔
      ¬ IsUnit (algebraMap (S0 ⊗[A0] B0) (Localization.AtPrime Q) ((1 : S0) ⊗ₜ[A0] a)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q]
    exact not_not.symm
  have h2 : a ∈ P ↔ ¬ IsUnit (algebraMap B0 L0 a) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff L0 P]
    exact not_not.symm
  rw [h1, h2, ← hφL a, not_iff_not]
  exact hUnits _

private theorem exists_tensor_flip
    {A0 L0 T0 S0 : Type u} [CommRing A0] [CommRing L0] [CommRing T0] [CommRing S0]
    [Algebra A0 L0] [Algebra A0 T0] [Algebra A0 S0] (cA : T0 ≃ₐ[A0] S0) :
    ∃ ψ : (L0 ⊗[A0] T0) ≃ₐ[A0] (S0 ⊗[A0] L0),
      ∀ l t, ψ (l ⊗ₜ[A0] t) = cA t ⊗ₜ[A0] l := by
  refine ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : L0 ≃ₐ[A0] L0) cA).trans
    (Algebra.TensorProduct.comm A0 L0 S0), ?_⟩
  intro l t
  simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.comm_tmul]

private theorem exists_prime_localization_equiv
    {B0 C0 : Type u} [CommRing B0] [CommRing C0]
    (ψ : B0 ≃+* C0) (Q : Ideal C0) [Q.IsPrime] :
    ∃ (P : Ideal B0) (_ : P.IsPrime)
      (ℓ : Localization.AtPrime P ≃+* Localization.AtPrime Q),
      ∀ w : B0, ℓ (algebraMap B0 (Localization.AtPrime P) w) =
        algebraMap C0 (Localization.AtPrime Q) (ψ w) := by
  let P : Ideal B0 := Q.comap ψ.toRingHom
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have H : P.primeCompl.map ψ.toMonoidHom = Q.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩
      change ψ (ψ.symm y) ∉ Q
      rw [ψ.apply_symm_apply]
      exact hy
  exact ⟨P, inferInstance,
    IsLocalization.ringEquivOfRingEquiv (M := P.primeCompl) (T := Q.primeCompl)
      (Localization.AtPrime P) (Localization.AtPrime Q) ψ H,
    fun w => IsLocalization.ringEquivOfRingEquiv_eq H w⟩

private theorem assemble_two_stalk_maps
    {A0 L0 T0 S0 B0 V0 W0 : Type u}
    [CommRing A0] [CommRing L0] [CommRing T0] [CommRing S0] [CommRing B0]
    [CommRing V0] [CommRing W0]
    [Algebra A0 L0] [Algebra A0 T0] [Algebra A0 S0] [Algebra A0 B0]
    (cA : T0 ≃ₐ[A0] S0) (J : V0 ≃+* W0)
    (Q0 : Ideal (S0 ⊗[A0] B0)) [Q0.IsPrime]
    (Q1 : Ideal (S0 ⊗[A0] L0)) [Q1.IsPrime]
    (e0 : W0 ≃+* Localization.AtPrime Q0)
    (e1 : Localization.AtPrime Q0 ≃+* Localization.AtPrime Q1)
    (a : L0 →+* V0) (b : T0 →+* V0)
    (hL : ∀ l : L0, e1 (e0 (J (a l))) =
      algebraMap (S0 ⊗[A0] L0) (Localization.AtPrime Q1) ((1 : S0) ⊗ₜ[A0] l))
    (hT : ∀ t : T0, e1 (e0 (J (b t))) =
      algebraMap (S0 ⊗[A0] L0) (Localization.AtPrime Q1) (cA t ⊗ₜ[A0] (1 : L0))) :
    ∃ (P : Ideal (L0 ⊗[A0] T0)) (_ : P.IsPrime)
      (e : V0 ≃+* Localization.AtPrime P),
      (∀ l : L0, e (a l) =
        algebraMap (L0 ⊗[A0] T0) (Localization.AtPrime P) (l ⊗ₜ[A0] (1 : T0))) ∧
      (∀ t : T0, e (b t) =
        algebraMap (L0 ⊗[A0] T0) (Localization.AtPrime P) ((1 : L0) ⊗ₜ[A0] t)) := by
  obtain ⟨ψ, hψ⟩ := exists_tensor_flip (A0 := A0) (L0 := L0) (T0 := T0) (S0 := S0) cA
  obtain ⟨P, hP, ℓ, hℓ⟩ := exists_prime_localization_equiv ψ.toRingEquiv Q1
  have hψR : ∀ (l : L0) (t : T0), ψ.toRingEquiv (l ⊗ₜ[A0] t) = cA t ⊗ₜ[A0] l := fun l t => hψ l t
  refine ⟨P, hP, ((J.trans e0).trans e1).trans ℓ.symm, ?_, ?_⟩
  · intro l
    change ℓ.symm (e1 (e0 (J (a l)))) = _
    rw [RingEquiv.symm_apply_eq, hL l, hℓ, hψR, map_one]
  · intro t
    change ℓ.symm (e1 (e0 (J (b t)))) = _
    rw [RingEquiv.symm_apply_eq, hT t, hℓ, hψR]
private theorem atomic_chart_comparison
    {X0 Z0 : Scheme.{u}} (f0 : X0 ⟶ Spec (CommRingCat.of R))
    (z0 : Z0 ⟶ Spec (CommRingCat.of R)) (U0 : Z0.Opens) (hU0 : IsAffineOpen U0)
    [Algebra R Γ(Z0, U0)]
    (halgU : ∀ r : R, algebraMap R Γ(Z0, U0) r =
      (z0.appLE ⊤ U0 le_top) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    (Y V : Scheme.{u}) (ρ : Y ⟶ Z0) (τ : Y ⟶ X0)
    (π : V ⟶ X0) (σ : V ⟶ Spec Γ(Z0, U0)) (j0 : V ⟶ Y)
    [IsOpenImmersion j0] (q : V) (hτ : j0 ≫ τ = π)
    (hρ : j0 ≫ ρ = σ ≫ hU0.fromSpec) (hpU : ρ.base (j0.base q) ∈ U0)
    [Algebra R (Z0.presheaf.stalk (ρ.base (j0.base q)))]
    (halgZ : Z0.fromSpecStalk (ρ.base (j0.base q)) ≫ z0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z0.presheaf.stalk (ρ.base (j0.base q))))))
    [Algebra R (X0.presheaf.stalk (τ.base (j0.base q)))]
    (halgX : X0.fromSpecStalk (τ.base (j0.base q)) ≫ f0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (X0.presheaf.stalk (τ.base (j0.base q)))))) :
    letI : Algebra R (X0.presheaf.stalk (π.base q)) :=
      ((X0.presheaf.germ ⊤ (π.base q) trivial).hom.comp
        (f0.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∀ (Q0 : Ideal ((X0.presheaf.stalk (π.base q)) ⊗[R] Γ(Z0, U0))) [Q0.IsPrime]
      (e0 : V.presheaf.stalk q ≃+* Localization.AtPrime Q0),
      (∀ s : X0.presheaf.stalk (π.base q), e0 ((π.stalkMap q).hom s) =
        algebraMap ((X0.presheaf.stalk (π.base q)) ⊗[R] Γ(Z0, U0))
          (Localization.AtPrime Q0) (s ⊗ₜ[R] (1 : Γ(Z0, U0)))) →
      (∀ a : Γ(Z0, U0), e0 (V.presheaf.germ ⊤ q trivial
        (σ.appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z0, U0))).inv a))) =
        algebraMap ((X0.presheaf.stalk (π.base q)) ⊗[R] Γ(Z0, U0))
          (Localization.AtPrime Q0) ((1 : X0.presheaf.stalk (π.base q)) ⊗ₜ[R] a)) →
      ∃ (P : Ideal ((Z0.presheaf.stalk (ρ.base (j0.base q))) ⊗[R]
          (X0.presheaf.stalk (τ.base (j0.base q))))) (_ : P.IsPrime)
        (e : Y.presheaf.stalk (j0.base q) ≃+* Localization.AtPrime P),
        (∀ s : Z0.presheaf.stalk (ρ.base (j0.base q)), e ((ρ.stalkMap (j0.base q)).hom s) =
          algebraMap ((Z0.presheaf.stalk (ρ.base (j0.base q))) ⊗[R]
            (X0.presheaf.stalk (τ.base (j0.base q)))) (Localization.AtPrime P)
              (s ⊗ₜ[R] (1 : X0.presheaf.stalk (τ.base (j0.base q))))) ∧
        (∀ t : X0.presheaf.stalk (τ.base (j0.base q)), e ((τ.stalkMap (j0.base q)).hom t) =
          algebraMap ((Z0.presheaf.stalk (ρ.base (j0.base q))) ⊗[R]
            (X0.presheaf.stalk (τ.base (j0.base q)))) (Localization.AtPrime P)
              ((1 : Z0.presheaf.stalk (ρ.base (j0.base q))) ⊗ₜ[R] t)) := by
  let S : CommRingCat.{u} := X0.presheaf.stalk (π.base q)
  let L : CommRingCat.{u} := Z0.presheaf.stalk (ρ.base (j0.base q))
  let T : CommRingCat.{u} := X0.presheaf.stalk (τ.base (j0.base q))
  letI aB' : Algebra R S :=
    ((X0.presheaf.germ ⊤ (π.base q) trivial).hom.comp
      (f0.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  intro Q0 hQ0 e0 he0S he0B
  have hxx : τ.base (j0.base q) = π.base q :=
    congrArg (fun m : V ⟶ X0 => m.base q) hτ
  let c : T ≅ S := X0.presheaf.stalkCongr (.of_eq hxx)
  have hc_alg : ∀ r : R, c.hom (algebraMap R T r) = algebraMap R S r :=
    canonical_stalk_scalar_row f0 _ _ hxx halgX
  let cA : T ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := c.commRingCatIsoToRingEquiv) hc_alg
  have E1 : ∀ t : T, (j0.stalkMap q).hom ((τ.stalkMap (j0.base q)).hom t) =
      (π.stalkMap q).hom (c.hom t) :=
    chart_stalk_naturality Y V X0 j0 τ π hτ q
  have E2 : ∀ a : Γ(Z0, U0), (j0.stalkMap q).hom
      ((ρ.stalkMap (j0.base q)).hom ((Z0.presheaf.germ U0 _ hpU).hom a)) =
        V.presheaf.germ ⊤ q trivial
          (σ.appTop ((Scheme.ΓSpecIso (CommRingCat.of Γ(Z0, U0))).inv a)) :=
    affine_chart_germ Z0 Y V U0 hU0 ρ σ j0 q hpU hρ
  let ζU : ↥U0 := ⟨ρ.base (j0.base q), hpU⟩
  letI aZ : Algebra Γ(Z0, U0) L := (Z0.presheaf.germ U0 _ hpU).hom.toAlgebra
  haveI hlocZ : IsLocalization.AtPrime (L : Type u) (hU0.primeIdealOf ζU).asIdeal :=
    hU0.isLocalization_stalk ζU
  haveI : IsScalarTower R Γ(Z0, U0) L :=
    affine_germ_scalar_tower z0 U0 _ hpU halgZ halgU
  let φL : L →+* Localization.AtPrime Q0 :=
    e0.toRingHom.comp ((j0.stalkMap q).hom.comp (ρ.stalkMap (j0.base q)).hom)
  have hφL : ∀ a : Γ(Z0, U0), φL (algebraMap Γ(Z0, U0) L a) =
      algebraMap (S ⊗[R] Γ(Z0, U0)) (Localization.AtPrime Q0) ((1 : S) ⊗ₜ[R] a) := by
    intro a
    exact (congrArg e0 (E2 a)).trans (he0B a)
  have hφLu : ∀ l : L, IsUnit (φL l) ↔ IsUnit l :=
    composed_units_iff (ρ.stalkMap (j0.base q)).hom (j0.stalkMap q).hom e0
  have hQp : Q0.comap (Algebra.TensorProduct.includeRight
      (R := R) (A := (S : Type u)) (B := Γ(Z0, U0))).toRingHom =
        (hU0.primeIdealOf ζU).asIdeal :=
    right_prime_comap (hU0.primeIdealOf ζU).asIdeal Q0 φL hφL hφLu
  obtain ⟨Q1, hQ1, e1, he1S, he1L⟩ :=
    FibreStalkBCRight.core (A := R) (S := (S : Type u)) (R := Γ(Z0, U0))
      (L := (L : Type u)) (hU0.primeIdealOf ζU).asIdeal Q0 hQp
      (Localization.AtPrime Q0) φL hφL
  haveI : Q1.IsPrime := hQ1
  haveI : IsIso (j0.stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion j0)).2 q
  let J : Y.presheaf.stalk (j0.base q) ≃+* V.presheaf.stalk q :=
    (asIso (j0.stalkMap q)).commRingCatIsoToRingEquiv
  have hL : ∀ l : L, e1 (e0 (J ((ρ.stalkMap (j0.base q)).hom l))) =
      algebraMap (S ⊗[R] L) (Localization.AtPrime Q1) ((1 : S) ⊗ₜ[R] l) := by
    intro l
    change e1 (φL l) = _
    exact he1L l
  have hT : ∀ t : T, e1 (e0 (J ((τ.stalkMap (j0.base q)).hom t))) =
      algebraMap (S ⊗[R] L) (Localization.AtPrime Q1) (cA t ⊗ₜ[R] (1 : L)) := by
    intro t
    change e1 (e0 ((j0.stalkMap q).hom ((τ.stalkMap (j0.base q)).hom t))) = _
    rw [E1 t, he0S (c.hom t)]
    exact he1S (cA t)
  exact assemble_two_stalk_maps cA J Q0 Q1 e0 e1
    (ρ.stalkMap (j0.base q)).hom (τ.stalkMap (j0.base q)).hom hL hT

end DefaultProofBlocks

include hU in

theorem main
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p)))))
    (hpU : (pullback.fst z f).base p ∈ U)
    (halgU : ∀ r : R, algebraMap R Γ(Z, U) r = (z.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t)) := by
  classical
  obtain ⟨q, rfl⟩ := exists_j_eq z f U hU hφU p hpU
  let Y : Scheme.{u} := pullback z f
  let V : Scheme.{u} := pullback f (φ (R := R) U)
  let ρ : Y ⟶ Z := pullback.fst z f
  let τ : Y ⟶ X := pullback.snd z f
  let π : V ⟶ X := pullback.fst f (φ (R := R) U)
  let σ : V ⟶ Spec Γ(Z, U) := pullback.snd f (φ (R := R) U)
  let j0 : V ⟶ Y := j z f U hU hφU
  have hτ : j0 ≫ τ = π := j_snd z f U hU hφU
  have hρ : j0 ≫ ρ = σ ≫ hU.fromSpec := by
    rw [j_fst, IsAffineOpen.isoSpec_inv_ι]
  haveI : IsOpenImmersion j0 := inferInstance
  letI aB' : Algebra R (X.presheaf.stalk (π.base q)) :=
    ((X.presheaf.germ ⊤ (π.base q) trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  obtain ⟨Q0, hQ0, e0, he0X, he0A⟩ :=
    fe_wrapper (R := R) f Γ(Z, U) (φ (R := R) U) rfl q (inst := aB') rfl
  haveI : Q0.IsPrime := hQ0
  exact atomic_chart_comparison f z U hU halgU Y V ρ τ π σ j0 q
    hτ hρ hpU halgZ halgX Q0 e0 he0X he0A

end StalkPB
h77_reactivate "P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.StalkPB"

end
h77_reactivate "P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk.StalkPB"

theorem solution
    {R : Type u} [CommRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : Z ⟶ Spec (CommRingCat.of R))
    (p : ↥(pullback z f))
    [Algebra R (Z.presheaf.stalk ((pullback.fst z f).base p))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z f).base p) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z f).base p)))))
    [Algebra R (X.presheaf.stalk ((pullback.snd z f).base p))]
    (halgX : X.fromSpecStalk ((pullback.snd z f).base p) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ((pullback.snd z f).base p))))) :
    ∃ (𝔔 : Ideal ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p))))
      (_ : 𝔔.IsPrime)
      (e : (pullback z f).presheaf.stalk p ≃+* Localization.AtPrime 𝔔),
      (∀ s : Z.presheaf.stalk ((pullback.fst z f).base p),
        e (((pullback.fst z f).stalkMap p).hom s) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) (s ⊗ₜ[R] (1 : X.presheaf.stalk ((pullback.snd z f).base p)))) ∧
      (∀ t : X.presheaf.stalk ((pullback.snd z f).base p),
        e (((pullback.snd z f).stalkMap p).hom t) =
          algebraMap ((Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗[R] (X.presheaf.stalk ((pullback.snd z f).base p)))
            (Localization.AtPrime 𝔔) ((1 : Z.presheaf.stalk ((pullback.fst z f).base p)) ⊗ₜ[R] t)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((pullback.fst z f).base p)) isOpen_univ
  letI : Algebra R Γ(Z, U) := StalkPB.algU z U
  exact StalkPB.main z f U hU (StalkPB.isoSpec_hom_algU z U hU) p halgZ halgX hpU (fun r => rfl)


end P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_stalk
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
