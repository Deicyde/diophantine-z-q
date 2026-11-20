import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd.lean
Original Git blob: e7db7f5d3e6aa0a91863466a939bcda9ea5aaf90
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
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

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

namespace FibreStalkBC
h77_bridge_namespace

variable {A R S k : Type*} [CommRing A] [CommRing R] [CommRing S] [CommRing k]
  [Algebra A R] [Algebra A k] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

@[reducible] noncomputable def tensorAlgebra : Algebra (R ⊗[A] k) (S ⊗[A] k) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A R S) (AlgHom.id A k)).toRingHom.toAlgebra

attribute [local instance] tensorAlgebra

theorem algebraMap_tensor_tmul (r : R) (c : k) :
    algebraMap (R ⊗[A] k) (S ⊗[A] k) (r ⊗ₜ c) = algebraMap R S r ⊗ₜ c := rfl

noncomputable def cancelEquiv :
    ((R ⊗[A] k) ⊗[R] S) ≃ₐ[R ⊗[A] k] (S ⊗[A] k) := by

  let e₁ : ((R ⊗[A] k) ⊗[R] S) ≃ₐ[R] (S ⊗[R] (R ⊗[A] k)) := Algebra.TensorProduct.comm R (R ⊗[A] k) S
  let e₂ : (S ⊗[R] (R ⊗[A] k)) ≃ₐ[S] (S ⊗[A] k) := Algebra.TensorProduct.cancelBaseChange A R S S k
  refine AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv.trans e₂.toRingEquiv) ?_
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    change e₂ (e₁ ((r ⊗ₜ[A] c) ⊗ₜ[R] (1 : S))) = algebraMap R S r ⊗ₜ c
    simp [e₁, e₂, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

theorem isLocalization_tensor (M : Submonoid R) [IsLocalization M S] :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[A] k) M) (S ⊗[A] k) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[A] k) M) ((R ⊗[A] k) ⊗[R] S) :=
    IsLocalization.tensor (R := R) (S := R ⊗[A] k) (A := S) M
  exact IsLocalization.isLocalization_of_algEquiv (R := R ⊗[A] k) (S := (R ⊗[A] k) ⊗[R] S) (P := S ⊗[A] k)
    (Algebra.algebraMapSubmonoid (R ⊗[A] k) M) (cancelEquiv (A := A) (R := R) (S := S) (k := k))

end FibreStalkBC

namespace FibreStalkBC
h77_bridge_namespace

variable {A R S k : Type*} [CommRing A] [CommRing R] [CommRing S] [CommRing k]
  [Algebra A R] [Algebra A k] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

attribute [local instance] tensorAlgebra

theorem isScalarTower_tensor : IsScalarTower R (R ⊗[A] k) (S ⊗[A] k) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := R ⊗[A] k) (A := S ⊗[A] k) fun r => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, algebraMap_tensor_tmul]

theorem core (𝔭 : Ideal R) [𝔭.IsPrime] [IsLocalization.AtPrime S 𝔭]
    (𝔔 : Ideal (R ⊗[A] k)) [h𝔔 : 𝔔.IsPrime]
    (hQp : 𝔔.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := R) (B := k)).toRingHom = 𝔭)
    (Tq : Type*) [CommRing Tq] [Algebra (R ⊗[A] k) Tq] [IsLocalization.AtPrime Tq 𝔔]
    (φ : S →+* Tq) (hφ : ∀ r : R, φ (algebraMap R S r) = algebraMap (R ⊗[A] k) Tq (r ⊗ₜ 1)) :
    haveI := IsLocalization.AtPrime.isLocalRing S 𝔭
    ∃ (𝔮 : Ideal (S ⊗[A] k)) (_ : 𝔮.IsPrime) (e : Tq ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := k)).toRingHom =
        IsLocalRing.maximalIdeal S ∧
      (∀ s : S, e (φ s) = algebraMap (S ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ c : k, e (algebraMap (R ⊗[A] k) Tq ((1 : R) ⊗ₜ[A] c)) = algebraMap (S ⊗[A] k) (Localization.AtPrime 𝔮) ((1 : S) ⊗ₜ[A] c)) := by
  haveI := IsLocalization.AtPrime.isLocalRing S 𝔭
  haveI := isScalarTower_tensor (A := A) (R := R) (S := S) (k := k)
  set T := R ⊗[A] k
  set M : Submonoid T := Algebra.algebraMapSubmonoid T 𝔭.primeCompl with hM
  haveI hloc : IsLocalization M (S ⊗[A] k) := isLocalization_tensor 𝔭.primeCompl

  have hdisj : Disjoint (M : Set T) (𝔔 : Set T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    apply hr
    rw [← hQp]
    exact hrQ

  let 𝔮 : Ideal (S ⊗[A] k) := 𝔔.map (algebraMap T (S ⊗[A] k))
  haveI h𝔮 : 𝔮.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (S ⊗[A] k) 𝔔 h𝔔 hdisj
  have hunder : 𝔮.comap (algebraMap T (S ⊗[A] k)) = 𝔔 := IsLocalization.under_map_of_isPrime_disjoint M (S ⊗[A] k) h𝔔 hdisj

  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) (𝔮.comap (algebraMap T (S ⊗[A] k))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔮) 𝔮
  have hN : 𝔔.primeCompl = (Ideal.comap (algebraMap T (S ⊗[A] k)) 𝔮).primeCompl := by
    ext x
    change x ∉ 𝔔 ↔ x ∉ Ideal.comap (algebraMap T (S ⊗[A] k)) 𝔮
    rw [hunder]
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) 𝔔 := by
    change IsLocalization 𝔔.primeCompl (Localization.AtPrime 𝔮)
    rw [hN]
    exact this
  let e : Tq ≃ₐ[T] Localization.AtPrime 𝔮 := IsLocalization.algEquiv 𝔔.primeCompl Tq (Localization.AtPrime 𝔮)
  refine ⟨𝔮, h𝔮, e.toRingEquiv, ?_, ?_, ?_⟩
  ·
    have hle : IsLocalRing.maximalIdeal S ≤ 𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := k)).toRingHom := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 S, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change algebraMap R S r ⊗ₜ[A] (1 : k) ∈ 𝔮
      rw [← algebraMap_tensor_tmul]
      apply Ideal.mem_map_of_mem
      rw [← hQp] at hr
      exact hr
    refine ((IsLocalRing.maximalIdeal.isMaximal S).eq_of_le ?_ hle).symm
    intro htop
    apply h𝔮.ne_top
    rw [Ideal.eq_top_iff_one] at htop ⊢
    simp at htop
    exact htop
  ·
    intro s
    suffices h : (e.toRingEquiv.toRingHom.comp φ) =
        (algebraMap (S ⊗[A] k) (Localization.AtPrime 𝔮)).comp
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := S) (B := k)).toRingHom by
      exact congrArg (fun f : S →+* Localization.AtPrime 𝔮 => f s) h
    refine IsLocalization.ringHom_ext 𝔭.primeCompl ?_
    ext r
    change e (φ (algebraMap R S r)) = algebraMap (S ⊗[A] k) (Localization.AtPrime 𝔮) (algebraMap R S r ⊗ₜ[A] 1)
    rw [hφ, ← algebraMap_tensor_tmul, ← IsScalarTower.algebraMap_apply]
    exact e.commutes (r ⊗ₜ 1)
  ·
    intro c
    change e (algebraMap T Tq ((1 : R) ⊗ₜ[A] c)) = _
    rw [e.commutes ((1 : R) ⊗ₜ[A] c), IsScalarTower.algebraMap_apply T (S ⊗[A] k) (Localization.AtPrime 𝔮), algebraMap_tensor_tmul,
      map_one]

end FibreStalkBC

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


/-
DEFAULT-LIMIT RE-PROOF (2026-11-17): only proof-command factoring.
The existing affine germ, scalar and first-projection calculations are proved
as separate top-level private lemmas with atomic scheme/ring/map parameters.
No budget, option, import, public hypothesis, point, algebra choice or output
is changed. The only stalk congruences below are the original canonical ones
from actual proved point/morphism equalities. No new cast definition is used.
-/

private theorem affine_germ_base_compat
    (Y : Scheme.{u}) (R B : CommRingCat.{u})
    (ι : Spec R ⟶ Y) (g : Y ⟶ Spec B) (φ : B ⟶ R)
    (h : ι ≫ g = Spec.map φ) (w : PrimeSpectrum R) (b : B) :
    (Spec.stalkIso R w).hom (ι.stalkMap w
      (Y.presheaf.germ ⊤ (ι.base w) trivial
        (g.appTop ((Scheme.ΓSpecIso B).inv b)))) =
      algebraMap R (Localization.AtPrime w.asIdeal) (φ b) := by
  erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ w trivial]
  have happ : ι.app ⊤ (g.appTop ((Scheme.ΓSpecIso B).inv b)) =
      (Scheme.ΓSpecIso R).inv (φ b) := by
    have hcomp : ι.app ⊤ (g.appTop ((Scheme.ΓSpecIso B).inv b)) =
        (ι ≫ g).appTop ((Scheme.ΓSpecIso B).inv b) := by
      rw [Scheme.Hom.comp_appTop]
      rfl
    rw [hcomp, h]
    have hn := Scheme.ΓSpecIso_inv_naturality φ
    have hv := congrArg (fun q : B ⟶ Γ(Spec R, ⊤) => q.hom b) hn
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hv
    exact hv.symm
  erw [happ]
  have hgerm := congrArg
    (fun q : Γ(Spec R, ⊤) ⟶ CommRingCat.of (Localization.AtPrime w.asIdeal) =>
      q.hom ((Scheme.ΓSpecIso R).inv (φ b))) (Spec.germ_stalkMapIso_hom w)
  simp only [CommRingCat.comp_apply] at hgerm
  erw [hgerm]
  simp

private theorem affine_stalk_scalar_compat
    {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (Rj : CommRingCat.{u}) (fj : Spec Rj ⟶ X) (φ : CommRingCat.of A ⟶ Rj)
    (hφ : Spec.map φ = fj ≫ f) (z : X) (p : PrimeSpectrum Rj)
    (hp : z = fj.base p) [IsIso (fj.stalkMap p)] :
    let eZ : X.presheaf.stalk z ≅ X.presheaf.stalk (fj.base p) :=
      X.presheaf.stalkCongr (.of_eq hp)
    let eJ : X.presheaf.stalk (fj.base p) ≅ (Spec Rj).presheaf.stalk p :=
      asIso (fj.stalkMap p)
    let rS : (X.presheaf.stalk z : Type u) ≃+* Localization.AtPrime p.asIdeal :=
      (eZ ≪≫ eJ ≪≫ Spec.stalkIso Rj p).commRingCatIsoToRingEquiv
    ∀ a : A, rS (X.presheaf.germ ⊤ z trivial
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      algebraMap Rj (Localization.AtPrime p.asIdeal) (φ a) := by
  let eZ : X.presheaf.stalk z ≅ X.presheaf.stalk (fj.base p) :=
    X.presheaf.stalkCongr (.of_eq hp)
  let eJ : X.presheaf.stalk (fj.base p) ≅ (Spec Rj).presheaf.stalk p :=
    asIso (fj.stalkMap p)
  let rS : (X.presheaf.stalk z : Type u) ≃+* Localization.AtPrime p.asIdeal :=
    (eZ ≪≫ eJ ≪≫ Spec.stalkIso Rj p).commRingCatIsoToRingEquiv
  change ∀ a : A, rS (X.presheaf.germ ⊤ z trivial
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
    algebraMap Rj (Localization.AtPrime p.asIdeal) (φ a)
  intro a
  change (Spec.stalkIso Rj p).hom (fj.stalkMap p (eZ.hom
    (X.presheaf.germ ⊤ z trivial
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))))) = _
  have hgerm : eZ.hom (X.presheaf.germ ⊤ z trivial
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      X.presheaf.germ ⊤ (fj.base p) trivial
        (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
    simp only [eZ, TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf (U := ⊤) trivial
      (Inseparable.of_eq hp).ge _
  rw [hgerm]
  exact affine_germ_base_compat X Rj (CommRingCat.of A) fj f φ hφ.symm p a

private theorem affine_stalk_first_projection
    (X Y : Scheme.{u}) (Rj T : CommRingCat.{u})
    (fj : Spec Rj ⟶ X) (ι : Spec T ⟶ Y) (π : Y ⟶ X)
    (incl : Rj ⟶ T) (w : PrimeSpectrum T)
    (h : ι ≫ π = Spec.map incl ≫ fj)
    [IsIso (fj.stalkMap (PrimeSpectrum.comap incl.hom w))] :
    let p : PrimeSpectrum Rj := PrimeSpectrum.comap incl.hom w
    let hp : π.base (ι.base w) = fj.base p :=
      congrArg (fun q : Spec T ⟶ X => q.base w) h
    let eZ : X.presheaf.stalk (π.base (ι.base w)) ≅ X.presheaf.stalk (fj.base p) :=
      X.presheaf.stalkCongr (.of_eq hp)
    let eJ : X.presheaf.stalk (fj.base p) ≅ (Spec Rj).presheaf.stalk p :=
      asIso (fj.stalkMap p)
    let rS : (X.presheaf.stalk (π.base (ι.base w)) : Type u) ≃+*
        Localization.AtPrime p.asIdeal :=
      (eZ ≪≫ eJ ≪≫ Spec.stalkIso Rj p).commRingCatIsoToRingEquiv
    ∀ r : Rj, (Spec.stalkIso T w).hom (ι.stalkMap w
      (π.stalkMap (ι.base w) (rS.symm (algebraMap Rj
        (Localization.AtPrime p.asIdeal) r)))) =
      algebraMap T (Localization.AtPrime w.asIdeal) (incl r) := by
  let p : PrimeSpectrum Rj := PrimeSpectrum.comap incl.hom w
  let hp : π.base (ι.base w) = fj.base p :=
    congrArg (fun q : Spec T ⟶ X => q.base w) h
  let eZ : X.presheaf.stalk (π.base (ι.base w)) ≅ X.presheaf.stalk (fj.base p) :=
    X.presheaf.stalkCongr (.of_eq hp)
  let eJ : X.presheaf.stalk (fj.base p) ≅ (Spec Rj).presheaf.stalk p :=
    asIso (fj.stalkMap p)
  let rS : (X.presheaf.stalk (π.base (ι.base w)) : Type u) ≃+*
      Localization.AtPrime p.asIdeal :=
    (eZ ≪≫ eJ ≪≫ Spec.stalkIso Rj p).commRingCatIsoToRingEquiv
  change ∀ r : Rj, (Spec.stalkIso T w).hom (ι.stalkMap w
    (π.stalkMap (ι.base w) (rS.symm (algebraMap Rj
      (Localization.AtPrime p.asIdeal) r)))) =
    algebraMap T (Localization.AtPrime w.asIdeal) (incl r)
  intro r
  have hcomp : ∀ v, ι.stalkMap w (π.stalkMap (ι.base w) v) =
      (ι ≫ π).stalkMap w v := fun v =>
    (congrArg (fun q : X.presheaf.stalk _ ⟶ _ => q.hom v)
      (Scheme.Hom.stalkMap_comp ι π w)).symm
  rw [hcomp, Scheme.Hom.stalkMap_congr_hom _ _ h w, Scheme.Hom.stalkMap_comp]
  change (Spec.stalkIso T w).hom ((Spec.map incl).stalkMap w
    (fj.stalkMap p (eZ.hom
      (rS.symm (algebraMap Rj (Localization.AtPrime p.asIdeal) r))))) = _
  have hinv : ∀ q, rS.symm q =
      eZ.inv (eJ.inv ((Spec.stalkIso Rj p).inv q)) := fun q => rfl
  rw [hinv, Iso.inv_hom_id_apply]
  have hchart : ∀ v, fj.stalkMap p (eJ.inv v) = v := fun v =>
    Iso.inv_hom_id_apply eJ v
  rw [hchart]
  have hlocal := congrArg
    (fun q : (Spec Rj).presheaf.stalk p ⟶ (Spec T).presheaf.stalk w =>
      (Spec.stalkIso T w).hom
        (q ((Spec.stalkIso Rj p).inv (algebraMap Rj (Localization.AtPrime p.asIdeal) r))))
    (Scheme.localRingHom_comp_stalkIso incl w).symm
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, Iso.hom_inv_id_apply] at hlocal
  erw [hlocal]
  change (Spec.stalkIso T w).hom ((Spec.stalkIso T w).inv
    (Localization.localRingHom p.asIdeal w.asIdeal incl.hom rfl
      ((Spec.stalkIso Rj p).hom ((Spec.stalkIso Rj p).inv
        (algebraMap Rj (Localization.AtPrime p.asIdeal) r))))) = _
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, Localization.localRingHom_to_map]


/-
FIXED-TYPE COMMAND FACTORING (2026-11-17).
The affine chart is earned in its own command. Its ring, point and maps are
opaque parameters in the stalk commands below; Y/π/σ are atomic schemes/maps.
Localization and the ORIGINAL germ-defined A-algebra scalar row are derived
separately, before the unchanged tensor-localization core. The whole stalk
RingEquiv is the same composite of actual stalk Isos, with all three clauses.
-/

private theorem exists_affine_tensor_chart
    {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (k : Type u) [CommRing k] [Algebra A k]
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))))) :
    ∃ (Rj : CommRingCat.{u}) (algRj : Algebra A Rj),
      letI := algRj
      ∃ (fj : Spec Rj ⟶ X)
        (ι : Spec (CommRingCat.of (Rj ⊗[A] k)) ⟶
          pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))))
        (w : PrimeSpectrum (Rj ⊗[A] k)),
        Spec.map (CommRingCat.ofHom (algebraMap A Rj)) = fj ≫ f ∧
        IsOpenImmersion fj ∧ IsOpenImmersion ι ∧ ι.base w = x ∧
        ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k))) =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := A) (A := (Rj : Type u)) (B := k))) ≫ fj ∧
        ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A k))) =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := A) (A := (Rj : Type u)) (B := k)).toRingHom) := by
  classical
  let 𝒰 := X.affineOpenCover
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap A k)))
  obtain ⟨j, y, hyx⟩ := 𝒱.exists_eq x
  set Rj : CommRingCat := 𝒰.X j with hRj
  set fj : Spec Rj ⟶ X := 𝒰.f j with hfj
  let φ : CommRingCat.of A ⟶ Rj := (Spec.fullyFaithful.preimage (fj ≫ f)).unop
  have hφ : Spec.map φ = fj ≫ f := Spec.fullyFaithful.map_preimage (fj ≫ f)
  letI algRj : Algebra A Rj := φ.hom.toAlgebra
  have hφ' : CommRingCat.ofHom (algebraMap A Rj) = φ := rfl
  let ec : pullback (Spec.map (CommRingCat.ofHom (algebraMap A Rj)))
      (Spec.map (CommRingCat.ofHom (algebraMap A k))) ≅ 𝒱.X j :=
    pullback.congrHom (by rw [hφ', hφ]; rfl) rfl
  let eT : Spec (CommRingCat.of (Rj ⊗[A] k)) ≅ 𝒱.X j :=
    (pullbackSpecIso A Rj k).symm ≪≫ ec
  obtain ⟨w, hw⟩ := (Scheme.homeoOfIso eT).surjective y
  set ι : Spec (CommRingCat.of (Rj ⊗[A] k)) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))) :=
    eT.hom ≫ 𝒱.f j with hι
  have hxι : ι.base w = x := by
    rw [← hyx, ← hw, Scheme.coe_homeoOfIso, hι]
    rfl
  have hιfst : ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := A) (A := (Rj : Type u)) (B := k))) ≫ fj := by
    simp only [hι, eT, ec, 𝒱, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom,
      Scheme.Pullback.openCoverOfLeft_f, Category.assoc]
    erw [pullback.lift_fst]
    erw [pullback.lift_fst_assoc]
    simp only [Category.comp_id, Category.assoc]
    erw [pullbackSpecIso_inv_fst_assoc]
    rfl
  have hιsnd : ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A k))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := A) (A := (Rj : Type u)) (B := k)).toRingHom) := by
    simp only [hι, eT, ec, 𝒱, Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom,
      Scheme.Pullback.openCoverOfLeft_f, Category.assoc]
    erw [pullback.lift_snd]
    erw [pullback.lift_snd]
    simp only [Category.comp_id, Category.assoc]
    erw [pullbackSpecIso_inv_snd]
    rfl
  have hfjIO : IsOpenImmersion fj := 𝒰.map_prop j
  have hιIO : IsOpenImmersion ι := by
    rw [hι]
    infer_instance
  have hφmap : Spec.map (CommRingCat.ofHom (algebraMap A Rj)) = fj ≫ f := by
    rw [hφ', hφ]
  exact ⟨Rj, algRj, fj, ι, w, hφmap, hfjIO, hιIO, hxι, hιfst, hιsnd⟩

private theorem localization_from_equiv
    (R S : Type u) [CommRing R] [CommRing S] (p : Ideal R) [p.IsPrime]
    (e : S ≃+* Localization.AtPrime p) :
    letI : Algebra R S :=
      (e.symm.toRingHom.comp (algebraMap R (Localization.AtPrime p))).toAlgebra
    IsLocalization.AtPrime S p := by
  letI : Algebra R S :=
    (e.symm.toRingHom.comp (algebraMap R (Localization.AtPrime p))).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv (R := R)
    (S := Localization.AtPrime p) p.primeCompl
    (AlgEquiv.ofRingEquiv (f := e.symm) (fun r => rfl))

private theorem scalar_tower_from_equiv
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (p : Ideal R) [p.IsPrime]
    (e : S ≃+* Localization.AtPrime p)
    (h : ∀ a : A, e (algebraMap A S a) =
      algebraMap R (Localization.AtPrime p) (algebraMap A R a)) :
    letI : Algebra R S :=
      (e.symm.toRingHom.comp (algebraMap R (Localization.AtPrime p))).toAlgebra
    IsScalarTower A R S := by
  letI : Algebra R S :=
    (e.symm.toRingHom.comp (algebraMap R (Localization.AtPrime p))).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a => by
    apply e.injective
    change e (algebraMap A S a) =
      e (e.symm (algebraMap R (Localization.AtPrime p) (algebraMap A R a)))
    rw [h, RingEquiv.apply_symm_apply]

private theorem affine_chart_core
    {A : Type u} [CommRing A] (X Y : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of A)) (k : Type u) [CommRing k] [Algebra A k]
    (π : Y ⟶ X) (Rj : CommRingCat.{u}) [Algebra A Rj]
    (fj : Spec Rj ⟶ X) [IsOpenImmersion fj]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap A Rj)) = fj ≫ f)
    (ι : Spec (CommRingCat.of (Rj ⊗[A] k)) ⟶ Y)
    (w : PrimeSpectrum (Rj ⊗[A] k))
    (hfst : ι ≫ π = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := (Rj : Type u)) (B := k))) ≫ fj) :
    letI z := π.base (ι.base w)
    letI : Algebra A (X.presheaf.stalk z) :=
      ((X.presheaf.germ ⊤ z trivial).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X.presheaf.stalk z) ⊗[A] k)) (_ : 𝔮.IsPrime)
      (e : Localization.AtPrime w.asIdeal ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := X.presheaf.stalk z) (B := k)).toRingHom =
          IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      (∀ s : X.presheaf.stalk z,
        e ((Spec.stalkIso (CommRingCat.of (Rj ⊗[A] k)) w).hom
          (ι.stalkMap w (π.stalkMap (ι.base w) s))) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ c : k, e (algebraMap (Rj ⊗[A] k) (Localization.AtPrime w.asIdeal)
        ((1 : Rj) ⊗ₜ[A] c)) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A] c)) := by
  let T : Type u := (Rj : Type u) ⊗[A] k
  let incl : Rj ⟶ CommRingCat.of T := CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := (Rj : Type u)) (B := k))
  let p : PrimeSpectrum Rj := PrimeSpectrum.comap incl.hom w
  let z : X := π.base (ι.base w)
  have hzpt : z = fj.base p :=
    congrArg (fun q : Spec (CommRingCat.of T) ⟶ X => q.base w) hfst
  haveI : IsIso (fj.stalkMap p) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion fj)).2 p
  let S : CommRingCat.{u} := X.presheaf.stalk z
  let eZ : S ≅ X.presheaf.stalk (fj.base p) := X.presheaf.stalkCongr (.of_eq hzpt)
  let eJ : X.presheaf.stalk (fj.base p) ≅ (Spec Rj).presheaf.stalk p :=
    asIso (fj.stalkMap p)
  let rS : (S : Type u) ≃+* Localization.AtPrime p.asIdeal :=
    (eZ ≪≫ eJ ≪≫ Spec.stalkIso Rj p).commRingCatIsoToRingEquiv
  letI algRjS : Algebra Rj S :=
    (rS.symm.toRingHom.comp (algebraMap Rj (Localization.AtPrime p.asIdeal))).toAlgebra
  haveI : IsLocalization.AtPrime (S : Type u) p.asIdeal :=
    localization_from_equiv (Rj : Type u) (S : Type u) p.asIdeal rS
  letI instA : Algebra A S :=
    ((X.presheaf.germ ⊤ z trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
  have hrS : ∀ a : A, rS (algebraMap A S a) =
      algebraMap Rj (Localization.AtPrime p.asIdeal) (algebraMap A Rj a) :=
    affine_stalk_scalar_compat X f Rj fj
      (CommRingCat.ofHom (algebraMap A Rj)) hφ z p hzpt
  haveI : IsScalarTower A Rj S := scalar_tower_from_equiv p.asIdeal rS hrS
  let φS : S →+* Localization.AtPrime w.asIdeal :=
    (Spec.stalkIso (CommRingCat.of T) w).hom.hom.comp
      ((ι.stalkMap w).hom.comp (π.stalkMap (ι.base w)).hom)
  have hφS : ∀ r : Rj, φS (algebraMap Rj S r) =
      algebraMap T (Localization.AtPrime w.asIdeal) (r ⊗ₜ[A] 1) :=
    affine_stalk_first_projection X Y Rj (CommRingCat.of T) fj ι π incl w hfst
  have hQp : w.asIdeal.comap (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := (Rj : Type u)) (B := k)).toRingHom = p.asIdeal := rfl
  obtain ⟨𝔮, h𝔮, e, hcomap, hcompat, hcompatk⟩ :=
    FibreStalkBC.core (A := A) (R := (Rj : Type u)) (S := (S : Type u)) (k := k)
      p.asIdeal w.asIdeal hQp (Localization.AtPrime w.asIdeal) φS hφS
  exact ⟨𝔮, h𝔮, e, hcomap, hcompat, hcompatk⟩

private theorem composed_stalk_equiv_apply
    (Y : Scheme.{u}) (T : CommRingCat.{u}) (ι : Spec T ⟶ Y)
    (w : PrimeSpectrum T) [IsIso (ι.stalkMap w)]
    (L : Type u) [CommRing L] (e : Localization.AtPrime w.asIdeal ≃+* L)
    (s : Y.presheaf.stalk (ι.base w)) :
    (((asIso (ι.stalkMap w)) ≪≫ Spec.stalkIso T w).commRingCatIsoToRingEquiv.trans e) s =
      e ((Spec.stalkIso T w).hom (ι.stalkMap w s)) := rfl

private theorem affine_chart_stalk_equiv
    {A : Type u} [CommRing A] (X Y : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of A)) (k : Type u) [CommRing k] [Algebra A k]
    (π : Y ⟶ X) (σ : Y ⟶ Spec (CommRingCat.of k))
    (Rj : CommRingCat.{u}) [Algebra A Rj] (fj : Spec Rj ⟶ X) [IsOpenImmersion fj]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap A Rj)) = fj ≫ f)
    (ι : Spec (CommRingCat.of (Rj ⊗[A] k)) ⟶ Y) [IsOpenImmersion ι]
    (w : PrimeSpectrum (Rj ⊗[A] k))
    (hfst : ι ≫ π = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := (Rj : Type u)) (B := k))) ≫ fj)
    (hsnd : ι ≫ σ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := A) (A := (Rj : Type u)) (B := k)).toRingHom)) :
    letI z := π.base (ι.base w)
    letI : Algebra A (X.presheaf.stalk z) :=
      ((X.presheaf.germ ⊤ z trivial).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X.presheaf.stalk z) ⊗[A] k)) (_ : 𝔮.IsPrime)
      (e : Y.presheaf.stalk (ι.base w) ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := X.presheaf.stalk z) (B := k)).toRingHom =
          IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      (∀ s : X.presheaf.stalk z, e ((π.stalkMap (ι.base w)).hom s) =
        algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ c : k, e (Y.presheaf.germ ⊤ (ι.base w) trivial
        (σ.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A] c)) := by
  let z : X := π.base (ι.base w)
  letI : Algebra A (X.presheaf.stalk z) :=
    ((X.presheaf.germ ⊤ z trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
  haveI : IsIso (ι.stalkMap w) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion ι)).2 w
  obtain ⟨𝔮, h𝔮, e, hcomap, hcompat, hcompatk⟩ :=
    affine_chart_core X Y f k π Rj fj hφ ι w hfst
  refine ⟨𝔮, h𝔮,
    ((asIso (ι.stalkMap w)) ≪≫ Spec.stalkIso (CommRingCat.of (Rj ⊗[A] k)) w).commRingCatIsoToRingEquiv.trans e,
    hcomap, ?_, ?_⟩
  · intro s
    rw [composed_stalk_equiv_apply]
    exact hcompat s
  · intro c
    rw [composed_stalk_equiv_apply]
    rw [affine_germ_base_compat Y (CommRingCat.of (Rj ⊗[A] k)) (CommRingCat.of k)
      ι σ (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := A) (A := (Rj : Type u)) (B := k)).toRingHom) hsnd w c]
    exact hcompatk c

theorem solution
    {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (k : Type u) [CommRing k] [Algebra A k]
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))))) :
    letI z := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base x
    letI : Algebra A (X.presheaf.stalk z) :=
      ((X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X.presheaf.stalk z) ⊗[A] k)) (_ : 𝔮.IsPrime)
      (e : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.stalk x ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := X.presheaf.stalk z) (B := k)).toRingHom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      (∀ s : X.presheaf.stalk z,
        e (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ c : k,
        e ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.germ ⊤ x trivial
            ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A] c)) := by
  let Y : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))
  let π : Y ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))
  let σ : Y ⟶ Spec (CommRingCat.of k) :=
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A k)))
  obtain ⟨Rj, algRj, hchart⟩ := exists_affine_tensor_chart X f k x
  letI := algRj
  obtain ⟨fj, ι, w, hφ, hfjIO, hιIO, hxι, hfst, hsnd⟩ := hchart
  letI : IsOpenImmersion fj := hfjIO
  letI : IsOpenImmersion ι := hιIO
  subst hxι
  exact affine_chart_stalk_equiv X Y f k π σ Rj fj hφ ι w hfst hsnd


end P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
