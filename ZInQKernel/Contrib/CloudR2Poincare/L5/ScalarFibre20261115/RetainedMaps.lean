import ZInQKernel.Contrib.CloudR2Poincare.L5.ScalarFibre20261115.Complexes

/-!
# Actual retained-model scalar arrows and composition coherence

For A -> S -> K, the ORIGINAL ModuleCat.extendScalarsComp identifies the
iterated raw extension with the original composite. The Gamma conversion
commutes with that native composition: this is proved on actual pure tensors,
not just a chosen category isomorphism or equality of numerical ranks.

Consequently the SAME retained comparison e and every original face Phi are
transported to restriction of their ACTUAL Gamma-valued scalar extensions.
This is coefficient/naturality transport only, NOT L1's semantic Cech/native-H
face theorem. L1 retains that ownership and supplies its proved face maps.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open scoped TensorProduct ChangeOfRings

namespace ZInQ.Contrib.CloudR2Poincare.L5.ScalarFibre20261115

/-- The ORIGINAL scalar-composition inverse evaluated on an actual double
pure tensor. Beta need not be flat. -/
theorem extendScalarsComp_inv_tmul
    {A S K : Type u} [CommRing A] [CommRing S] [CommRing K]
    (α : A →+* S) (β : S →+* K) (M : ModuleCat.{u} A) (b : K) (s : S) (m : M) :
    (ModuleCat.extendScalarsComp α β).inv.app M
      (b ⊗ₜ[S,β] (s ⊗ₜ[A,α] m)) = (b * β s) ⊗ₜ[A,β.comp α] m := by
  letI : Algebra S K := β.toAlgebra
  apply ((ModuleCat.extendScalarsComp α β).app M).toLinearEquiv.symm_apply_eq.mpr
  change b ⊗ₜ[S,β] (s ⊗ₜ[A,α] m) =
    (ModuleCat.extendScalarsComp α β).hom.app M ((b * β s) ⊗ₜ[A,β.comp α] m)
  rw [extendScalarsComp_hom_tmul]
  have h : s ⊗ₜ[A,α] m = s • ((1 : S) ⊗ₜ[A,α] m) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [h, TensorProduct.tmul_smul]
  change (β s * b) ⊗ₜ[S,β] ((1 : S) ⊗ₜ[A,α] m) =
    (b * β s) ⊗ₜ[S,β] ((1 : S) ⊗ₜ[A,α] m)
  rw [mul_comm]

/-- Canonical Gamma conversion and the ORIGINAL raw A -> S -> K composition
commute on every original module, not a surrogate rank-selected comparison. -/
theorem gammaScalarExtensionIso_comp_coherence
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalarsComp α β).inv.app M ≫
        (gammaScalarExtensionIso K (β.comp α)).hom.app M =
      (gammaScalarExtensionIso K β).hom.app ((ModuleCat.extendScalars α).obj M) ≫
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).map
          ((ModuleCat.extendScalarsComp α ((Scheme.ΓSpecIso K).inv.hom.comp β)).inv.app M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    change (gammaScalarExtensionIso K (β.comp α)).hom.app M
        ((ModuleCat.extendScalarsComp α β).inv.app M
          ((1 : K) ⊗ₜ[S,β] (s ⊗ₜ[A,α] m))) =
      (ModuleCat.extendScalarsComp α ((Scheme.ΓSpecIso K).inv.hom.comp β)).inv.app M
        ((gammaScalarExtensionIso K β).hom.app ((ModuleCat.extendScalars α).obj M)
          ((1 : K) ⊗ₜ[S,β] (s ⊗ₜ[A,α] m)))
    simp only [extendScalarsComp_inv_tmul, gammaScalarExtensionIso_hom_tmul, one_mul, map_one]
    rfl
  | add x y hx hy =>
    simp only [ModuleCat.comp_apply, TensorProduct.tmul_add, map_add] at hx hy ⊢
    rw [hx, hy]

/-- Literal native raw extension-composition iso on integer complexes. -/
def rawScalarCompositionCochainIso
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K) :
    (ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars (β.comp α)).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp α β).symm (.up ℤ)

/-- Conversion AFTER ORIGINAL raw A -> S -> K composition, with its actual
native iso retained rather than replacing a scalar functor by an avatar. -/
def gammaScalarCompositeCochainIso
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K) :
    (ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).mapHomologicalComplex
        (.up ℤ) ⋙
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ) :=
  rawScalarCompositionCochainIso α K β ≪≫ gammaScalarCochainIso K (β.comp α)

/-- On ACTUAL complexes the composite conversion equals successive Gamma
conversion followed by the original Gamma extension-composition map. -/
theorem gammaScalarCompositeCochainIso_coherence
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    (C : CochainComplex (ModuleCat.{u} A) ℤ) :
    (gammaScalarCompositeCochainIso α K β).hom.app C =
      (gammaScalarCochainIso K β).hom.app
          (((ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)).obj C) ≫
        ((ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)).map
          ((rawScalarCompositionCochainIso α (CommRingCat.of Γ(Spec K, ⊤))
            ((Scheme.ΓSpecIso K).inv.hom.comp β)).hom.app C) := by
  ext n : 1
  exact gammaScalarExtensionIso_comp_coherence α K β (C.X n)

/-- Naturality in the SAME original face Phi for the composed A -> S -> K
conversion; this preserves the arrow that native Cech comparison expects. -/
theorem gammaScalarCompositeCochainIso_naturality
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    (C D : CochainComplex (ModuleCat.{u} A) ℤ) (Φ : C ⟶ D) :
    ((ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ)).map
        (((ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)).map Φ) ≫
      (gammaScalarCompositeCochainIso α K β).hom.app D =
    (gammaScalarCompositeCochainIso α K β).hom.app C ≫
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)).map
        (((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).mapHomologicalComplex
          (.up ℤ)).map Φ) :=
  (gammaScalarCompositeCochainIso α K β).hom.naturality Φ

/-- The SAME retained model comparison transported using ACTUAL Gamma-valued
extension and native composition, then original K-scalar restriction. -/
def retainedGammaChainMap
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (e : P ⟶ ((ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)).obj C) :
    ((ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex
          (.up ℤ)).obj P) ⟶
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).mapHomologicalComplex
          (.up ℤ)).obj C) :=
  ((ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)).map
    ((((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex
      (.up ℤ)).map e) ≫
        (rawScalarCompositionCochainIso α (CommRingCat.of Γ(Spec K, ⊤))
          ((Scheme.ΓSpecIso K).inv.hom.comp β)).hom.app C)

/-- The raw beta extension of the ORIGINAL retained e fits the canonical
conversion square with its ACTUAL restricted Gamma extension. -/
theorem retainedGammaChainMap_square
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (e : P ⟶ ((ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)).obj C) :
    ((ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ)).map e ≫
        (gammaScalarCompositeCochainIso α K β).hom.app C =
      (gammaScalarCochainIso K β).hom.app P ≫ retainedGammaChainMap α K β C P e := by
  rw [gammaScalarCompositeCochainIso_coherence, ← Category.assoc,
    (gammaScalarCochainIso K β).hom.naturality e]
  simp only [retainedGammaChainMap, Functor.map_comp, Functor.comp_map, Category.assoc]

end ZInQ.Contrib.CloudR2Poincare.L5.ScalarFibre20261115
