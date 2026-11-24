import ZInQKernel.Contrib.CloudR2Poincare.L2.TildeConeComparison
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Canonical raw scalar extension / Gamma-Spec coefficient conversion

L2 already certifies the ORIGINAL residue beta map and tilde/cone fibre
comparison. This file proves only the missing coefficient-natural conversion:
E_beta is canonically E_(eta beta) followed by restriction along eta. Here eta
is an ACTUAL ring equivalence (specialized to Gamma-Spec), and beta is ANY ring
map. No beta-flatness or isomorphism chosen from ranks is used.

The comparison is the ACTUAL extension/restriction adjunction unit, followed
by the inverse of the ACTUAL extension-composition iso. Forward b tensor m is
eta(b) tensor m; inverse uses eta^{-1}. Native ring objects are retained in the
Gamma-Spec and residue specializations, not rebuilt from a Field dictionary.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace ZInQ.Contrib.CloudR2Poincare.L5.ScalarFibre20261115

section RingEquivalence
variable {S K G : Type u} [CommRing S] [CommRing K] [CommRing G]

/-- The canonical extension-composition map evaluated on ANY pure tensor.
This is the native adjunction-defined composition iso, not a substitute. -/
theorem extendScalarsComp_hom_tmul (β : S →+* K) (η : K →+* G)
    (M : ModuleCat.{u} S) (g : G) (m : M) :
    (ModuleCat.extendScalarsComp β η).hom.app M (g ⊗ₜ[S,η.comp β] m) =
      g ⊗ₜ[K,η] ((1 : K) ⊗ₜ[S,β] m) := by
  calc
    _ = (ModuleCat.extendScalarsComp β η).hom.app M
        (g • ((1 : G) ⊗ₜ[S,η.comp β] m)) := by
      rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    _ = g • ((ModuleCat.extendScalarsComp β η).hom.app M
        ((1 : G) ⊗ₜ[S,η.comp β] m)) := by rw [map_smul]
    _ = g • ((1 : G) ⊗ₜ[K,η] ((1 : K) ⊗ₜ[S,β] m)) := by
      rw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
    _ = _ := by
      change (g * (1 : G)) ⊗ₜ[K,η] ((1 : K) ⊗ₜ[S,β] m) =
        g ⊗ₜ[K,η] ((1 : K) ⊗ₜ[S,β] m)
      rw [mul_one]

/-- Canonical coefficient-natural functor iso, for EVERY original module/map.
Only eta is invertible; beta need not be flat. -/
def scalarExtensionRingEquivIso (β : S →+* K) (η : K ≃+* G) :
    (ModuleCat.extendScalars β : ModuleCat.{u} S ⥤ ModuleCat.{u} K) ≅
      (ModuleCat.extendScalars (η.toRingHom.comp β) : ModuleCat.{u} S ⥤ ModuleCat.{u} G) ⋙
        (ModuleCat.restrictScalars η.toRingHom : ModuleCat.{u} G ⥤ ModuleCat.{u} K) := by
  let F := ModuleCat.extendScalars β
  let E := ModuleCat.extendScalars η.toRingHom
  let R := ModuleCat.restrictScalars η.toRingHom
  let adj := ModuleCat.extendRestrictScalarsAdj η.toRingHom
  haveI : R.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv η
  exact (Functor.rightUnitor F).symm ≪≫
    Functor.isoWhiskerLeft F (asIso adj.unit) ≪≫
      (Functor.associator F E R).symm ≪≫
        Functor.isoWhiskerRight (ModuleCat.extendScalarsComp β η.toRingHom).symm R

/-- The functor component is an ACTUAL K-linear module isomorphism. -/
def scalarExtensionRingEquivComponent (β : S →+* K) (η : K ≃+* G)
    (M : ModuleCat.{u} S) :
    (ModuleCat.extendScalars β).obj M ≅
      (ModuleCat.restrictScalars η.toRingHom).obj
        ((ModuleCat.extendScalars (η.toRingHom.comp β)).obj M) :=
  (scalarExtensionRingEquivIso β η).app M

/-- The forward map is exactly eta(b) tensor m, from the original native
adjunction and composition iso. -/
theorem scalarExtensionRingEquivComponent_hom_tmul
    (β : S →+* K) (η : K ≃+* G) (M : ModuleCat.{u} S) (b : K) (m : M) :
    (scalarExtensionRingEquivComponent β η M).hom (b ⊗ₜ[S,β] m) =
      η b ⊗ₜ[S,η.toRingHom.comp β] m := by
  letI : Algebra K G := η.toRingHom.toAlgebra
  change ((ModuleCat.extendScalarsComp β η.toRingHom).app M).toLinearEquiv.symm
      ((1 : G) ⊗ₜ[K,η.toRingHom] (b ⊗ₜ[S,β] m)) =
        η b ⊗ₜ[S,η.toRingHom.comp β] m
  apply ((ModuleCat.extendScalarsComp β η.toRingHom).app M).toLinearEquiv.symm_apply_eq.mpr
  change (1 : G) ⊗ₜ[K,η.toRingHom] (b ⊗ₜ[S,β] m) =
    (ModuleCat.extendScalarsComp β η.toRingHom).hom.app M
      (η b ⊗ₜ[S,η.toRingHom.comp β] m)
  rw [extendScalarsComp_hom_tmul]
  have h : b ⊗ₜ[S,β] m = b • ((1 : K) ⊗ₜ[S,β] m) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [h, TensorProduct.tmul_smul]
  change (η b * (1 : G)) ⊗ₜ[K,η.toRingHom] ((1 : K) ⊗ₜ[S,β] m) =
    η b ⊗ₜ[K,η.toRingHom] ((1 : K) ⊗ₜ[S,β] m)
  rw [mul_one]

/-- The inverse uses the inverse ACTUAL coefficient-ring map. -/
theorem scalarExtensionRingEquivComponent_inv_tmul
    (β : S →+* K) (η : K ≃+* G) (M : ModuleCat.{u} S) (g : G) (m : M) :
    (scalarExtensionRingEquivComponent β η M).inv
      (g ⊗ₜ[S,η.toRingHom.comp β] m) = η.symm g ⊗ₜ[S,β] m := by
  apply (scalarExtensionRingEquivComponent β η M).toLinearEquiv.symm_apply_eq.mpr
  change g ⊗ₜ[S,η.toRingHom.comp β] m =
    (scalarExtensionRingEquivComponent β η M).hom (η.symm g ⊗ₜ[S,β] m)
  simpa only [η.apply_symm_apply] using
    (scalarExtensionRingEquivComponent_hom_tmul β η M (η.symm g) m).symm

/-- Explicit naturality on the ORIGINAL coefficient morphism. -/
theorem scalarExtensionRingEquivIso_naturality
    (β : S →+* K) (η : K ≃+* G) {M N : ModuleCat.{u} S} (φ : M ⟶ N) :
    (ModuleCat.extendScalars β).map φ ≫ (scalarExtensionRingEquivIso β η).hom.app N =
      (scalarExtensionRingEquivIso β η).hom.app M ≫
        (ModuleCat.restrictScalars η.toRingHom).map
          ((ModuleCat.extendScalars (η.toRingHom.comp β)).map φ) :=
  (scalarExtensionRingEquivIso β η).hom.naturality φ

end RingEquivalence

/-- Gamma-Spec specialization with the ORIGINAL native ring object K. This
works for any commutative ring; no Field dictionary is reconstructed. -/
def gammaScalarExtensionIso {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K) :
    (ModuleCat.extendScalars β : ModuleCat.{u} S ⥤ ModuleCat.{u} K) ≅
      (ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β) :
        ModuleCat.{u} S ⥤ ModuleCat.{u} Γ(Spec K, ⊤)) ⋙
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom :
          ModuleCat.{u} Γ(Spec K, ⊤) ⥤ ModuleCat.{u} K) :=
  scalarExtensionRingEquivIso β (Scheme.ΓSpecIso K).symm.commRingCatIsoToRingEquiv

/-- Generic field consumer ABI requested by L1, with no beta-flatness. -/
def fieldGammaScalarExtensionIso {S κ : Type u} [CommRing S] [Field κ]
    (β : S →+* κ) :
    (ModuleCat.extendScalars β : ModuleCat.{u} S ⥤ ModuleCat.{u} κ) ≅
      (ModuleCat.extendScalars ((Scheme.ΓSpecIso (.of κ)).inv.hom.comp β) :
        ModuleCat.{u} S ⥤ ModuleCat.{u} Γ(Spec (.of κ), ⊤)) ⋙
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of κ)).inv.hom :
          ModuleCat.{u} Γ(Spec (.of κ), ⊤) ⥤ ModuleCat.{u} κ) :=
  gammaScalarExtensionIso (.of κ) β

/-- The forward Gamma map is exactly the required Gamma-Spec inverse. -/
theorem gammaScalarExtensionIso_hom_tmul {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K) (M : ModuleCat.{u} S) (b : K) (m : M) :
    (gammaScalarExtensionIso K β).hom.app M (b ⊗ₜ[S,β] m) =
      (Scheme.ΓSpecIso K).inv b ⊗ₜ[S,(Scheme.ΓSpecIso K).inv.hom.comp β] m :=
  scalarExtensionRingEquivComponent_hom_tmul β
    (Scheme.ΓSpecIso K).symm.commRingCatIsoToRingEquiv M b m

/-- The inverse Gamma map is exactly the required Gamma-Spec hom. -/
theorem gammaScalarExtensionIso_inv_tmul {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K) (M : ModuleCat.{u} S)
    (g : Γ(Spec K, ⊤)) (m : M) :
    (gammaScalarExtensionIso K β).inv.app M
      (g ⊗ₜ[S,(Scheme.ΓSpecIso K).inv.hom.comp β] m) =
        (Scheme.ΓSpecIso K).hom g ⊗ₜ[S,β] m :=
  scalarExtensionRingEquivComponent_inv_tmul β
    (Scheme.ΓSpecIso K).symm.commRingCatIsoToRingEquiv M g m

/-- L2 already fixes beta_s. Cancelling ONLY the target Gamma-Spec isomorphism
proves the genuinely missing literal raw-to-Gamma residue ring triangle. -/
theorem residueScalar_gamma_triangle (S : Type u) [CommRing S] (s : Spec (.of S)) :
    (Scheme.ΓSpecIso ((Spec (.of S)).residueField s)).inv.hom.comp
        (L2.nativeResidueScalarMap S s) =
      ((Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop).hom := by
  let K := (Spec (.of S)).residueField s
  have categoryTriangle :
      L2.nativeResidueRingMap S s ≫ (Scheme.ΓSpecIso K).inv =
        (Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop := by
    change ((Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop ≫
      (Scheme.ΓSpecIso K).hom) ≫ (Scheme.ΓSpecIso K).inv =
        (Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom categoryTriangle

/-- Thin residue specialization: original beta_s/residue dictionary reused;
the target is the ACTUAL Gamma-valued native residue map. -/
def residueGammaScalarExtensionIso (S : Type u) [CommRing S] (s : Spec (.of S)) :
    (ModuleCat.extendScalars (L2.nativeResidueScalarMap S s) :
      ModuleCat.{u} S ⥤ ModuleCat.{u} ((Spec (.of S)).residueField s)) ≅
      (ModuleCat.extendScalars
        ((Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop).hom :
        ModuleCat.{u} S ⥤ ModuleCat.{u} Γ(Spec ((Spec (.of S)).residueField s), ⊤)) ⋙
          (ModuleCat.restrictScalars (Scheme.ΓSpecIso ((Spec (.of S)).residueField s)).inv.hom :
            ModuleCat.{u} Γ(Spec ((Spec (.of S)).residueField s), ⊤) ⥤
              ModuleCat.{u} ((Spec (.of S)).residueField s)) :=
  gammaScalarExtensionIso ((Spec (.of S)).residueField s) (L2.nativeResidueScalarMap S s) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (congrArg ModuleCat.extendScalars (residueScalar_gamma_triangle S s)))
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso ((Spec (.of S)).residueField s)).inv.hom)

end ZInQ.Contrib.CloudR2Poincare.L5.ScalarFibre20261115
