/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten.
Released under Apache 2.0 license as described in LICENSE in this directory.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Selected and adapted from chrisflav/oka at
9a9fc315498d58484ac1abc9668548212eb7c1ff:
Oka/AlgebraicGeometry/Modules/QuasicoherentSections.lean, lines 69–131,
Oka/AlgebraicGeometry/Modules/CocycleTwist.lean, elementary restriction lemmas,
and Oka/AlgebraicGeometry/Modules/Tilde.lean, section-localization wrapper.
Changes: isolate names; keep only quasi-coherent denominator clearing;
replace the Oka wrapper with actual Mathlib tilde-Gamma localization.
No Oka parser or notation declarations are copied.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

section Restrictions
variable {X : Scheme.{u}} (M : X.Modules) {V W W' : X.Opens}

lemma mres_res (h : W ≤ V) (h' : W' ≤ W) (x : Γ(M, V)) :
    TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen x W h) W' h' =
      TopCat.Presheaf.restrictOpen x W' (h'.trans h) :=
  TopCat.Presheaf.restrict_restrict _ _ _

lemma mres_self (x : Γ(M, V)) : TopCat.Presheaf.restrictOpen x V le_rfl = x :=
  TopCat.Presheaf.restrict_self _

lemma mres_smul (h : W ≤ V) (r : Γ(X, V)) (x : Γ(M, V)) :
    TopCat.Presheaf.restrictOpen (r • x) W h =
      TopCat.Presheaf.restrictOpen r W h • TopCat.Presheaf.restrictOpen x W h := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

lemma ores_res (h : W ≤ V) (h' : W' ≤ W) (r : Γ(X, V)) :
    TopCat.Presheaf.restrictOpen (TopCat.Presheaf.restrictOpen r W h) W' h' =
      TopCat.Presheaf.restrictOpen r W' (h'.trans h) :=
  TopCat.Presheaf.restrict_restrict _ _ _

lemma ores_pow (h : W ≤ V) (r : Γ(X, V)) (k : ℕ) :
    TopCat.Presheaf.restrictOpen (r ^ k) W h =
      TopCat.Presheaf.restrictOpen r W h ^ k := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

end Restrictions

/-- Restriction of Spec-sections as the actual R-linear map from Mathlib. -/
abbrev specSectionsToBasicOpen {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R) :=
  (modulesSpecToSheaf.obj M).presheaf.map
    (homOfLE (le_top : (PrimeSpectrum.basicOpen f : (Spec R).Opens) ≤ ⊤)).op

/-- Quasi-coherent Spec-sections genuinely localize, by the existing tilde-Gamma theorem. -/
theorem specSections_isLocalized {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f) (specSectionsToBasicOpen M f).hom := by
  exact (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance f

section AffineOpen
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (F : X.Modules)

lemma fromSpec_image_le (W : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ W ≤ U :=
  (hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le

lemma le_fromSpec_image_top : U ≤ hU.fromSpec ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

lemma fromSpec_appIso_hom_restrict (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso W).hom (X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r) =
      (Spec Γ(X, U)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r) := by
  rw [Scheme.Hom.appIso_hom, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, hU.fromSpec_app_of_le U le_rfl]
  simp only [Category.assoc, ← Functor.map_comp, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

lemma smul_restrict_fromSpec (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (x : Γ(F.restrict hU.fromSpec, W)) :
    (r • x : Γ(F.restrict hU.fromSpec, W)) = (show Γ(F, hU.fromSpec ''ᵁ W) from
      TopCat.Presheaf.restrictOpen r _ (fromSpec_image_le hU W) •
        (show Γ(F, hU.fromSpec ''ᵁ W) from x)) := by
  rw [Scheme.Modules.smul_Spec_def]
  change _ = X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r • _
  rw [← fromSpec_appIso_hom_restrict hU]
  change ((hU.fromSpec.appIso W).inv ((hU.fromSpec.appIso W).hom _)) •
    (show Γ(F, hU.fromSpec ''ᵁ W) from x) = _
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply]

include hU in
/-- Actual quasi-coherent sections on an arbitrary affine open clear denominators.
This adds no localization premise: it is derived from the native QC module itself. -/
theorem exists_restrictOpen_eq_pow_smul [F.IsQuasicoherent]
    (f : Γ(X, U)) (s : Γ(F, X.basicOpen f)) :
    ∃ (k : ℕ) (t : Γ(F, U)), TopCat.Presheaf.restrictOpen t (X.basicOpen f) (X.basicOpen_le f) =
      TopCat.Presheaf.restrictOpen f (X.basicOpen f) (X.basicOpen_le f) ^ k • s := by
  have hW := hU.fromSpec_image_basicOpen f
  letI := specSections_isLocalized (F.restrict hU.fromSpec) f
  let s' : Γ(F, hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f) :=
    TopCat.Presheaf.restrictOpen s _ hW.le
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (specSectionsToBasicOpen (F.restrict hU.fromSpec) f).hom s'
  refine ⟨k, TopCat.Presheaf.restrictOpen (show Γ(F, hU.fromSpec ''ᵁ ⊤) from a) U
    (le_fromSpec_image_top hU), ?_⟩
  have ha' : TopCat.Presheaf.restrictOpen (show Γ(F, hU.fromSpec ''ᵁ ⊤) from a)
      (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f) (hU.fromSpec.image_mono le_top) =
      TopCat.Presheaf.restrictOpen f (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
        (fromSpec_image_le hU _) ^ k • s' := by
    rw [← ores_pow]
    refine ha.symm.trans ?_
    rw [Submonoid.smul_def]
    exact smul_restrict_fromSpec hU F _ _ _
  refine (mres_res F _ _ _).trans ?_
  refine (mres_res F (hU.fromSpec.image_mono le_top) hW.ge _).symm.trans ?_
  rw [ha', mres_smul, ores_pow, ores_res]
  simp only [s', mres_res, mres_self]

end AffineOpen
end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
