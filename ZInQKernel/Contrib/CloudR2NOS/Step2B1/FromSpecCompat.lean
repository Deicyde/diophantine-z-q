/-
H5 lane3 Step 2, B1 KEY: `FromSpecImageCompat` (L1b.lean 036834de) PROVED from Mathlib, so (L1.b)
has no remaining obligation. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

Proof: Mathlib `Scheme.Hom.appIso_hom'` gives
`(φ.appIso U).hom = φ.appLE (φ ''ᵁ U) U (preimage_image_eq).ge`. Then
`IsAffineOpen.SpecMap_appLE_fromSpec` gives
`Spec.map (φ.appLE …) ≫ (φU).fromSpec = U.fromSpec ≫ φ`. Evaluate at `p`; on points,
`Spec.map` acts by `PrimeSpectrum.comap`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.L1b

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

theorem fromSpecImageCompat : FromSpecImageCompat.{u} := by
  intro X φ _ U p
  have h := IsAffineOpen.SpecMap_appLE_fromSpec φ (U.2.image_of_isOpenImmersion φ) U.2
    (φ.preimage_image_eq U.1).ge
  have hpt := congrArg (fun g : Spec Γ(X, U.1) ⟶ X => g p) h
  simp only [Scheme.Hom.comp_apply] at hpt
  rw [← Scheme.Hom.appIso_hom'] at hpt
  exact hpt

/-- (L1.b) with no remaining obligation. -/
theorem comapLocalizationIso_proved : ComapLocalizationIso.{u} :=
  comapLocalizationIso fromSpecImageCompat

end ZInQ.Contrib.CloudR2NOS.Step2B1
