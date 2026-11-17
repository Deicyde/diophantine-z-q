/-
H5 lane3 Step 2, B1 KEY (L1.b) `ComapLocalizationIso` (L1Plan.lean 8272a66b) PROVED from Mathlib,
plus ONE small point-compatibility obligation. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.
Universe u.

Construction:
* `V := φ ''ᵁ U`, affine by `image_of_isOpenImmersion`.
* `ψ : Γ(U) ≃+* Γ(V)`, from `(φ.appIso U).symm`.
* `q := p.comap ψ.symm`, the prime of `Γ(V)` over `p`.
* (L0) Mathlib `ideal_comap_of_isOpenImmersion`: `(I.comap φ).ideal U = (I.ideal V).comap ψ`.
* `ρ := IsLocalization.ringEquivOfRingEquiv … ψ`, where `p.primeCompl.map ψ = q.primeCompl`. It
  satisfies `ρ ∘ loc_p = loc_q ∘ ψ`, so `ρ (loc_p ((I V).comap ψ)) = loc_q (I V)`. The step
  `ψ ((I V).comap ψ) = I V` holds because `ψ` is surjective (`Ideal.map_comap_of_surjective`).

Small obligation (TRUE), `FromSpecImageCompat`: `V.fromSpec q = φ (U.fromSpec p)`. Both points are
the image of `p` under `Spec Γ(U) ≅ U ≅ φU ≅ Spec Γ(V)`, and the iso of global sections induced
by `φ` is `ψ` (`Scheme.Hom.appIso`, `IsAffineOpen.fromSpec` naturality).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.L1a

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

/-- (TRUE) The chart point of the image open. -/
def FromSpecImageCompat : Prop :=
  ∀ {X : Scheme.{u}} (φ : X ⟶ X) [IsIso φ] (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U.1)),
    (U.2.image_of_isOpenImmersion φ).fromSpec
        (PrimeSpectrum.comap (φ.appIso U.1).hom.hom p) = φ (U.2.fromSpec p)

theorem comapLocalizationIso (hFS : FromSpecImageCompat.{u}) : ComapLocalizationIso.{u} := by
  intro X I φ _ U p
  let V : X.affineOpens := ⟨φ ''ᵁ U.1, U.2.image_of_isOpenImmersion φ⟩
  let ψ : Γ(X, U.1) ≃+* Γ(X, V.1) := (φ.appIso U.1).symm.commRingCatIsoToRingEquiv
  let q : PrimeSpectrum Γ(X, V.1) := PrimeSpectrum.comap (φ.appIso U.1).hom.hom p
  refine ⟨V, q, hFS φ U p, ?_⟩
  -- the primes correspond under `ψ`
  have hq : q.asIdeal = p.asIdeal.comap ψ.symm.toRingHom := rfl
  have hM : p.asIdeal.primeCompl.map ψ.toRingHom.toMonoidHom = q.asIdeal.primeCompl := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      change ψ.symm (ψ t) ∉ p.asIdeal
      simpa using ht
    · intro hs
      refine ⟨ψ.symm s, ?_, by simp⟩
      exact hs
  let ρ : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) ψ hM
  have hρ : ∀ r : Γ(X, U.1), ρ (algebraMap _ _ r) = algebraMap _ (Localization.AtPrime q.asIdeal)
      (ψ r) := fun r => IsLocalization.ringEquivOfRingEquiv_eq hM r
  refine ⟨ρ, ?_⟩
  -- (L0)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I φ U]
  change Ideal.map ρ (Ideal.map (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal))
      ((I.ideal V).comap ψ.toRingHom)) = _
  rw [Ideal.map_map]
  have hcomp : (ρ : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal).comp
      (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal)) =
        (algebraMap Γ(X, V.1) (Localization.AtPrime q.asIdeal)).comp ψ.toRingHom := by
    ext r
    exact hρ r
  rw [hcomp, ← Ideal.map_map, Ideal.map_comap_of_surjective _ ψ.surjective]

end ZInQ.Contrib.CloudR2NOS.Step2B1
