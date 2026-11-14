import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace ZariskiConn

/-- `Spec K → Spec R` is scheme-theoretically dominant for an injective `R → K`, `R` a domain. -/
theorem isSchemeTheoreticallyDominant_Spec_map {R K : Type} [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] (h : Function.Injective (algebraMap R K)) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := algebraMap R K)).2 ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).1 h]
    exact bot_le
  exact .of_isDominant _

/-- **Global sections of a flat universally closed scheme over an integrally closed domain.**
Let `R` be an integrally closed domain with fraction field `K` and `p : X ⟶ Spec R` flat and
universally closed, with geometrically integral generic fibre. Then `R → Γ(X, 𝒪_X)` is
bijective. -/
theorem appTop_bijective_of_generic {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{0}} (p : X ⟶ Spec (.of R))
    [Flat p] [UniversallyClosed p]
    [GeometricallyIntegral (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    Function.Bijective ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) := by
  set ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have := isSchemeTheoreticallyDominant_Spec_map hinj
  let P : Scheme := pullback p ι
  let _ : P.Over (Spec (.of K)) := ⟨pullback.snd p ι⟩
  have : UniversallyClosed (P ↘ Spec (.of K)) := by
    change UniversallyClosed (pullback.snd p ι); infer_instance
  have : GeometricallyIntegral (P ↘ Spec (.of K)) := by
    change GeometricallyIntegral (pullback.snd p ι); infer_instance
  have hK := Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral P K
  -- the injection `Γ(X) → Γ(X_K)`
  have hj : Function.Injective (pullback.fst p ι).appTop :=
    (pullback.fst p ι).app_injective ⊤
  set φ := ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom with hφ
  set ψ := Scheme.Modules.baseRingToGlobalSections K P with hψ
  set j := (pullback.fst p ι).appTop.hom with hjdef
  have hcomm : ∀ r : R, j (φ r) = ψ (algebraMap R K r) := by
    intro r
    have h1 : (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫ (pullback.fst p ι).appTop =
        CommRingCat.ofHom (algebraMap R K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
          (pullback.snd p ι).appTop := by
      rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
        ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    exact congrArg (fun g => g.hom r) h1
  have hφint : φ.IsIntegral := by
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
      (isIntegral_appTop_of_universallyClosed p)
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · apply hinj; apply hK.1
    rw [← hcomm, ← hcomm, hab]
  · obtain ⟨c, hc⟩ := hK.2 (j b)
    -- `c` is integral over `R`
    obtain ⟨q, hqm, hq⟩ := hφint b
    have hcint : IsIntegral R c := by
      refine ⟨q, hqm, hK.1 ?_⟩
      rw [map_zero, Polynomial.hom_eval₂, hc]
      have : (ψ.comp (algebraMap R K)) = j.comp φ := by ext r; exact (hcomm r).symm
      rw [this, ← Polynomial.hom_eval₂, hq, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hcint
    refine ⟨r, hj ?_⟩
    change j (φ r) = j b
    rw [hcomm, hr, hc]

end ZariskiConn
