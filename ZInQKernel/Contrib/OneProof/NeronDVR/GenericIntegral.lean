import ZInQKernel.Contrib.NeronC.NMPInjective

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace NeronDVR

/-- A flat scheme over a domain is integral if its generic fibre is integral. -/
theorem isIntegral_of_integral_generic_fibre
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsIntegral X := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsSchemeTheoreticallyDominant j :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _ (IsFractionRing.injective R K)
  have : QuasiCompact j := show QuasiCompact (Spec.map _) by infer_instance
  let i := pullback.fst f j
  have : QuasiCompact i := show QuasiCompact (pullback.fst f j) by infer_instance
  have : IsSchemeTheoreticallyDominant i :=
    show IsSchemeTheoreticallyDominant (pullback.fst f j) by infer_instance
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨irreducibleSpace_def X |>.mpr ?_, IsSchemeTheoreticallyDominant.isReduced i⟩
  have h : IsIrreducible (Set.range i) := by
    let Z : Scheme.{u} := pullback f j
    have himage := (IrreducibleSpace.isIrreducible_univ (↥Z)).image
      (fun z : Z => i z) i.continuous.continuousOn
    rwa [Set.image_univ] at himage
  change IsIrreducible (Set.univ : Set X)
  simpa only [i.denseRange.closure_eq] using h.closure

end NeronDVR
