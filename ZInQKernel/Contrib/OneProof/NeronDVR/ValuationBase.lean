import Mathlib.RingTheory.Valuation.ValuationRing
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.OneProof.NeronDVR.MappingDescent
import ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists

/-!
# Presenting a DVR as a valuation subring

The strict henselization machinery works with valuation subrings of fields.
An arbitrary DVR with a specified fraction field is isomorphic to its image
valuation subring. Transporting the model across this isomorphism preserves
the specified generic fibre.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronDVR

open ZInQ.Contrib.GroupLawNeron

private theorem model_of_ringEquiv
    {R O K : Type} [CommRing R] [IsDomain R] [CommRing O] [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra O K]
    (e : R ≃+* O) (hRing : (algebraMap O K).comp e.toRingHom = algebraMap R K)
    (N : Over (Spec (CommRingCat.of O))) (hN : CToPrinted.IsNeronModelOver O K N)
    (A : Over (Spec (CommRingCat.of K))) (ε : (Over.pullback (genMap O K)).obj N ≅ A) :
    ∃ M : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K M ∧
      Nonempty ((Over.pullback (genMap R K)).obj M ≅ A) := by
  let s := Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso s := isIso_SpecMap_iff.mpr e.bijective
  have hs : genMap O K ≫ s = genMap R K := by
    change Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) = Spec.map (CommRingCat.ofHom (algebraMap R K))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hRing]
  have hpb : IsPullback (genMap O K) (𝟙 _) s (genMap R K) :=
    IsPullback.of_vert_isIso ⟨by simpa only [Category.id_comp] using hs⟩
  let M := Over.mk (N.hom ≫ s)
  let i : (Over.pullback s).obj M ≅ N := NeronExt.pbMapIso s N
  have hM : CToPrinted.IsNeronModelOver R K M :=
    isNeronModelOver_of_fpqc (R := R) (R' := O) (K := K) (K' := K)
      s (𝟙 _) hpb M (NeronExt.isNeronModelOver_of_iso i hN)
  exact ⟨M, hM, ⟨NeronExt.pbCongr hs.symm M ≪≫ (Over.pullbackComp (genMap O K) s).app M ≪≫
    (Over.pullback (genMap O K)).mapIso i ≪≫ ε⟩⟩

/-- It suffices to construct local Néron models for DVRs presented as valuation
subrings of their fraction fields. -/
theorem neronSchemeExtensionDVR_of_valuationSubring
    (h : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (A : PkgI3.AbVar K),
      ∃ N : Over (Spec (CommRingCat.of O)),
        CToPrinted.IsNeronModelOver O K N ∧
          Nonempty ((Over.pullback (genMap O K)).obj N ≅ A.X)) :
    NeronSchemeExtensionDVR := by
  intro R _ _ _ K _ _ _ A
  let O := (ValuationRing.valuation R K).valuationSubring
  let e : R ≃+* O := ValuationRing.equivInteger R K
  have : IsDiscreteValuationRing O := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hRing : (algebraMap O K).comp e.toRingHom = algebraMap R K :=
    RingHom.ext (ValuationRing.coe_equivInteger_apply R K)
  obtain ⟨N, hN, ⟨ε⟩⟩ := h K O A
  obtain ⟨M, ⟨hsm, hsep, _, hqc, hext⟩, ⟨εM⟩⟩ := model_of_ringEquiv e hRing N hN A.X ε
  refine ⟨M, hsm, hsep, hqc, εM, fun Y _ f => ?_⟩
  obtain ⟨g, hg⟩ := (hext Y).surjective (f ≫ εM.inv)
  refine ⟨g, ?_⟩
  change (Over.pullback (genMap R K)).map g = f ≫ εM.inv at hg
  change (Over.pullback (genMap R K)).map g ≫ εM.hom = f
  rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end NeronDVR
