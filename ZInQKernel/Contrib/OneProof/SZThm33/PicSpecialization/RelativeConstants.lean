import ZInQKernel.Contrib.OneProof.NeronDVR.RelativePicard
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.GlobalSections.Proper

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.ToricOrthogonality

/-- A section and an integral model with proper geometrically integral
generic fibre force all global functions on the model to come from its DVR. -/
theorem appTop_bijective_of_proper_generic
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of R)) (s : Spec (.of R) ⟶ X) (hs : s ≫ f = 𝟙 _)
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    [GeometricallyIntegral (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    Function.Bijective f.appTop := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let p := pullback.fst f j
  let r := pullback.snd f j
  let w := pullback.lift (j ≫ s) (𝟙 _) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have hwp : w ≫ p = j ≫ s := pullback.lift_fst _ _ _
  have hwr : w ≫ r = 𝟙 _ := pullback.lift_snd _ _ _
  have hsTop (a : Γ(Spec (.of R), ⊤)) : s.appTop (f.appTop a) = a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
    rfl
  have hwTop (a : Γ(Spec (.of K), ⊤)) : w.appTop (r.appTop a) = a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hwr, Scheme.Hom.id_appTop]
    rfl
  refine ⟨Function.LeftInverse.injective hsTop, ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let D := X.basicOpen (NeronDVR.GenericFrame.pullbackParameter f π)
  obtain ⟨e, he⟩ := NeronDVR.GenericFrame.exists_iso_genericBasicOpen (K := K) f hπ
  change e.hom ≫ D.ι = p at he
  have hD : Nonempty D := by
    obtain ⟨a⟩ : Nonempty (Spec (.of K)) := inferInstance
    have hpt : D.ι (e.hom (w a)) ∈ D.ι ''ᵁ (⊤ : D.toScheme.Opens) := ⟨_, trivial, rfl⟩
    rw [D.ι_image_top] at hpt
    exact ⟨⟨_, hpt⟩⟩
  have hD' : Nonempty (D.ι ''ᵁ (⊤ : D.toScheme.Opens) : X.Opens) := D.ι_image_top.symm ▸ hD
  have hι : Function.Injective D.ι.appTop := by
    rw [Scheme.Opens.ι_appTop]
    exact map_injective_of_isIntegral X _
  have hp : Function.Injective p.appTop := by
    intro a b hab
    apply hι
    rw [← he, Scheme.Hom.comp_appTop] at hab
    have hinv (c : Γ(D.toScheme, ⊤)) : e.inv.appTop (e.hom.appTop c) = c := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
      rfl
    simpa only [CommRingCat.comp_apply, hinv] using congrArg (fun a => e.inv.appTop a) hab
  intro a
  refine ⟨s.appTop a, hp ?_⟩
  have hrp : p ≫ f = r ≫ j := pullback.condition
  have hη : Function.Surjective r.appTop :=
    (bijective_appTop_of_isProper_of_geometricallyIntegral r).2
  have hw_id (c : Γ(pullback f j, ⊤)) : r.appTop (w.appTop c) = c := by
    obtain ⟨d, rfl⟩ := hη c
    rw [hwTop]
  have hsec : j.appTop (s.appTop a) = w.appTop (p.appTop a) := by
    simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hwp]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hrp, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, hsec, hw_id]

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.appTop_bijective_of_proper_generic
