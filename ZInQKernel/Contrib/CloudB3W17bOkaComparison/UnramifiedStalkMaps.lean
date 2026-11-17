import ZInQKernel.Contrib.CloudB3W17bOkaComparison.UnramifiedLocalUniqueness

/-!
# Actual unramified regular-ring maps into a local analytic stalk

The proof uses the actual open-diagonal uniqueness theorem on spectra of the
actual rings.  The local target ring may be an analytic stalk.  Its residue
value map is a genuine local homomorphism; it is not an algebraic map from A
to B.  No Krull-intersection, Henselianity or GAGA premise is introduced.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- Two maps from an actual finite-type unramified algebra into a local ring
are equal when they agree on the base and on actual residue values. -/
theorem unramified_local_ringMaps_ext
    {R B S K : Type} [CommRing R] [CommRing B] [CommRing S] [Field K]
    [Algebra R B] [Algebra.FiniteType R B] [Algebra.FormallyUnramified R B]
    [IsLocalRing S] (f g : B →+* S)
    (hb : f.comp (algebraMap R B) = g.comp (algebraMap R B))
    (e : S →+* K) [IsLocalHom e] (he : e.comp f = e.comp g) : f = g := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap R B))
  letI : FormallyUnramified s :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr
      (RingHom.formallyUnramified_algebraMap.mpr inferInstance)
  letI : LocallyOfFiniteType s :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let F := Spec.map (CommRingCat.ofHom f)
  let G := Spec.map (CommRingCat.ofHom g)
  let p := Spec.map (CommRingCat.ofHom e)
  have w : F ≫ s = G ≫ s := by
    change Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hb)
  have h : p ≫ F = p ≫ G := by
    change Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom g)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext he)
  have hp : p (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint S :=
    IsLocalRing.comap_closedPoint e
  have H := formallyUnramified_localSpec_ext s F G w p (IsLocalRing.closedPoint K) hp h
  exact CommRingCat.hom_ext_iff.mp (Spec.map_injective H)

end ZInQ.Contrib.CloudB3W17bOkaComparison
