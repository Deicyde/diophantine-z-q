import ZInQKernel.Contrib.OneProof.SZThm33.HenselianEtaleSections
import ZInQKernel.Contrib.OneProof.FaltingsDVR.EtaleSections

/-!
# Lifting points along a henselian valuation ring

A residue-valued point of an étale morphism lifts uniquely to a
point over a henselian local test ring.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SmoothGroup

/-- Lift a point over the residue field through an étale morphism, with
the prescribed map from the henselian local test ring to the base. -/
theorem existsUnique_lift_of_etale_over_residue
    {R : Type} [CommRing R] [HenselianLocalRing R]
    {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (g : Spec (.of R) ⟶ S)
    (z : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hz : z ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ g) :
    ∃! a : Spec (.of R) ⟶ X, a ≫ f = g ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ a = z := by
  let i := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let w := pullback.lift z i hz
  have hw : w ≫ pullback.snd f g = i := pullback.lift_snd _ _ _
  obtain ⟨b, hb, hbi⟩ := exists_section_over_residue_of_etale (pullback.snd f g) w hw
  refine ⟨b ≫ pullback.fst f g, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hb, Category.id_comp]
  · rw [← Category.assoc, hbi, pullback.lift_fst]
  · rintro a ⟨ha, hai⟩
    let c : Spec (.of R) ⟶ pullback f g :=
      pullback.lift a (𝟙 _) (by rwa [Category.id_comp])
    have hc : c ≫ pullback.snd f g = 𝟙 _ := pullback.lift_snd _ _ _
    have hci : i ≫ c = w := by
      apply pullback.hom_ext
      · simpa [w, c] using hai
      · simp [w, c]
    have hcb : c = b := by
      apply section_eq_of_closed_eq (pullback.snd f g) hc hb
      have h := hci.trans hbi.symm
      have hpoint := congrArg (fun x : Spec (.of (IsLocalRing.ResidueField R)) ⟶ pullback f g =>
        x (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) h
      let x := IsLocalRing.closedPoint (IsLocalRing.ResidueField R)
      change c (i x) = b (i x) at hpoint
      have hi : i x = IsLocalRing.closedPoint R := IsLocalRing.PrimeSpectrum.comap_residue R x
      simpa only [hi] using hpoint
    rw [← hcb, pullback.lift_fst]

#print axioms existsUnique_lift_of_etale_over_residue

end SmoothGroup
