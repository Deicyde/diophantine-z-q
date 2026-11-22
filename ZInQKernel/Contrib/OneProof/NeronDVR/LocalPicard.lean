import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Field

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Modules

/-- An invertible module over the spectrum of a local ring trivializes
on an open containing its closed point, which is the entire spectrum. -/
theorem Modules.nonempty_iso_unit_spec_localRing
    (R : Type u) [CommRing R] [IsLocalRing R] (L : (Spec (CommRingCat.of R)).Modules)
    [hL : L.IsInvertible] : Nonempty (L ≅ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) := by
  let S := Spec (CommRingCat.of R)
  obtain ⟨U, hc, ⟨e⟩⟩ := hL.exists_isoUnit (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun x _ => by
    have hx : x ⤳ IsLocalRing.closedPoint R :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
    exact hx.mem_open U.isOpen hc
  exact ⟨((pullbackId S).app L).symm ≪≫
    (pullbackCongr (Scheme.toIso_inv_ι S).symm).app L ≪≫
    (pullbackComp _ _).symm.app L ≪≫
    (pullback S.topIso.inv).mapIso e ≪≫ pullbackObjUnitIso _⟩

/-- The Picard group of the spectrum of a local ring is trivial. -/
theorem Pic.subsingleton_spec_localRing (R : Type u) [CommRing R] [IsLocalRing R] :
    Subsingleton (Spec (CommRingCat.of R)).Pic := by
  let S := Spec (CommRingCat.of R)
  refine ⟨fun L L' => Pic.eq_iff_nonempty_iso.2 ?_⟩
  obtain ⟨e⟩ := Modules.nonempty_iso_unit_spec_localRing R ((fromSkeleton S.Modules).obj L.val)
  obtain ⟨e'⟩ := Modules.nonempty_iso_unit_spec_localRing R ((fromSkeleton S.Modules).obj L'.val)
  exact ⟨e ≪≫ e'.symm⟩

end AlgebraicGeometry.Scheme
