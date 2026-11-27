import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.FiniteExceptionalFibers
import ZInQKernel.Contrib.OneProof.SGA3NbhdDVR

/-! # Open fiberwise identity component from a good open of the same model

Stacks 37.27.5 (Tag 0559) gives a nonempty open of geometrically irreducible fibers
for a finite-type morphism over an irreducible base when its generic fiber is
geometrically irreducible. This module receives the ordinary preconnected-fibers
consequence on such an open; it does not postulate potential semistability or a
replacement model.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CToPrinted

namespace ZInQ.Contrib.IsogenyDegree

/-- The finite-exception proof of openness on the original model. -/
theorem isOpen_idCompSet_of_preconnected_on_open {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.DimensionLEOne R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom]
    (U : Set (PrimeSpectrum R)) (hU : IsOpen U) (hne : U.Nonempty)
    (hc : ∀ s ∈ U, _root_.IsPreconnected (G.hom ⁻¹' {s})) : IsOpen (idCompSet G) := by
  obtain ⟨f, -, hsub, hfinite, hclosed⟩ := exists_basicOpen_with_finite_closed_exception hU hne
  let T : Set (PrimeSpectrum R) := (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R))ᶜ
  exact SGA3Nbhd.isOpen_idCompSet_of_finite G T hfinite hclosed fun s hs =>
    hc s (hsub (not_not.mp (show ¬ s ∉ PrimeSpectrum.basicOpen f from hs)))

#print axioms isOpen_idCompSet_of_preconnected_on_open

end ZInQ.Contrib.IsogenyDegree
