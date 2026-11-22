import ZInQKernel.Contrib.OneProof.NeronDVR.StableOpen
import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Geometrically.Smooth

/-!
# Invariant reduced closed complements

Smooth pullback preserves the reduced subscheme of a closed set. Thus the
complement of an invariant open has a canonical compatible ideal sheaf,
when the covering map is smooth and the schemes are locally noetherian.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false in
private theorem radical_eq_of_isReduced_subscheme {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] : I.radical = I := by
  rw [← I.ker_subschemeι]
  ext U : 2
  rw [radical_ideal, Scheme.Hom.ker_apply]
  refine Ideal.radical_eq_iff.mpr ?_
  intro z hz
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hz
  apply RingHom.mem_ker.mpr
  exact (show IsNilpotent (I.subschemeι.app U z) from
    ⟨n, by rw [← map_pow]; exact RingHom.mem_ker.mp hn⟩).eq_zero

set_option backward.isDefEq.respectTransparency false in
/-- The formation of the reduced induced subscheme commutes with smooth pullback. -/
theorem comap_vanishingIdeal_of_smooth {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Smooth f] (Z : Closeds Y) :
    (vanishingIdeal Z).comap f = vanishingIdeal (Z.preimage f.continuous) := by
  let I := vanishingIdeal Z
  have : IsReduced I.subscheme := isReduced_subscheme_vanishingIdeal Z
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : IsReduced (I.comap f).subscheme := isReduced_of_isOpenImmersion (I.comapIso f).hom
  have hs : I.support = Z := Closeds.ext (coe_support_vanishingIdeal Z)
  calc
    I.comap f = (I.comap f).radical := (radical_eq_of_isReduced_subscheme _).symm
    _ = vanishingIdeal (I.comap f).support := vanishingIdeal_support.symm
    _ = vanishingIdeal (Z.preimage f.continuous) := by rw [support_comap, hs]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace CategoryTheory.Over.DescentDatum

set_option backward.isDefEq.respectTransparency false in
/-- The ideal of the reduced complement is invariant under smooth descent. -/
theorem comap_vanishingIdeal_compl_eq {S S' : Scheme.{u}} {p : S' ⟶ S} [Smooth p]
    {X : Over S'} [IsLocallyNoetherian X.left] (d : DescentDatum p X)
    {U : X.left.Opens} (hU : d.IsInvariant U) :
    let I := Scheme.IdealSheafData.vanishingIdeal
      ⟨(U : Set X.left)ᶜ, U.isOpen.isClosed_compl⟩
    I.comap d.toHom = I.comap (pullback.fst (X.hom ≫ p) p) := by
  have : Smooth d.toHom := d.smooth_toHom
  simp only [Scheme.IdealSheafData.comap_vanishingIdeal_of_smooth]
  congr 1
  apply Closeds.ext
  simp only [Closeds.coe_preimage]
  exact congrArg Set.compl (congrArg SetLike.coe (d.preimage_toHom_eq hU))

end CategoryTheory.Over.DescentDatum
