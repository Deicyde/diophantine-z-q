-- The affine-complement proof is adapted from frenzymath/Jacobian-Challenge
-- (c4254cce15b3e284a0a3ae1d73936f2ee195d272), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu.
-- See LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- The adaptation proves invertibility of the specified reduced ideal.

import ZInQKernel.Contrib.OneProof.NeronDVR.InvariantComplement
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.AffineComplement
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Regular

/-!
# Invariant Cartier complements over DVRs

The reduced complement of a nonempty invariant affine open is an effective
Cartier divisor with equal ideal sheaf pullbacks along the two overlap maps.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

universe schemeUniverse

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 3 in
/-- The reduced complement of a nonempty affine open in an integral,
locally factorial noetherian separated scheme is effective Cartier. -/
theorem Scheme.isInvertible_vanishingIdeal_compl_of_isAffineOpen
    (source : Scheme.{schemeUniverse}) [IsNoetherian source]
    [source.IsSeparated] [IsIntegral source]
    (hX : ∀ point : source, UniqueFactorizationMonoid (source.presheaf.stalk point))
    {openSubset : source.Opens} (hU : IsAffineOpen openSubset)
    (hne : (openSubset : Set source).Nonempty) :
    (IdealSheafData.vanishingIdeal
      ⟨(openSubset : Set source)ᶜ, openSubset.isOpen.isClosed_compl⟩).IsInvertible := by
  intro point
  obtain ⟨targetOpen, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := point) (U := ⊤) trivial
  have : Nonempty targetOpen := ⟨⟨point, hxV⟩⟩
  have : IsAffineHom hV.fromSpec := IsAffineHom.of_comp hV.fromSpec (Limits.terminal.from source)
  have hWne : (hV.fromSpec ⁻¹ᵁ openSubset : Set (Spec Γ(source, targetOpen))).Nonempty := by
    obtain ⟨sourcePoint, hzU, hzV⟩ := nonempty_preirreducible_inter openSubset.isOpen targetOpen.isOpen hne ⟨point, hxV⟩
    obtain ⟨z', rfl⟩ : sourcePoint ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hzV
    exact ⟨z', hzU⟩
  have := IsLocallyNoetherian.component_noetherian ⟨targetOpen, hV⟩
  let := TopCat.Presheaf.algebra_section_stalk source.presheaf ⟨point, hxV⟩
  have := hV.isLocalization_stalk ⟨point, hxV⟩
  have := hX point
  obtain ⟨generator, hg, denominator, hb, hb0, hgb⟩ := exists_notMem_mul_mem_span_vanishingIdeal_compl Γ(source, targetOpen)
    (hU.preimage hV.fromSpec) hWne (hV.primeIdealOf ⟨point, hxV⟩).asIdeal (source.presheaf.stalk point)
  have hx : point ∈ source.basicOpen generator :=
    (source.mem_basicOpen generator point hxV).mpr (IsLocalization.map_units (source.presheaf.stalk point)
      (M := (hV.primeIdealOf ⟨point, hxV⟩).asIdeal.primeCompl) ⟨generator, hg⟩)
  have : Nonempty (source.basicOpen generator) := ⟨⟨point, hx⟩⟩
  refine ⟨source.affineBasicOpen (U := ⟨targetOpen, hV⟩) generator, hx, ?_⟩
  let := (source.presheaf.map (homOfLE (source.basicOpen_le generator)).op).hom.toAlgebra
  have := hV.isLocalization_basicOpen generator
  have key : (IdealSheafData.vanishingIdeal ⟨(openSubset : Set source)ᶜ, openSubset.isOpen.isClosed_compl⟩).ideal
      (source.affineBasicOpen (U := ⟨targetOpen, hV⟩) generator) =
        Ideal.span {algebraMap Γ(source, targetOpen) Γ(source, source.basicOpen generator) denominator} := by
    rw [← IdealSheafData.map_ideal_basicOpen]
    exact Ideal.map_eq_span_singleton_of_mul_mem_span_singleton generator hb hgb
  rw [key]
  exact Ideal.isRegularPrincipal_span_singleton
    (mem_nonZeroDivisors_of_ne_zero (M₀ := Γ(source, source.basicOpen generator))
      ((map_ne_zero_iff _ (map_injective_of_isIntegral source _)).mpr hb0))

end AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

universe u

/-- Over a smooth cover, the affine open of a smooth integral model over a
DVR determines an invariant effective Cartier divisor by taking its reduced
complement. -/
theorem exists_invariant_effectiveCartier_of_affine_open
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {S : Scheme.{u}} {p : Spec (CommRingCat.of R) ⟶ S} [Smooth p]
    {G : Over (Spec (CommRingCat.of R))} [Smooth G.hom] [IsNoetherian G.left]
    [G.left.IsSeparated] [IsIntegral G.left] (d : DescentDatum p G)
    {U : G.left.Opens} (hinv : d.IsInvariant U) (hU : IsAffineOpen U)
    (hne : (U : Set G.left).Nonempty) :
    ∃ D : G.left.IdealSheafData, D.IsInvertible ∧ D.support.compl = U ∧
      D.comap d.toHom = D.comap (pullback.fst (G.hom ≫ p) p) := by
  let D := Scheme.IdealSheafData.vanishingIdeal
    ⟨(U : Set G.left)ᶜ, U.isOpen.isClosed_compl⟩
  have : IsRegular G.left :=
    ⟨ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
      R G.hom⟩
  have hD : D.IsInvertible := G.left.isInvertible_vanishingIdeal_compl_of_isAffineOpen
    IsRegular.uniqueFactorizationMonoid_stalk hU hne
  refine ⟨D, hD, ?_, d.comap_vanishingIdeal_compl_eq hinv⟩
  ext x
  change x ∉ (D.support : Set G.left) ↔ x ∈ (U : Set G.left)
  simp [D, Scheme.IdealSheafData.coe_support_vanishingIdeal]

end CategoryTheory.Over.DescentDatum
