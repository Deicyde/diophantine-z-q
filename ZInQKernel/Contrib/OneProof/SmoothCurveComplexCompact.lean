import ZInQKernel.Contrib.OneProof.Y3InvariantAffine
import ZInQKernel.Contrib.CloudB3W17ProperCompact.NativeCompact

/-! The native complex points of any smooth proper curve are compact. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

/-- Compactness of the complex points of a smooth proper curve, including
a curve with several connected components. -/
theorem compactSpace_complexPoint_of_proper_smooth
    (X : Over (Spec (CommRingCat.of ℂ))) [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom] : CompactSpace (ComplexPoint X) := by
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherian X.left := {}
  let C := irreducibleComponents X.left
  have : Finite C := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let V (c : C) : X.left.Opens :=
    ⟨c.val, by
      obtain ⟨x, hx⟩ := c.property.1.nonempty
      have hc : c.val = irreducibleComponent x := CurveSplit.components_disjoint X.hom _ c.property _
        (irreducibleComponent_mem_irreducibleComponents x) ⟨x, hx, mem_irreducibleComponent⟩
      rw [hc]
      exact CurveSplit.isOpen_irreducibleComponent X.hom x⟩
  let Y (c : C) := Over.mk ((V c).ι ≫ X.hom)
  let i (c : C) : Y c ⟶ X := Over.homMk (V c).ι rfl
  have hc (c : C) : IsCompact (Set.range (Point.map (R := ℂ) (i c))) := by
    have hClosed : IsClosed (V c : Set X.left) :=
      isClosed_of_mem_irreducibleComponents _ c.property
    have : IsClosedImmersion (V c).ι := IsClosedImmersion.of_isPreimmersion _
      (by simpa only [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι] using hClosed)
    have : IsProper (Y c).hom := inferInstanceAs (IsProper ((V c).ι ≫ X.hom))
    have : IsReduced (Y c).left := CurveSplit.isReduced_of_smooth ((V c).ι ≫ X.hom)
    have : IrreducibleSpace (Y c).left := Subtype.irreducibleSpace c.property.1
    have : IsIntegral (Y c).left := isIntegral_of_irreducibleSpace_of_isReduced _
    have := W17ProperCompact.compactSpace_complexPoint_of_isIntegral_isProper (Y c)
    exact isCompact_range (Point.continuous_map (i c))
  refine ⟨?_⟩
  have hcover : ⋃ c : C, Set.range (Point.map (R := ℂ) (i c)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    let c : C := ⟨irreducibleComponent p.underlying,
      irreducibleComponent_mem_irreducibleComponents p.underlying⟩
    have hmem : p.underlying ∈ V c := mem_irreducibleComponent
    have hr : Set.range p.left ⊆ Set.range (V c).ι := by
      rw [← Scheme.Hom.coe_opensRange (V c).ι, Scheme.Opens.opensRange_ι]
      rintro _ ⟨x, rfl⟩
      have hx : (x : Spec (CommRingCat.of ℂ)) = IsLocalRing.closedPoint ℂ :=
        @Subsingleton.elim (Spec (CommRingCat.of ℂ)) inferInstance _ _
      rw [hx]
      exact hmem
    refine Set.mem_iUnion.mpr ⟨c, ⟨Over.homMk (IsOpenImmersion.lift (V c).ι p.left hr) ?_, ?_⟩⟩
    · change IsOpenImmersion.lift (V c).ι p.left hr ≫ (V c).ι ≫ X.hom = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact p.w
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  rw [← hcover]
  exact isCompact_iUnion hc

end AlgebraicGeometry

#print axioms AlgebraicGeometry.compactSpace_complexPoint_of_proper_smooth
