import ZInQKernel.Contrib.OneProof.Y3ResidueAction
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.AffineNeighborhood

/-! Smooth proper curves, including disconnected ones, admit invariant affine
neighborhoods for finite actions. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- Every finite set on a proper smooth curve over a field lies in an affine
open, even when the curve has several components. -/
theorem exists_affineOpens_forall_mem_of_smooth_curve
    {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] (s : Finset X) :
    ∃ U : X.affineOpens, ∀ x ∈ s, x ∈ U.1 := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  let C := irreducibleComponents X
  have : Finite C := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let V (c : C) : X.Opens :=
    ⟨c.val, by
      obtain ⟨x, hx⟩ := c.property.1.nonempty
      have hc : c.val = irreducibleComponent x := CurveSplit.components_disjoint f _ c.property _
        (irreducibleComponent_mem_irreducibleComponents x) ⟨x, hx, mem_irreducibleComponent⟩
      rw [hc]
      exact CurveSplit.isOpen_irreducibleComponent f x⟩
  have hVclosed (c : C) : IsClosed (V c : Set X) :=
    isClosed_of_mem_irreducibleComponents _ c.property
  have hVdisj : Pairwise (fun c d => Disjoint (V c) (V d)) := by
    intro c d hcd
    apply disjoint_iff_inf_le.mpr
    intro x hx
    exact False.elim (hcd (Subtype.ext
      (CurveSplit.components_disjoint f _ c.property _ d.property ⟨x, hx.1, hx.2⟩)))
  have hlocal (c : C) : ∃ U : X.affineOpens, U.1 ≤ V c ∧
      ∀ x ∈ s, x ∈ V c → x ∈ U.1 := by
    let f' := (V c).ι ≫ f
    have : IsClosedImmersion (V c).ι := IsClosedImmersion.of_isPreimmersion _
      (by simpa only [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι] using hVclosed c)
    have : IsProper f' := inferInstance
    have : SmoothOfRelativeDimension 1 f' :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((V c).ι ≫ f))
    have : IsReduced (V c).toScheme := CurveSplit.isReduced_of_smooth f'
    have : IrreducibleSpace (V c).toScheme := Subtype.irreducibleSpace c.property.1
    have : IsIntegral (V c).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    let inComponent := s.filter (fun x => x ∈ V c)
    let toComponent (x : inComponent) : (V c).toScheme :=
      ⟨x.val, (Finset.mem_filter.mp x.property).2⟩
    let s' : Finset (V c).toScheme := inComponent.attach.image toComponent
    obtain ⟨U', hU'⟩ := exists_affineOpens_forall_mem_of_smooth_integral_curve f' s'
    let U := (U'.1.ι ≫ (V c).ι).opensRange
    have hU : IsAffineOpen U := isAffineOpen_opensRange (U'.1.ι ≫ (V c).ι)
    refine ⟨⟨U, hU⟩, ?_, fun x hx hxV => ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact (U'.1.ι y).property
    · let x' : (V c).toScheme := ⟨x, hxV⟩
      have hx' : x' ∈ s' := Finset.mem_image.mpr
        ⟨⟨x, Finset.mem_filter.mpr ⟨hx, hxV⟩⟩, Finset.mem_attach _ _, rfl⟩
      exact ⟨⟨x', hU' _ hx'⟩, rfl⟩
  choose U hle hmem using hlocal
  refine ⟨⟨⨆ c, (U c).1, IsAffineOpen.iSup_of_disjoint (fun c => (U c).2) ?_⟩, ?_⟩
  · intro c d hcd
    exact (hVdisj hcd).mono (hle c) (hle d)
  · intro x hx
    let c : C := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    exact (le_iSup (fun d => (U d).1) c) (hmem c x hx mem_irreducibleComponent)

/-- A finite action on a proper smooth curve over a field has an invariant
affine neighborhood around every point. -/
theorem exists_invariant_isAffineOpen_of_smooth_curve
    {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f]
    {G : Type*} [Group G] [Finite G] (ρ : G →* Aut X) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U := by
  classical
  have := Fintype.ofFinite G
  have : IsSeparated (terminal.from X) := by rw [← terminal.comp_from f]; infer_instance
  let s : Finset X := Finset.univ.image (fun g => (ρ g).asIso.hom x)
  obtain ⟨V, hV⟩ := exists_affineOpens_forall_mem_of_smooth_curve f s
  let U : X.Opens := ⨅ g : G, (ρ g).asIso.hom ⁻¹ᵁ V.1
  refine ⟨U, IsAffineOpen.iInf (fun g => V.2.preimage (ρ g).asIso.hom), ?_, ?_⟩
  · change x ∈ (U : Set X)
    rw [Opens.coe_iInf, Set.mem_iInter]
    exact fun g => hV _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))
  · intro h
    ext y
    change ((ρ h).asIso.hom y ∈ (U : Set X)) ↔ y ∈ (U : Set X)
    rw [Opens.coe_iInf, Set.mem_iInter, Set.mem_iInter]
    change (∀ g, (ρ g).asIso.hom ((ρ h).asIso.hom y) ∈ V.1) ↔ ∀ g, (ρ g).asIso.hom y ∈ V.1
    have hcomp (g : G) : (ρ g).asIso.hom ((ρ h).asIso.hom y) = (ρ (g * h)).asIso.hom y := by rw [map_mul]; rfl
    simp only [hcomp]
    constructor
    · intro hy g
      simpa only [inv_mul_cancel_right] using hy (g * h⁻¹)
    · exact fun hy g => hy (g * h)

end AlgebraicGeometry

#print axioms AlgebraicGeometry.exists_invariant_isAffineOpen_of_smooth_curve
