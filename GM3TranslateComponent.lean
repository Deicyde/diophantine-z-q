/-
Lane5 producer of C3's exact TranslateComponent.{u}.
SOURCE ONLY / UNCOMPILED. Truth pre-check: true. An infinite rational preimage
provides a rational point g in C; right translation by g^{-1} is an ACTUAL
scheme isomorphism and sends g to the unit. Homeomorphisms permute maximal
irreducible sets and postcomposition with an iso is injective on rational
points, preserving infinity. No reducedness, smoothness or dimension case
is assumed. The exact consumer's proper/AlgClosed hypotheses are harmless.

Translation is an iso in Over, NOT generally a GROUP homomorphism; no false
IsMonHom instance is attached to a nontrivial translation.
-/
import Mathlib.Topology.Irreducible
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Assembly

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace H5OriginalDVR.Lane5.GM3Points

/-- The actual categorical right translation sends a point x to x*y. -/
theorem mulRight_comp_point
    {k : Type u} [Field k] (G : Grp (Over (Spec (CommRingCat.of k))))
    (x y : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ G.X) :
    x ≫ (GrpObj.mulRight y).hom = x * y := by
  change x ≫ lift (𝟙 G.X) (toUnit G.X ≫ y) ≫ μ[G.X] = lift x y ≫ μ[G.X]
  simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc,
    toUnit_unit, Category.id_comp]

/-- EXACT C3 interface; use a scheme homeomorphism and an actual point map. -/
theorem translateComponent :
    ZInQ.Contrib.CloudR2NOS.Step1.TranslateComponent.{u} := by
  intro k _ _ G _ C hC hInfinite
  obtain ⟨g, hgC⟩ := hInfinite.nonempty
  let e : G.X ≅ G.X := GrpObj.mulRight (g⁻¹)
  let eScheme : G.X.left ≅ G.X.left := (Over.forget _).mapIso e
  let h : G.X.left ≃ₜ G.X.left := eScheme.hom.homeomorph
  let C' : Set G.X.left := h '' C
  have hC' : C' ∈ irreducibleComponents G.X.left :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber h h.continuous h.isOpenMap
      (fun x => (Set.subsingleton_singleton.preimage h.injective).isPreirreducible)
      h.surjective hC
  have hgOne : g ≫ e.hom = 1 := by
    exact (mulRight_comp_point G g (g⁻¹)).trans (mul_inv_cancel g)
  have hunit : (η[G.X] : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ G.X).left.base
      (IsLocalRing.closedPoint k) ∈ C' := by
    refine ⟨g.left.base (IsLocalRing.closedPoint k), hgC, ?_⟩
    change (g ≫ e.hom).left.base (IsLocalRing.closedPoint k) =
      (η[G.X] : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ G.X).left.base
        (IsLocalRing.closedPoint k)
    rw [hgOne]
    rfl
  let F : (ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ G.X) →
      (ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ G.X) := fun x => x ≫ e.hom
  have hF : Function.Injective F := by
    intro x y hxy
    exact (cancel_mono e.hom).mp hxy
  have hsub : F '' ((fun x : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ G.X =>
      x.left.base (IsLocalRing.closedPoint k)) ⁻¹' C) ⊆
      ((fun x : ZInQ.Contrib.CloudR2NOS.Step1.Pt k ⟶ G.X =>
        x.left.base (IsLocalRing.closedPoint k)) ⁻¹' C') := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨x.left.base (IsLocalRing.closedPoint k), hx, ?_⟩
    rfl
  exact ⟨C', hC', hunit, (hInfinite.image hF).mono hsub⟩

end H5OriginalDVR.Lane5.GM3Points
