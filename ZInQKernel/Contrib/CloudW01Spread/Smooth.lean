import ZInQKernel.Contrib.SpreadOut.Spread
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth

/-!
# Smoothness descends to a finite stage

The statement `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` is unchanged.
This is a bridge to the actual scheme-morphism descent proof in AxiomMath/Stacks
at revision c496df0d9beea9deaeabcea8492605f9a0a2313b (Stacks 0C0C,
EGA IV 17.7.8(ii)). The imported proof and its explicit dependency closure are
ported in this directory; see NOTICE.md and LICENSE.

The only translation is from the structure map of an object of `Over S` to
its morphism to `Over.mk (𝟙 S)`. The target of the base-changed morphism is
canonically isomorphic to the new base, so the two morphism properties agree.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudW01Spread

universe u

/-- Base changing the map to the identity object tests exactly the property
of the base-changed structure morphism. -/
theorem pullback_to_identity_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T : Scheme.{u}} (g : T ⟶ S) (X : Over S) :
    P ((Over.pullback g).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left ↔
      P ((Over.pullback g).obj X).hom := by
  have h : ((Over.pullback g).map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S))).left ≫
      pullback.snd (𝟙 S) g = ((Over.pullback g).obj X).hom := by
    simp only [Over.pullback_map_left, Over.pullback_obj_hom, Over.homMk_left, Over.mk_hom]
    exact pullback.lift_snd _ _ _
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := P) _
    (pullback.snd (𝟙 S) g), h]

end ZInQ.Contrib.CloudW01Spread

namespace ZInQ.Contrib.SpreadOut

/-- EGA IV₄ 17.7.8(ii), with exactly the fixed target's hypotheses. -/
theorem EGAIV_17_7_8_ii_proof : EGAIV_17_7_8_ii := by
  intro J _ _ _ D _ _ _ c hc i Xi hlfp hqc hqs hs
  letI : LocallyOfFinitePresentation Xi.hom := hlfp
  letI : QuasiCompact Xi.hom := hqc
  letI : QuasiSeparated Xi.hom := hqs
  letI : CompactSpace Xi.left := QuasiCompact.compactSpace_of_compactSpace Xi.hom
  letI : QuasiSeparatedSpace Xi.left := quasiSeparatedSpace_of_quasiSeparated Xi.hom
  let Y : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let τ : Xi ⟶ Y := Over.homMk Xi.hom
  haveI : CompactSpace Y.left := by
    change CompactSpace (D.obj i)
    infer_instance
  haveI : QuasiSeparatedSpace Y.left := by
    change QuasiSeparatedSpace (D.obj i)
    infer_instance
  haveI : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{0}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  haveI : LocallyOfFinitePresentation τ.left := hlfp
  haveI : Smooth ((Over.pullback (c.π.app i)).map τ).left :=
    (CloudW01Spread.pullback_to_identity_iff (@Smooth) (c.π.app i) Xi).2 hs
  obtain ⟨j, a, hj⟩ :=
    AlgebraicGeometry.exists_smooth_baseChange_of_smooth_limitBaseChange D c i Xi Y τ hc
  exact ⟨j, a, (CloudW01Spread.pullback_to_identity_iff (@Smooth) (D.map a) Xi).1 hj⟩

end ZInQ.Contrib.SpreadOut

#print axioms ZInQ.Contrib.CloudW01Spread.pullback_to_identity_iff
#print axioms ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof
