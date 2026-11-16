/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

set_option autoImplicit false

universe u

-- [port] was: p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.AlgebraicGeometry"
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MorphismProperty
open _root_.AlgebraicGeometry
-- [port] `p2m_open` accepts a namespace before it is declared; it is declared (empty) here first
namespace AlgebraicGeometry
end AlgebraicGeometry
open _root_.P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.AlgebraicGeometry

namespace AlgebraicGeometry
-- [port] was: p2m_export "AlgebraicGeometry" "Surjective Spec Scheme GeometricallyConnected geometrically"
export _root_.AlgebraicGeometry (Surjective Spec Scheme GeometricallyConnected geometrically)
namespace GeometricallyConnectedDescentAux
-- [port] was: p2m_open "AlgebraicGeometry"
open _root_.AlgebraicGeometry

theorem geometricallyConnected_of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S) [Surjective σ]
    [hgc : GeometricallyConnected (pullback.snd f σ)] : GeometricallyConnected f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩

  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp only [kL, l', Category.assoc, pullback.condition]
  haveI : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩

  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l') (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by rw [hm₁]; exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd b kL) sq

  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous

end AlgebraicGeometry.GeometricallyConnectedDescentAux

theorem solution :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by
  refine DescendsAlong.mk' fun {X Y Z} {f} {g} _ hf hfst => ?_
  haveI : Surjective f := hf
  haveI : GeometricallyConnected (pullback.fst f g) := hfst
  haveI : GeometricallyConnected (pullback.snd g f) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr hfst
  exact AlgebraicGeometry.GeometricallyConnectedDescentAux.geometricallyConnected_of_pullback_snd g f
