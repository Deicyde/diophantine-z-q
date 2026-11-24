/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f]
    (y : ↥Y) (hy : (f.base ⁻¹' {y}).Nonempty) :
    topologicalKrullDim ↥(f.base ⁻¹' {y}) = n := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  haveI : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f (Y.fromSpecResidueField y) inferInstance
  have hne : Nonempty ↥(f.fiber y) := by
    obtain ⟨x, hx⟩ := hy
    exact ⟨(f.fiberHomeo y).symm ⟨x, hx⟩⟩
  have h1 : (n : WithBot ℕ∞) ≤ topologicalKrullDim ↥(f.fiber y) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h2 : topologicalKrullDim ↥(f.fiber y) ≤ n :=
    AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h3 : topologicalKrullDim ↥(f.fiber y) = topologicalKrullDim ↥(f.base ⁻¹' {y}) :=
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph
  rw [← h3]
  exact le_antisymm h2 h1
