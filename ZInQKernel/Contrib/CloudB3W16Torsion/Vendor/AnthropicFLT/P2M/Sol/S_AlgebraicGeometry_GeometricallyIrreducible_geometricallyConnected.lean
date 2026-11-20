/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨?_⟩
  have h := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f)
  rw [geometrically_eq_universally] at h ⊢
  refine MorphismProperty.universally_mono ?_ _ h
  intro X' Y' g hg hI hS
  haveI : IrreducibleSpace X' := hg hI hS
  infer_instance

example {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f :=
  solution f
