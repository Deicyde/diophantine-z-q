/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace CoherentBaseChange

structure FibreH0Family (T : Scheme.{u}) where

  G : ∀ (U : T.Opens), IsAffineOpen U → TwoTermComplex.{u, u} Γ(T, U)

  h0 : T → ℕ

  hglue : ∀ (U : T.Opens) (hU : IsAffineOpen U) (t : U),
    h0 t = (G U hU).fibreH0 (hU.primeIdealOf t)

end CoherentBaseChange
