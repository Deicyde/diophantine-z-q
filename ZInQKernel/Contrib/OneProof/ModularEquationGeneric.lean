import ZInQKernel.Contrib.CloudB2X0Transitive.ModularEquation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j

/-!
# The modular equation for the generic elliptic curve, proved (flt-cqj2)

`FltCqj.ModularEquationGeneric` (`ZInQKernel/Contrib/CloudB2X0Transitive/ModularEquation.lean`): for every
cyclic subgroup `C` of order `N` of `E_j` over `\overline{ℚ(j)}`, `Φ_N(j(E_j/C), j) = 0`. It is the leaf that the
bypass fold of flt-cqj (`scratch/flt-cqj2/FoldBypassModEq.lean`) puts in place of Igusa's theorem
`ZInQ.RLeaf.IgusaGL2`; proving it removes that leaf from the single proof.

The proof is the `MapsTo` half of Anthropic FLT's
`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`, whose whole proof cone
(661 FLT modules, 414 of them ported by this task to Lean 4.35 / Mathlib v4.35) is vendored under
`ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/` (Apache-2.0; `LICENSE`, `NOTICE.upstream`; every
port change marked `-- [port]`). New code; no `sorry`, no `axiom`, no `native_decide`.
-/

namespace FltCqj2

/-- **Anthropic FLT's cyclic-quotient bijection**, at universe `0`: exactly the statement
`ZInQ.Contrib.CloudB2X0Transitive.CyclicQuotientJBijOn` (`Bridge.lean`), proved by the ported theorem. -/
theorem cyclicQuotientJBijOn_proof : ZInQ.Contrib.CloudB2X0Transitive.CyclicQuotientJBijOn := by
  intro K _ N _ data L _ _ _ _ hN E _ hE
  exact WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
    K N data L hN E hE

/-- **The modular equation for the generic curve** (`FltCqj.ModularEquationGeneric`), proved: the `MapsTo` half
of the cyclic-quotient bijection (`FltCqj.modularEquationGeneric_of_bijOn`). -/
theorem modularEquationGeneric_proof : FltCqj.ModularEquationGeneric :=
  FltCqj.modularEquationGeneric_of_bijOn cyclicQuotientJBijOn_proof

/-- **`X₀(N)`-transitivity for the generic curve** (`ZInQ.RLeaf.X0Transitive`, row H-41), proved. -/
theorem x0Transitive_proof : ZInQ.RLeaf.X0Transitive :=
  FltCqj.x0Transitive_of_modularEquationGeneric modularEquationGeneric_proof

end FltCqj2
