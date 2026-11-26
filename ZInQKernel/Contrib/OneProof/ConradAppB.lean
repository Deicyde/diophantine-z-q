import ZInQKernel.Contrib.OneProof.ConradAppB.SenFiniteInertia
import ZInQKernel.Contrib.OneProof.ConradAppB.HodgeTateLocAlg
import ZInQKernel.Contrib.OneProof.ConradAppB.PropB3

/-!
# Conrad's Appendix B over `ℚ_p`, proved

`HDec.G0Galois.C8Conrad.ConradAppB` is the conjunction of the two statements of
Conrad, *Lifting global representations with local properties* (author preprint, Dec. 11,
2011), Appendix B, used at step C8 (diophantine_zq.tex L760–764), for the base field `ℚ_p`:

* `ConradAppBQp` (p. 32): a continuous character `ψ : G_{ℚ_p} → E^×` that is Hodge–Tate with
  a single weight is locally algebraic. Twisting by an integral power of the cyclotomic
  character reduces to weight `0`, where the rank-one weight-zero case of Sen's theorem
  (Serre, *Groupes algébriques associés aux modules de Hodge–Tate*, Astérisque 65 (1979),
  §1.4, Th. 2 and Cor. 3) gives finite image on inertia (`ConradAppB/HodgeTateLocAlg`).
* `ConradPropB3Qp` (Prop. B.3, p. 33): a locally algebraic character of exponent `n` has the
  Hodge–Tate weight `n` with full multiplicity. After the twist, the character is unramified
  up to a finite-order factor, and an unramified character has a period in `ℂ_p`; the
  dimension count is the tree's `Bridges.conradHTMult_of_identityLine` (`ConradAppB/PropB3`).

Both rest on the three inputs proved in `ConradAppB/` (the unramified–cyclotomic splitting by
local class field theory, periods of unramified characters, and induction to `ℂ_p ⊗ L`) and on
the tree's Tate–Sen theorem for the cyclotomic tower over `ℚ_p`. Conrad's preprint is used
only as the statement.
-/

set_option autoImplicit false

namespace ZInQ.Contrib.SenWeightZero

/-- **Conrad, Appendix B (pp. 32–33), base field `ℚ_p`, proved.** -/
theorem conradAppB_proof : HDec.G0Galois.C8Conrad.ConradAppB :=
  ⟨conradAppBQp_of_sen senFiniteInertia_proof,
    conradPropB3Qp_of_inputs unramifiedCyclotomicSplitting_proof unramifiedPeriod_proof⟩

end ZInQ.Contrib.SenWeightZero
