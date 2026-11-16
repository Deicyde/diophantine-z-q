import ZInQKernel.Contrib.CloudB3W11TwistDescent.TateAdapter

/-!
# Tate twist invariants over the exact OneProof definitions

The whole-group theorem reuses the Apache-2.0 Anthropic Tate proof at
`6e837e75355538c7f80bab5b956861e86c4eacc2`, ported to the pinned Lean/Mathlib.
Its actual cyclotomic trace estimates and Ax–Sen–Tate input are proved, not
assumed. A twisted norm-product argument extends it to every finite `K/ℚ_p`.
The adapter proves equality of the action with `cpAct` and uses exactly `cycPow`.
Preserved source notices are in the supporting modules' LICENSE/NOTICE files.
-/

namespace ZInQ.Contrib.CloudB3W11

/-- Tate 1967, §3.3, Theorem 2, nonzero cyclotomic-power specialization at
finite extensions of `ℚ_p`, with the exact existing OneProof constant. -/
theorem tateTwistInvariants_proof : ZInQ.Contrib.HodgeSplit.TateTwistInvariants :=
  ZInQ.Contrib.CloudB3W11TwistDescent.all_twist_invariants_vanish

end ZInQ.Contrib.CloudB3W11
