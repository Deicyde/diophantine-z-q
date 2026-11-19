import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel

/-!
# Lane RC22 (glue sweep): lane RC0's `RCLeaves` without the GLUE field `levelSupport`

Lane RC0 collects every remaining hypothesis of Theorem 5.3 in the structure `RCLeaves`
(`RC/Wiring/Leaves.lean`) and proves `restrictedConverseGenuine_of_leaves : Prints → RCLeaves →
RestrictedConverseGenuine`. Its earlier field `levelSupport` (lane RC13's GLUE "the level of the
functional equation is supported on the bad primes") was redundant: `levelSupport_of_modularNewform`
proves it from `ModularNewform` (lane RC8's print, then the field `modularNewform`, now the theorem
`RCLeaves.modularNewform`). Lane RC0 (round 3) dropped the field and uses
`levelSupport_of_modularNewform` inside `RCLeaves.twistSign`, so the
reduced structure of this file is now `RCLeaves` itself:

* `RCLeavesReduced := RCLeaves`;
* `RCLeavesReduced.toRCLeaves` is the identity;
* `restrictedConverseGenuine_of_reducedLeaves` (PROVED): **Theorem 5.3** (tex 1005–1011) from
  `Prints` and `RCLeavesReduced`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Ana

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Wiring

/-- **Lane RC0's `RCLeaves`, which no longer has the GLUE field `levelSupport`.** -/
abbrev RCLeavesReduced : Type := RCLeaves

/-- `RCLeaves` from `RCLeavesReduced` (the identity). -/
def RCLeavesReduced.toRCLeaves (L : RCLeavesReduced) : RCLeaves := L

/-- Every `RCLeaves` is the rebuilt structure of its reduction (PROVED). -/
theorem RCLeaves.eq_toRCLeaves (L : RCLeaves) : L = RCLeavesReduced.toRCLeaves L := rfl

/-- **Theorem 5.3 (`hyp:RC`) from `Prints` and `RCLeavesReduced`** (PROVED; tex 1005–1011): lane
RC0's `restrictedConverseGenuine_of_leaves`. -/
theorem restrictedConverseGenuine_of_reducedLeaves (P : Prints) (L : RCLeavesReduced) :
    RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_leaves P L.toRCLeaves

end ZInQ.Manuscript.RC.GlueSweep.Ana
