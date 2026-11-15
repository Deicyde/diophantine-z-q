import ZInQKernel.Contrib.OneProof.H.TailZ19
import ZInQKernel.Contrib.OneProof.TYZSplit
import ZInQKernel.Contrib.OneProof.TopChain
import ZInQKernel.Contrib.TYZChain.Main

/-!
# The whole proof in one theorem

`ZInQ.OneProof.frozenTarget` derives the frozen target `ZInQ.FrozenTarget` from every statement that is still open on
the development fork, and from nothing else. It composes three compiled chains:

* H: `HDec.HSyn.sixContactMin_of_open15` (`OneProof/H/`) proves `ZInQ.SixContactMin` from the open research leaves
  (`OpenResearchLeaves12`), textbook leaves (`OpenTextbookLeaves10`), added leaves (`OpenAddedLeaves11`) and glue
  (`OpenGlue7`). The modules up to `TailK` are leaf-fold4's chain moved onto the kernel's declarations (op-dedupe,
  op-compact); `TailL`-`TailN` are leaf-fold5's and `TailO` is leaf-fold6's, copied from their olean chains;
  `TailP`-`TailX` are leaf-fold7's (the split tasks av-glue, av-split, curve-split, hodge-split, qm-split, mcr-glue
  folded in; docs/research/leaf-fold7.md); `TailY`-`TailZ4` are leaf-fold8's (height-split, height-glue,
  qm-glue and six cloud-worker Contrib proofs folded in; docs/research/leaf-fold8.md); `TailZ5`-`TailZ9` are leaf-fold9's
  (`r1rec`, `r5` proved from `r1r2`, `r15` from `dsThm966` (modular-split), `r7b`, `r8` from published-form leaves
  (reduct-split), `r5count` from González–Rotger's count on `X₆` (shimura-split), and cloud PR #11's two proofs;
  docs/research/leaf-fold9.md); `TailZ10`-`TailZ15` are leaf-fold10's (dimjac-glue's proof of
  `dimJacobianEqGenus`, `y3Connected` from Deligne's printed theorem (shimura-glue), `r6`, `semistableReductionThm`
  and `semistablePersists` from published-form leaves (reduct-glue); docs/research/leaf-fold10.md); `TailZ16`-`TailZ17`
  are route-a-fold's (r1univ-rigid's Mumford rigidity: the moduli leaves `r1r2`, `shimuraFamily`,
  `gonzalezRotgerCountX6`, `deligneComponentsY3Printed` restated on abelian schemes, as printed, plus the leaf
  `mumfordRigidityCore`; docs/research/route-a-fold.md); `TailZ18`-`TailZ19` are leaf-fold12's (cm24-value's proof of
  `igusaCMValue24`; c-to-printed's `neronLocalizesDVR`, `faltingsLemma5BC`, `semistableNeronBaseChange` from printed
  leaves).
* TYZ: `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` proves reading A of Tian–Yuan–Zhang from four leaves; the
  fourth, tyz-35's pinned form of TYZ Theorem 3.3, is derived from TYZ Theorem 3.3 in its printed form
  (`ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33`, `OneProof/TYZSplit.lean`, task tyz-split).
* GZ and assembly: `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` proves `ZInQ.FrozenTarget`
  from H, reading A and the two open Gross–Zagier statements, with `HeckeThetaNewform` proved
  (`OneProof/TopChain.lean`) and Hecke's continuation and the functional equation proved
  (`ZInQ.Contrib.heckeContinuation`, `ZInQ.Contrib.functionalEquation5`).

The hypotheses of `frozenTarget` are therefore exactly the open statements. Discharging one means replacing a field or
hypothesis by its proof; the theorem's statement then loses that hypothesis.
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open.** -/
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves12) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves11)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open15 r t l g)
    (tyzThm35ReadingA_of_leaves h11 h29 hS (ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 h33))
    ZInQ.GZTheta.Frontier.heckeThetaNewform hL2 hL3

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget
