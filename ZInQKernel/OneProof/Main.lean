import ZInQKernel.OneProof.H.TailK
import ZInQKernel.OneProof.TopChain
import ZInQKernel.OneProof.TYZBridge

/-!
# The whole proof in one theorem

`ZInQ.OneProof.frozenTarget` derives the frozen target `ZInQ.FrozenTarget` from every statement that is still open on
the development fork, and from nothing else. It composes two compiled chains:

* H: `HDec.HSyn.sixContactMin_of_open4` (`OneProof/H/`, generated from leaf-fold4's olean chain by
  `scripts/one_proof/gen.sh`) proves `ZInQ.SixContactMin` from the open research leaves (`OpenResearchLeaves2`), the
  open textbook leaves (`OpenTextbookLeaves4`), the added leaves (`OpenAddedLeaves4`) and the open glue (`OpenGlue4`);
* the rest: `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` proves `ZInQ.FrozenTarget` from H,
  reading A of Tian–Yuan–Zhang (from its seven open statements by cm-bridge's chain, `OneProof/TYZBridge.lean`) and the
  two open Gross–Zagier statements, with `HeckeThetaNewform` proved (`OneProof/TopChain.lean`). Hecke's continuation and the functional equation are proved there
  (`ZInQ.Contrib.heckeContinuation`, `ZInQ.Contrib.functionalEquation5`).

The hypotheses of `frozenTarget` are therefore exactly the open statements. Discharging one means replacing a field or
hypothesis by its proof; the theorem's statement then loses that hypothesis.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.CMBridge

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package

open ZInQ.Contrib.TYZDecomp in
/-- **Theorem 1.1, from every statement still open.** The TYZ hypotheses are the finest chain
(frontier rows T-1 to T-7): reading A of TYZ Theorem 3.5 from cm-bridge's
`tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five` (`OneProof/TYZBridge.lean`, from
`scratch/cm-bridge/Bridge.lean`). The GZ hypotheses are rows Z-1 and Z-2. -/
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves2) (t : HDec.HSyn.OpenTextbookLeaves4) (l : HDec.HSyn.OpenAddedLeaves4)
    (g : HDec.HSyn.OpenGlue4)
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal ZInQ.Contrib.TYZGenus.RingClass.HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (h5 : Lemma321Five)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
    (HDec.HSyn.sixContactMin_of_open4 r t l g)
    (tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five h11 h1 h29 hS h318 h35 h5)
    ZInQ.GZTheta.Frontier.heckeThetaNewform hL2 hL3

end ZInQ.Contrib.TYZGenus.CMBridge

end

#print axioms ZInQ.OneProof.frozenTarget
