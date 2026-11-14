import ZInQKernel.OneProof.H.TailK
import ZInQKernel.OneProof.TopChain

/-!
# The whole proof in one theorem

`ZInQ.OneProof.frozenTarget` derives the frozen target `ZInQ.FrozenTarget` from every statement that is still open on
the development fork, and from nothing else. It composes two compiled chains:

* H: `HDec.HSyn.sixContactMin_of_open4` (`OneProof/H/`, generated from leaf-fold4's olean chain by
  `scripts/one_proof/gen.sh`, then moved onto the kernel's declarations by op-dedupe: 2951 copies removed, see
  `docs/research/op-dedupe.md`; gen.sh no longer reproduces these modules) proves `ZInQ.SixContactMin` from the open research leaves (`OpenResearchLeaves2`), the
  open textbook leaves (`OpenTextbookLeaves4`), the added leaves (`OpenAddedLeaves4`) and the open glue (`OpenGlue4`);
* the rest: `ZInQ.Frontier.frozenTarget_of_open_main` (`OneProof/TopChain.lean`, from `scratch/frontier/TopChain.lean`)
  proves `ZInQ.FrozenTarget` from H, the open Tian–Yuan–Zhang statements of the finest reduction on fork main, and the
  two open Gross–Zagier statements. Hecke's continuation and the functional equation are proved there
  (`ZInQ.Contrib.heckeContinuation`, `ZInQ.Contrib.functionalEquation5`).

The hypotheses of `frozenTarget` are therefore exactly the open statements. Discharging one means replacing a field or
hypothesis by its proof; the theorem's statement then loses that hypothesis.
-/

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package ZInQ.Contrib.TYZGenus.RingClass

namespace ZInQ.OneProof

/-- **Theorem 1.1, from every statement still open.** -/
theorem frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves2) (t : HDec.HSyn.OpenTextbookLeaves4) (l : HDec.HSyn.OpenAddedLeaves4)
    (g : HDec.HSyn.OpenGlue4)
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.Frontier.frozenTarget_of_open_main (HDec.HSyn.sixContactMin_of_open4 r t l g)
    h11 h1 h29 hcm hs h318 hG hL2 hL3

end ZInQ.OneProof

#print axioms ZInQ.OneProof.frozenTarget
