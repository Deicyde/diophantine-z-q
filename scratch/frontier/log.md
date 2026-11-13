# frontier: results log

Task frontier, 2026-11-13. Inventory of the open Props on the path to `ZInQ.FrozenTarget`.

## Setup
- 10:44 PST: start (no earlier log). `git merge origin/main` -> HEAD contains fork main b7cdba8e (303 commits merged, clean).
- Branch docs of today's tasks dumped (read-only, not committed) to /tmp/frontier-docs/<branch>/.

## Findings
- VERIFIED (chainlib signature parse, git show): top of the chain
  - `ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier : SixContactMin → Literature.TYZThm35ReadingA → Literature.GrossZagier → FrozenTarget` (fork main, Contrib/GaussFE/Headline.lean).
  - `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd` (Scope.lean), `grossZagierCd_of_leaves' : HeckeThetaNewform → FHNonvanishing → GrossZagierHeegner → GrossZagierCd` (Decomp.lean), `frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` (5 hyps).
  - wip/atkin-li 6f77abb1 Contrib/GZTheta/NewCMFinal.lean: `heckeThetaNewform : HeckeThetaNewform` and `frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner : SixContactMin → TYZThm35ReadingA → FHNonvanishing → GrossZagierHeegner → FrozenTarget`. NewCMFinal imports only NewCMProof, New32, both unchanged from fork main (git diff empty).
  - wip/g0-assemble3 357f5d9e scratch/g0-assemble3/G0Assemble3.lean L90474: `HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) : ZInQ.SixContactMin`; field counts parsed: ResearchLeaves4 24, TextbookLeaves 35, GluePieces4 46. Conclusion is the kernel's `ZInQ.SixContactMin` (file imports ZInQKernel.Hypotheses.JHeight etc.).
- Branch snapshot (10:50 PST): active branches beyond the brief: assemble-port (GluePieces5 in progress, on leaf-fold2's prefix), leaf-fold2, linked-ram, cm-bridge, period-glue(+-b), period-num, cpts-transport, ts-kummer, hecke-rest, frob-contrib, dim-contrib, rv-fast, g8-local, g8-tate-b, notes-fix2. spread-out = frob-pieces commit 60340bed.
- 10:58 VERIFIED: `lake env lean scratch/frontier/TopChain.lean` exit 0 (6 s, after `lake build` of NewCMProof, New32, TYZGenus.{RingClassBridge,Package}, GZDecomp.Decomp, MainLiterature, GaussFE.Headline). Output scratch/frontier/TopChain.out: `ZInQ.GZTheta.Frontier.newCM`, `ZInQ.GZTheta.Frontier.heckeThetaNewform`, `ZInQ.Frontier.frozenTarget_of_open_main` all `[propext, Classical.choice, Quot.sound]`. So atkin-li's proof of HeckeThetaNewform compiles verbatim over fork main, and FrozenTarget follows from SixContactMin + {TYZThm11Integral, TYZLcalOne, TYZLemma29Mod2, CM.CMFieldOfDefinition ringClassFieldD, TYZSigmaFixesZn, Lemma318Literal HHprime, ∀ℓ IsTYZLcal ℓ → GenusPointLeafCM ℓ} + {FHNonvanishing, GrossZagierHeegner}.
- TYZ agent inventory (scratch/frontier/agent-tyz.md): finest set = cm-bridge 58f42029 scratch `CMBridge.tyzThm35ReadingA_of_cmLeaves7'` + tyz-cm Contrib Shimura reductions; 12 open Props (strict: 3 LEAF, 9 GLUE). Signatures of `tyzThm35ReadingA_of_cmLeaves_ringClassD`, `tyzThm35ReadingA_of_cmLeaves7'`, `tyzThm35ReadingA_of_shimura` re-read by chainlib: VERIFIED.
