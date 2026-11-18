# d2a6-reroute results log

- Base: wip/lane74b 6b404a20; `git merge origin/wip/sz-raynaud` -> ff8a03ac7 (no conflicts). Nothing else merged.
- Read docs/research/sz-raynaud.md, .fleet/sz-raynaud.md, ZInQKernel/Contrib/OneProof/SZRaynaud.lean. VERIFIED (read).
- Top module TailZ79: `OpenResearchLeaves53` has `sga7_IX_Cor3_3_Def34`, `sga7_IX_3_5_ForwardGeom_Def34`; its conversion
  `openResearchLeaves36EBCF_of_OpenResearchLeaves53` computes `sga7_IX_3_5_ForwardGeom := sga7_IX_3_5_ForwardGeom_of_def34 ..`
  and `sga7_IX_3_3_SHpre := shpre_of_cor33 (sga7_IX_Cor3_3_of_def34 ..)`. VERIFIED (read).
- D2 in TailH: `raynaudPlace_of_R6` (TailH:2577) applies r6 over F = K(A[m]); `torsFix_of_descent` (TailH:2961) uses
  `raynaudPlace_of_R6` + `wildIter` + `fixed_of_unipSq_of_iterate'`. Other r6 readers in TailH: `tateWildK_of_R6`,
  `localGlue_of_leaves`, `localGlue_of_descent`, `localGlue_of_unramRoots`, `g7LocalPackK_of_R` (calls raynaudPlace_of_R6
  directly), `g8LocalPack_of_D/U/BC`, `localGlue_of_transport`, `localGlue_of_tateBridge35`, `localGlue_of_kerWild`,
  `exists_localGlue_of_tateBridgeK`. VERIFIED (grep).
- A6 in the kernel: TailF `qmModelG3_of hNOS hRay hTors hB : QMModelG3` (G3Out at T = {3}) via
  `LeafQM.AV.QML3.goodReduction` (Raynaud route); its only chain reader TailI `modelG3G6_of_leaves3`, through
  `modelG3G6_of`, which uses G3Out only after `g3Out_mono` into `T u` (`{3} ⊆ T u`). VERIFIED (read).
- Manuscript L529-530 (read): "The proper model and its universal abelian scheme give good reduction outside the places
  over S"; S contains all primes <= 324 (L383-384); the proper model is L443-477 (Buzzard Thm 2.1/Cor 2.3 at V_1(5) over
  Z[1/30], full-five marking, Isom_O(O/3, A[3]), free G_5 quotient, "represents exactly the full-three moduli problem").
  Uses of good reduction later: L558 (outside T), L752-753 (outside T u {l}), L781 (p not in T u {3,5}), L849 (p > R).
  VERIFIED (read).
- The kernel already has the integral model as a statement: `SGRSplit.ShimuraIntegralModelRep` (Contrib/OneProof/
  ShimuraGoodReductionNoGuard.lean: for p > 324 a proper smooth curve over Z_(p) with a QMAbScheme representing the
  moduli problem on locally noetherian Z_(p)-schemes); it was a bundle field from leaf-fold22 (TailZ34) and was pruned
  by sgr-fold (TailZ39). VERIFIED (read).
- Run 2 (11-17 10:22): rebuilt `TailZ79` + `SZRaynaud` (lake build, 15380 jobs, 0 errors; /tmp log).
- D2R.lean: one fix (`valuation_lt_one_iff ... .mp`); compiles; `#print axioms` of `isWildInertia_of_wild_gen`,
  `raynaudPlaceFix_of_wildNF`, `torsFix_of_wildNF`, `localGlue_of_descent_wildNF`: [propext, Classical.choice,
  Quot.sound]. VERIFIED (scratch/d2a6-reroute/d2r-out.txt).
- A6U.lean (A6 on L529-530 from sgr-split's `ShimuraIntegralModelRep`): `D2A6.hasGoodReduction_of_intModel`
  (QML3 object over K ⊇ ℚ has good reduction at every valuation subring O of K in which a prime p > 324 is not a
  unit: classifying point, valuative criterion, pullback of the universal QMAbScheme, rigidity), the copy
  `HDec.LTGoodRed.goodRedTorsionT` (gen/gen_goodred.py), `HDec.D2A6.qmModelG3U_of`, `modelG3G6_of_leavesU`:
  all compile, standard axioms. VERIFIED (a6u-out.txt).
- Third r6 consumer found (not in sz-raynaud's report): the kernel field, `KernelField.kernelFieldExists_of_pieces_hf`
  via `good_of_QML3 hNOS hRay hTors K PK (T u) (three_mem_T u)` (good reduction of the model outside T(u), B3(v)).
  It is the same manuscript step L529-530. VERIFIED (read, Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean:1196).
- TaintD.lean (decl-level taint, closure of `sixContactMin_of_open72`, 274299 constants; out taintD-out.txt):
  IX35 seeds: 28 carriers, 91 tainted (the whole chain from TailZ79 down to `gluePieces_of_open4_hf_pz_eb`);
  COR33 seeds: 23 carriers, 86 tainted. TaintD2.lean (carriers by constructor type; adds `ResearchLeaves3EB`).
  The field-level FieldTaint (Taint79.lean) did not finish in 20 min (killed, no output).
- R6's terminal readers on the live chain (VERIFIED, taintD2-out.txt): TailH `raynaudPlace_of_R6`, `tateWildK_of_R6`,
  `torsFix_of_descent` (D2, via Consumers' `linkedTateLocal_of_leaves3_hf` -> LTLocal); TailI `modelG3G6_of_leaves3`
  (A6); TailC `good_of_QML3` (kernel field, via `kernelFieldExists_of_split_hf''`).
- Contrib/OneProof/D2WildNF.lean (= D2R.lean), A6IntModel.lean (= A6U.lean), D2A6Wrap.lean (`D2A6.R6U` :=
  RaynaudWildNF ∧ ShimuraIntegralModelRep; wrappers with the originals' signatures): lake build OK; wrappers
  standard axioms. VERIFIED.
- gen/gen_chain.py -> Contrib/OneProof/D2A6Chain.lean (131 blocks: 102 declarations + 29 structures copied,
  `X -> X_u`/`XU`; R6 -> R6U, IX 3.5 fields -> `r6u : R6U`, readers -> wrappers): `lake env lean` 0 errors,
  `#print axioms HDec.HSyn.sixContactMin_of_open72_u`: [propext, Classical.choice, Quot.sound]. VERIFIED
  (chain-out1.txt).
- gen/gen_bypass.py -> BypassFold.lean (the next TailZ: `OpenResearchLeaves54`, 28 fields = 53's 27 with
  `sga7_IX_3_5_ForwardGeom_Def34` -> `elliotWildInertiaTrivial` + `shimuraIntegralModelRep`, `raynaudSemistableSHOr` ->
  `silverbergZarhinThm35`; `openResearchLeaves53U_of_OpenResearchLeaves54`; `sixContactMin_of_open73`):
  `lake env lean` OK, `#print axioms HDec.HSyn.sixContactMin_of_open73`: standard. VERIFIED (bypass-out.txt).
  Strict count (this base's kinds.tsv, H rows): 5/24 on 29 -> 5/25 on 30; strictest 5/24 -> 5/25 (GLUE +1:
  ELLIOT and the integral model count GLUE; the IX 3.5 row was GLUE, the 4.7 row LEAF -> SZ35 LEAF).
- Cor. 3.3 (`sga7_IX_Cor3_3_Def34`) stays: COR33 taint shows its live readers are `ss1_ss3_of14NF_hf_gm_pz_eb`
  (SS3, semistable persistence, `semistablePersistsSHcp`) and `researchLeaves9_of_open14_hf_gm_pz_eb`'s
  `semistableNeronBaseChange` (`sga7_IX_3_3`); neither is D2 or A6. VERIFIED (taintD-out.txt, EichlerBoundCopy).
