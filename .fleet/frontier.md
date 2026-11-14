# frontier (2026-11-13)

**Main result.** `docs/research/frontier.md` lists every Prop still open on the path to `ZInQ.FrozenTarget`:
**70 = 21 LEAF + 49 GLUE** (strict rule: LEAF only if the Lean Prop is a printed refereed statement or a
specialization of it; composites, readings and unprinted consequences are GLUE). By premise:
- GZ: 2 (both GLUE: `GZDecomp.FHNonvanishing`, `GZDecomp.GrossZagierHeegner`).
- TYZ: 7 (3 LEAF).
- H: 61 (18 LEAF): 21 research fields, 17 textbook fields, 14 glue fields, and 9 Props from today's reductions.

For each Prop the report gives: Lean name, def file, class, citation (UNVERIFIED where taken from reports), last task,
newest branch@commit, and whether a task is running on it. §0 has a compact list of all 70 names.

**Chain, and how far it is checked.**
- **GZ + TYZ: compiled.** `ZInQ.Frontier.frozenTarget_of_open` derives `FrozenTarget` from `SixContactMin` plus
  exactly the 9 GZ and TYZ Props.
- **H, scenario A: compiled.** assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (92a27877, flat file
  compiled per its log) supplies `SixContactMin`. Composed with the above, the compiled composite has 79 hypotheses.
- **H, scenario F: not compiled as one file.** Nine further compiled branch results (T40 ⇐ `X0Transitive`;
  T26 ⇐ T5; `piTwistC`, `sphereFactorAffine` proved; `properSmoothGenConnected` ⇐ `ZariskiConnectedness`) bring the
  set to the 70 listed plus 6 bundle fields that are never projected.
- `scratch/frontier/chain.py` follows the hypotheses textually: 0 signature mismatches, route def texts identical
  to the assembly's, and the report's tables equal to the open set (`chain.py doc`).

**Declarations proved (this task).** All compile with `lake env lean`; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each.
- `scratch/frontier/TYZChain.lean` (tyz-cm's eleven Shimura modules and cm-bridge's `Bridge.lean`, verbatim; built by
  `build_tyz.py`):
  - `ZInQ.Frontier.tyzThm35ReadingA_of_open : TYZThm11Integral → TYZLcalOne → TYZLemma29Mod2 →
    Shimura.ShimuraReciprocityModFn → Lemma318Literal HHprime → (∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ CMBridge.tyzZ) →
    CMBridge.Lemma321Five → Literature.TYZThm35ReadingA`;
  - `ZInQ.Frontier.frozenTarget_of_open` (`SixContactMin` + those 7 + `FHNonvanishing` + `GrossZagierHeegner` →
    `FrozenTarget`);
  - `ZInQ.GZTheta.Frontier.newCM`, `heckeThetaNewform` (verbatim copies of atkin-li's proof).
- `scratch/frontier/TopChain.lean`: `ZInQ.Frontier.frozenTarget_of_open_main`, the fork-main-only variant, which the
  integrator's `ZInQ.OneProof.frozenTarget` uses.

**Findings.**
- The brief's "T1-T32 all proved" is false: T1, T3-T11, T16(b), T23, T24, T26, T27, T29 are open, though T26
  now follows from T5.
- g0-assemble3's `tateRamAtThree` is likely false. This is linked-ram's finding; assemble-port uses the corrected
  `TateRamAtThreeD`.
- `HomLatticeCorr` (now in assemble-port) is GLUE, not a printed theorem; this is homlattice's verdict.
- Several stale status texts: STATUS/README on `HeckeThetaNewform`; h-decomposition §2.2.
- No statement changes are proposed by this task.

**What remains.** The 70 Props. Folding the 9 scenario-F edges into the assembly is mechanical but not done. To
get the finer TYZ list into `OneProof`, cm-bridge's `Bridge.lean` would need to become a library module.

Files: `docs/research/frontier.md`, `scratch/frontier/{chain.py, chainlib.py, chain_out.txt, refs.txt, log.md,
TYZChain.lean, TopChain.lean, build_tyz.py, agent-*.md}`.
