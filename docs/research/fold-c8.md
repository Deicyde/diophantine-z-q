# fold-c8: the joint C8 fold, count-neutral (Picard rows out, the manuscript's de Rham / Conrad route in)

Task fold-c8, 2026-11-17. Base: wip/leaf-fold33b b9b85486 (main + fold-b115 + fold-b116; top
`sixContactMin_of_open79` on `OpenResearchLeaves60`, TailZ86). The branch wip/fold-c8 is that base plus this task's
commits, so wip/leaf-fold33b can fast-forward to it. Results log: `scratch/fold-c8/log.md`. Replay instructions:
`scratch/fold-c8/REPLAY.md`. This is model work and no person has reviewed it.

Marks: **VERIFIED** means compiled, computed, or read in a named file on this host. **UNVERIFIED** means not checked
here. Theorem numbers quoted from the specs and not read here are marked UNVERIFIED.

## Manuscript check

No step was found to be an error. Each line was read in `diophantine_zq.tex` on this host (VERIFIED by reading). The
cited prints themselves (Conrad, Scholze, Milne) are not on this host.

| tex lines | statement (paraphrase) | verdict |
| --- | --- | --- |
| L755 | Tate convention: the cyclotomic character has HT weight −1 | OK. The project's `htMult` uses the same convention; Conrad's convention is the opposite, and the translation is definitional (`htMult_eq_conradHTMult_neg`, `rfl`; conrad-b3 §3.1). |
| L758-760 | the twisting character is a de Rham subrepresentation of the Hom representation, unramified outside finitely many primes | OK. The sentence holds as stated. Its Hodge–Tate half, sharpened to weight 0 at 5 (`TwistCharHTWt0`), is **proved** (`C8Conrad.twistCharHTWt0_proof`) and stays labelled on-the-spot: the weight-0 form comes from the weight comparison at L765-766, not from a print. The integrator's note: de Rham ⇒ HT is printed at Conrad p. 11 Lemma 4.1 (not read here: UNVERIFIED). |
| L760-762 | local algebraicity \cite[App. B, pp. 32-33]{conrad-local-characters} and CFT over ℚ: a finite character times an integral power of the cyclotomic character | OK at the level of the citation. It is now the leaf `conradAppB` (= `ConradAppBQp ∧ ConradPropB3Qp`, base field ℚ_p), exactly the manuscript's citation; bibitem L11046-11049 is an author preprint, Dec. 11 2011 (unrefereed). The page read is the reading desk's, forwarded through conrad-b3, not done here. |
| L763-764 | "removing its integral local Hodge–Tate weight" leaves finite inertia at 5 and elsewhere | OK, supported by Conrad Prop. B.3 (the HT weight of a locally algebraic character is its exponent), which is part of the same citation. Lean: `locAlgExponentEqWeight_of_conradPropB3`. The departure leaf Tate 1967 (`TateTwistInvariantsInertia`) is not used: it is absent from the closure (VERIFIED). |
| L765-767 | the weights {0,−1} against {0,1−k} force k = 2 and power zero | OK. Unchanged route (`g12DetPZ_of_inputs`). |
| L864-866 | "Poincaré reducibility" (uncited) gives an L'-isogeny A × Z → J | Gap filled: proved outright by PR #86 (`ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof : AVB1.PoincareComplement`, standard axioms). No row. |
| lem:de-rham-descent, L10939-10950 (statement), L10953-10965 (Scholze Cor. 1.8 + Thms 9.1, 9.3, erratum), L10966-10970 (Milne v2.00 Part I Thm 12.1(a)) | `H¹_et` is de Rham; `V_ℓ(A) ≅ H¹^∨` equivariantly | OK at the level of its citations. These are the leaves `scholzeH1AbVar` (Scholze, stated for general g: a labelled generalization of the manuscript's g = 2; `ScholzeH1AbSurf` with g = 2 is stated too and implied) and `t10TateDuality` (Milne, unread). Lean states `H¹` over Mathlib's **pro-étale** `Scheme.EllAdicCohomology`; the comparison with classical étale cohomology is flagged as an on-the-spot step in `scholzeH1AbVar`'s flag. |
| L10996 | the Hodge numbers of `H¹_dR(A/F)` are 2,2 (uncited) | Inside the leaf `scholzeH1AbVar` (ELLIOT: uncited manuscript step; general g: h^{1,0} = g, Mumford §4, locator UNVERIFIED). |

The integrator's expected verdicts all agree with this reading: L758-764 OK, L763-764 supported by Conrad Prop. B.3,
lem:de-rham-descent OK at the level of its citations, and TwistCharHTWt0's sentence holds as stated.

**On-the-spot statements** (neither in the manuscript nor in a cited print), all labelled, none added by this task:
* `TwistCharHTWt0`: proved glue; its docstring in `C8CFT.lean` labels it GLUE / on-the-spot; the `conradAppB` row's flag names it.
* In `scholzeH1AbVar`'s flag: general g (a generalization); F̄ vs ℂ_p; Mathlib's pro-étale ℓ-adic cohomology vs
  classical étale cohomology.

## 1. Result

**The joint C8 fold is in, built and checked. It is count-neutral: H strict 5/24 on 29 → 5/24 on 29, strictest
5/24 → 5/24, with 30 open hypotheses before and after (VERIFIED: the fold script's count and render_open).** That is
the integrator's expected count, measured on this top. PR #86 is required: without it `poincareComplement` would be a
new textbook row and the count would be 5/25 on 30.

| | top | rows out | rows in | H strict / strictest |
| --- | --- | --- | --- | --- |
| base | `sixContactMin_of_open79` (TailZ86; `OpenResearchLeaves60`, `OpenTextbookLeaves18`, `OpenAddedLeaves27`) | | | 5/24 on 29 |
| fold-c8 | `sixContactMin_of_open80` (TailZ87; `OpenResearchLeaves61`, `OpenTextbookLeaves18`, `OpenAddedLeaves28`) | `picRepresentableAbVar`, `kleimanPicZeroProper954SiteQ` (added), `hodgeTateDecompOr` (research): all GLUE | `conradAppB`, `scholzeH1AbVar`, `t10TateDuality` (added): all GLUE | 5/24 on 29 |

The departure leaf `TateTwistInvariantsInertia` (Tate 1967) never entered the tree's bundles; it is off the route
(not in the closure). `poincareComplement` is filled by PR #86's `poincareComplement_proof` (no row).

What the fold does:
* **Consumer (i), step C8.** The Weil-pairing fields `t09SymmIsogenyExists` / `phiAmpleIsogeny` /
  `weilPairingMumford` / `detTate`, which come from the Picard rows and only feed `DetTate`, are replaced in a copy
  of every declaration that reads them by `c8 : C8Conrad.C8Inputs`, and the reader `g12Det_of_pz m.r14det m.detTate …`
  by `C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`. The C8 inputs come from `conradAppB` through
  `C8Conrad.c8Inputs_of_leaves` (`twistCharHTWt0`, `inertiaAtPDecomp` and `minkowskiInertiaQ` are proved).
* **Consumer (ii), Poincaré.** `openTextbookLeaves13HF_of_open16_P` with `hP := poincareComplement_proof`.
* **Consumer (iii), `hodgeTateDecompAbVar`.** This field is read from `DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1
  scholzeH1AbVar t10TateDuality` instead of the Picard rows.
* **`hodgeTateDecompOr` no longer read.** Its only flow was into consumer (iii). The new research bundle drops it, and
  the conversion `openResearchLeaves60_of_OpenResearchLeaves61 n l` fills it with
  `hodgeTateDecompOr_of_scholzeH1Milne l.scholzeH1AbVar l.t10TateDuality` (proved from the new leaves; the rerouted
  chain ignores it). So no research-bundle copy was needed.

## 2. How it was built (VERIFIED)

1. **Merges.** `origin/wip/conrad-b3` e579047cc merged cleanly (d7482351). PR #86 head 8050603b merged cleanly
   (f0294b40): 317 files, all new, none of them changing an existing file. Hygiene (90e65c77): 12 dry-run scratch
   files that declare HDec.HSyn bundle generations were renamed `.lean.txt`. No host paths were found. The vendored
   LICENSE/NOTICE files are kept (CloudR2Poincare L1, L3, L4; CloudR2Hom C4SourcePort).
2. **Generator** `scratch/fold-c8/fold_c8.py`, one run.
   - c8-conrad2's taint (`gen/Taint.lean`, same seeds) on this top: closure 292708, 71 tainted. The live chain is
     d2a6b's `D2A6Chain` (`_sf_u` / `_u` copies) plus PicZeroCharZeroCopy and TailA.
   - c8-conrad2's copy generator (`gen/gen.py`, unchanged except the header argument): 69 blocks, 13 structures, both
     readers replaced.
   - A top section built from the live D2A6Chain declarations by checked textual edits (the script stops if a text
     changed): `GR9.openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u_hm` (iii), `openAddedLeaves18_hm`,
     `GR9.sixContactMin_of_open45_pz_eb_sf_u_hm` (ii), `GR9.sixContactMin_of_open72_sf_u_hm` (bypasses
     `sixContactMin_of_open48_eb_k954_sf_u`, which only converts the Picard bundle) and `sixContactMin_of_open79_hm`.
   - Then `TailZ87` with the new bundles and top (numeric names), Main.lean, and kinds.tsv.
   - The dry-run chain compiled on the first try (7.7 s).
3. **Files.**
   - New: `ZInQKernel/OneProof/H/C8Chain.lean` (1445 lines, 258 constants) and `ZInQKernel/OneProof/H/TailZ87.lean`
     (44 constants).
   - Changed: `ZInQKernel/OneProof/Main.lean` (import, two binders, call, one paragraph) and
     `docs/one-proof/kinds.tsv` (3 rows dropped, 3 added), plus the regenerated docs.
   - Not touched: claims.tsv and volatile.tsv (neither has a row for any of the six fields). No existing declaration
     of `ZInQKernel/OneProof/H/` was changed.

**kinds.tsv rows added** (flags from the specs: conrad-b3 for `conradAppB`, ht-merge for `scholzeH1AbVar` and
`t10TateDuality`; session names replaced by "the reviewer", "the reading desk", "an earlier review"):
* `conradAppB`: consequence, GLUE/GLUE, pending review. It notes the reading desk's page read of 11-17, that the
  source is an unrefereed preprint (the manuscript's own citation), and the reviewer's strict-review rating of the
  p. 32 part. It also says Prop. B.3 is read in Conrad's conventions and names TwistCharHTWt0 as on-the-spot proved
  glue.
* `scholzeH1AbVar`: consequence, GLUE/GLUE, pending review. It flags general g as a generalization (g = 2 is
  `ScholzeH1AbSurf`), the analytification dictionary, and Mathlib's pro-étale vs classical étale cohomology as an
  on-the-spot step.
* `t10TateDuality`: published, GLUE/GLUE (unread: Milne v2.00 Part I Thm 12.1(a) / Milne 1986 Thm 15.1(a) not read;
  locator UNVERIFIED).

## 3. Checks after the fold (VERIFIED; files `scratch/fold-c8/*-fold1.txt`)

* **Build.** `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.C8Chain
  ZInQKernel.OneProof.H.TailZ87` succeeds (16331 jobs). Before that, the component modules were built:
  `C8Printed`, `C8CFT`, `ScholzeH1AbVar` and PR #86's `CloudR2Poincare.FinalUnconditional` (16329 jobs). PR #86's
  `L1/Source20261116/ResidueFieldModels.lean` alone takes 2123 s.
* **Axioms.** `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`. The same holds
  for `sixContactMin_of_open80`, `sixContactMin_of_open79_hm`, `openResearchLeaves60_of_OpenResearchLeaves61`,
  `poincareComplement_proof`, `hodgeTateDecompOr_of_scholzeH1Milne`, `hodgeTateDecompAbVar_of_scholzeH1`,
  `g12DetPZ_of_inputs`, `c8Inputs_of_leaves`, `twistCharHTWt0_proof` and `locAlgExponentEqWeight_of_conradPropB3`
  (`axioms-out.txt`).
* **Hash guard** (DumpCompact + cmp_hashes): 21041 → 21343 constants. 302 are new (C8Chain 258, TailZ87 44). Only
  `ZInQ.OneProof.frozenTarget` changed (`cmp_fold1.txt`).
* **Closure** (`FoldCheck-fold1.txt`, 296120 constants):
  - Absent: `sorryAx`, `T09Pic.PicRepresentableAbVar`, `KleimanSite.KleimanPicZeroProper954SiteQ`,
    `OpenAddedLeaves27`, `sixContactMin_of_open79`, `C8Conrad.TateTwistInvariantsInertia` (Tate 1967),
    `detTate_of_leaves4_pz` and `hodgeTateDecompAbVar_of_open_k954`. The closure has 0 constants named
    `*PicRepresentable*` or `*KleimanPicZeroProper*`.
  - The hypotheses of `frozenTarget` are `OpenResearchLeaves61`, `OpenTextbookLeaves18`, `OpenAddedLeaves28` and `hPC`.
    `HodgeTateDecompOr` and `OpenResearchLeaves60` remain in the closure only as the target of the conversion; they
    are not hypotheses.
  - Field check: `OpenResearchLeaves61` has `OpenResearchLeaves60`'s fields minus `hodgeTateDecompOr`, and no field
    type differs.
* **`#discharges`** on the folded tree: 30 open hypotheses, 23 discharge one. The removed fields have no row, since
  they are not open. On the base, ht-merge's run showed `hodgeTateDecompOr` discharged by
  `hodgeTateDecompOr_of_scholzeH1Milne` from the two new leaves (`scratch/ht-merge/discharges_out.txt`). The Picard
  rows leave through the reroute, not through a discharging theorem; the closure check is the evidence.
* **OpenStatements:** 30. **render_open:** 29 H, strict 5/24, strictest 5/24, 1 other; `--check` ok.
  **frontier_crosswalk:** 232 IDs, 3 matched (was 4: H-199 matched `picRepresentableAbVar`); `--check` ok.
  **DischargesTest** was rerun: 23 DISCHARGES lines, no error. **autoform check** exits 0 (776 articles, 647 fully
  proved). **`scratch/lane74/gate.sh`** gives GATE=ok.
* **Follow-up noticed, not done:** DischargesTest now matches `OpenResearchLeaves61.deRhamVpAbVarDirect` by
  `DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne`, which uses the two new leaves alone. That row is
  LEAF/LEAF, so removing it would not lower the GLUE count (it would make 4/24 on 28). The decision is the
  integrator's.

### AllContrib / clash check (VERIFIED; `scratch/fold-c8/log.md` §6)

* Every one of the 6640 `ZInQKernel/Contrib` modules has an olean. The 31 missing ones were built first.
* **ClashScan** (contrib-clashes' olean scan with Lean 4.35's duplicate rule) over all Contrib modules plus
  `OneProof.Main` and `TailZ87`: 19043 modules, 856345 constants. **There are 7 fatal clashes, all pre-existing, and
  none involves a module of this branch:**
  - six are `HDecomp.Textbook.Different` against `Contrib.Different.Local` (fixed on wip/contrib-clashes, not on this
    base);
  - one is `WeierstrassCurve.Affine.divisorSum` (the CloudB2X0Transitive vendored FLT def against the Tau Ceti axiom).
* **CloudB3W17bReduced against PR #86:** no fatal clash. There is one accepted duplicate,
  `TopCat.Presheaf.stalkCongr.eq_1`: both vendor Stacks' `Perfect.BaseChangeStalk`.
* **Real co-import:**
  - the base `AllContrib.lean` list builds;
  - **the base list + every PR #86 module + all 26 CloudB3W17bReduced modules imports cleanly (exit 0)**;
  - the base list + the C8 / Scholze modules fails on the `divisorSum` clash. That failure is pre-existing: the base
    list + the unchanged base chain `OneProof.H.TailZ86` fails the same way, and the C8 modules import the chain.
* `AllContrib.lean` is not edited. The C8 modules can join it once the chain-vs-AllContrib clashes are fixed.

## 4. What remains

* Reviews of the three new rows: Conrad p. 33 Prop. B.3 (a human read would clear the AI page-read flag), Scholze in
  general g, and Milne.
* Optional cleanup, not done here: `C8LocAlg.TateTwistInvariantsInertia`, `locAlgExponentEqWeight_of_tateInertia` and
  `C8CFT.c8TwistFinite_of_leaves` are off the route.
* PR #86 is to be closed by the integrator after landing, with a note pointing at the landed SHA (not done here).
