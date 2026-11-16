# dcy3-fold: `deligneComponentsY3PrintedAb` removed from `ZInQ.OneProof.frozenTarget`, no new leaf

Task dcy3-fold, 2026-11-15/16. Base 094bdd96 (origin/wip/leaf-fold29; `frozenTarget` through
`HDec.HSyn.sixContactMin_of_open31`, 51 H fields). The fold applies dcy3-used's result (origin/wip/dcy3-used 36240662,
already an ancestor of the base; docs/research/dcy3-used.md §§2, 3, 5; `ZInQKernel/Contrib/OneProof/DeligneComponentsY3Used.lean`).
It is done in place, prune-style, as in yu-prune, rigid-prune and r6-nf. dcy3-used's `scratch/dcy3-used/BypassFold.lean`
was not used, because it targets an older base. Results log: scratch/dcy3-fold/log.md. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a named file on this host; **STANDARD** = textbook mathematics;
**SPECULATIVE** = judgement.

**Base defect, reported first (VERIFIED).** The base does not build as committed. `ZInQKernel/OneProof/Main.lean`
(leaf-fold29, 3b2562f1) uses `H29Split.LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZLemma29PrintedNe3`,
`TYZThm21At31` and `tyzLemma29Mod2_of_sixLeaves`. These are defined only in h29-ne3's drop-in
`scratch/h29-ne3/TYZLemma29Mod2.lean`, which was never copied over `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean`.
For every check below, that drop-in was copied into the working tree **locally and never committed**: it is a
Contrib file this task may not edit. The integrator must apply it to leaf-fold29. Every module up to TailZ37 builds
without it.

## 1. Main result

**`frozenTarget` loses `OpenAddedLeaves17.deligneComponentsY3PrintedAb : ShimuraGlue.DeligneComponentsY3PrintedAb`
(Deligne's π₀ theorem on `Y₃`, printed form on abelian schemes; GLUE/GLUE in kinds.tsv) and gains nothing.**
VERIFIED, with the drop-in above:
* `lake build +ZInQKernel.OneProof.Main` succeeds (13686 jobs);
* `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`;
* the pp.all type of `frozenTarget` prints identically before and after (scratch/dcy3-fold/frozenTarget_before.txt,
  frozenTarget_after.txt). Only `OpenAddedLeaves17` has one field fewer;
* PruneScan finds 0 unused fields among the remaining 50.

| | H fields | strict (kinds.tsv, H rows) | strictest | all rows of kinds.tsv (with the 11 `frozenTarget` Props) |
|---|---|---|---|---|
| before (094bdd96) | 51 | 41 LEAF / 10 GLUE | 39 / 12 | strict 49 / 13, strictest 47 / 15 |
| after | **50** | **41 / 9** | **39 / 11** | strict 49 / 12, strictest 47 / 14 |

The result is fields −1 and GLUE −1, in both readings, as expected. The field's rows in kinds.tsv and claims.tsv
are deleted (scratch/dcy3-fold/removed-rows.txt).

**Why the field is not needed.** The chain read the field only once, as `TSHecke.Y3Connected`. That reading was
`TailZ23.addedLeaves9_of_open14` (`deligneComponentsY3Printed := (deligneComponentsY3Printed_iff_ab_gl …).mpr
l.deligneComponentsY3PrintedAb`), followed by `TailZ13.addedLeaves8_of_open9` (`y3Connected := y3Connected_of_deligne
(deligneComponentsY3_of_printed …)`). dcy3-used proved
`DCY3Used.y3Connected_of_leaves : MumfordGroupLaw → ShimuraMainThmIDeligneY3AbU → HDec.TSHecke.Y3Connected` from two
research fields the bundle keeps. The type of `TSHecke.Y3Connected` and the consumer `heckeIrreducible_of_connected`
are unchanged.

### 1.1 The plumbing (step 1, scratch/dcy3-fold/thread.py; compiled before any deletion)

The only new binder is `(hY3 : TSHecke.Y3Connected)`. It is added where generation 8's `y3Connected` is produced and
carried up the stack:
* `addedLeaves8_of_open9 (l) (hY3)` (TailZ13) sets `y3Connected := hY3`;
* `sixContactMin_of_open11` (TailZ13) takes `hY3` last and passes it on;
* on the chain, `sixContactMin_of_open17` (TailZ23), `_open18` (TailZ24) and `_open19` (TailZ25) take it after
  `hSS`. `_open20` to `_open27` (TailZ26 to TailZ33) take it last;
* off the chain, `sixContactMin_of_open12` to `_open16` (TailZ15, 17, 18, 19, 22) take it too. Their bundles lose
  the field (§1.2), so they have no other source for it;
* **supply:** `sixContactMin_of_open28` (TailZ34) passes
  `_root_.DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU` with
  `r : OpenResearchLeaves21`. TailZ34 gets the one new import `ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used`.
  That module imports only RayClassShimura and TailZ40, which are already in TailZ34's environment. TailZ34 is the
  first generation that has `shimuraMainThmIDeligneY3AbU`.

`open28`'s type is unchanged, and so are `open29`–`open31` and `frozenTarget`, so folds that build on `open31`
merge without signature conflicts. Step 1 built on the first try. PruneScan then reported exactly
`OpenAddedLeaves17.deligneComponentsY3PrintedAb` UNUSED. The prune set is scratch/dcy3-fold/prune-set-step1.txt:
`OpenAddedLeaves9.deligneComponentsY3Printed` and the Ab field in `OpenAddedLeaves12`–`17`.

### 1.2 The prune (step 2, scratch/dcy3-fold/prune_dcy3.py; deletions only, every line in prune_out.txt)

* **Fields** (with their docstrings):
  * `deligneComponentsY3Printed` in `OpenAddedLeaves9` (TailZ13);
  * `deligneComponentsY3PrintedAb` in `OpenAddedLeaves10` (TailZ17), `11` (TailZ18), `12` (TailZ22), `13` (TailZ24),
    `14` (TailZ26), `15` (TailZ30), `16` (TailZ31) and `17` (TailZ34).

  Generations 10 and 11 are off the chain, but they must go too. Unlike r6-nf's off-chain generations,
  `addedLeaves11_of_open12` and `addedLeaves10_of_open11` fill them from the next generation, so the whole lineage
  loses the field ("from every generation").
* **Assignments** (9):
  * `addedLeaves9_of_open10` (TailZ17) and `addedLeaves9_of_open14` (TailZ23), the two `iff_ab` readings;
  * `addedLeaves10_of_open11`, `addedLeaves11_of_open12` and `addedLeaves12_of_open13`;
  * `openAddedLeaves13_of_…14`, `14_of_…15`, `15_of_…16` and `16_of_…17`.
* **Dead readers: none.** DeadCascade (dead-cascade.txt) lists only generated `casesOn`/`recOn` and the off-chain
  conversions with `open13`–`open16` above them. Those only lose an assignment.
* **Kept:**
  * the theorems `R1UnivRigid.deligneComponentsY3Printed_iff_ab` (TailZ17) and `…_iff_ab_gl` (TailZ40), and the kernel
    definitions `ShimuraGlue.DeligneComponentsY3Printed(Ab)`. They are still declared, now off the closure;
  * `DCY3Used.y3ConnectedAb_of_field` shows that the used form is not stronger than the removed field.
* **Docstrings updated:** `OpenAddedLeaves9`, `addedLeaves8_of_open9`, `sixContactMin_of_open28` and Main.lean's
  module doc.

## 2. Every hypothesis after the prune

The kinds are given as strict/strictest from docs/one-proof/kinds.tsv. The full statements are in
docs/one-proof/OPEN.md, which is not regenerated here (§5).

* **OpenResearchLeaves24 (26 fields, unchanged):** `bostLowerBound` L/L, `deRhamH1AbVarT` L/L, `dsThm965` L/G, `dsThm966` L/L, `eigenformHTNew` G/G, `elkiesX6StarFunctionField` L/L, `gaudronRemondThm14` L/L, `gonzalezRotgerProp56X6` L/L, `gonzalezRotgerX6Ab` L/L, `hodgeTateDecompAbVar` L/L, `javanpeykarBound` L/L, `mumfordGroupLaw` L/L, `neronBaseChangeStrictHenselization` L/L, `pazukiCor13Upper` L/L, `r11r12` G/G, `r16CoreY` G/G, `r17` G/G, `r7a` L/L, `r9a` L/L, `r9b` L/L, `raynaudSemistableSH` L/L, `semistablePersistsSHcp` L/L, `sga3_VIB_3_10` L/L, `sga7_IX_3_3_SH` L/L, `sga7_IX_3_5_ForwardGeom` L/L, `shimuraMainThmIDeligneY3AbU` G/G.
* **OpenTextbookLeaves11 (11 fields, unchanged):** `cartierSmooth` L/L, `charPolyIndepOfEllAlgClosed` L/L, `gagaMorphism` L/L, `geomConnOfRationalPoint` L/L, `groupSchemeEquidim` L/L, `homFreeFiniteAlgClosed` L/L, `mumfordTorsionAlgClosed` L/L, `neronSchemeExtensionExists` L/L, `poincareComplement` L/L, `regularSmoothPerfect` L/L, `uniformizationLeafAll` G/G.
* **OpenAddedLeaves17 (12 fields, one fewer):** `axSenTate` L/L, `deligneComponentsX6PrintedAb` L/L, `egaIV_8_10_5_xii` L/L, `geomConnOfAlgClosure` L/L, `milneIsogenyQuasiInverse` L/L, `phiAmpleIsogeny` L/L, `picRepresentableAbVar` L/L, `picZeroAbVar` L/L, `shimuraIntegralModelRep` G/G, `tateTwistInvariants` L/L, `thetaRatiosAlgebraic` G/G, `weilPairingMumford` L/G.
* **OpenGlue7 (1 fields, unchanged):** `quotientP1Coordinate` G/G.
* **frozenTarget's other arguments (11, unchanged; kinds.tsv keys):** `h11` L/L, `tyzLemma29PrintedNe3` L/L, `tyzThm21At31` L/L, `tyzProp23Printed` L/L, `tyzTestVectorExists` L/L, `legendreThreeSquares` L/L, `jonesPallX2Y2Z16` L/L, `hCM` G/G, `h33` L/L, `hFH` G/G, `hL3` G/G.

## 3. The remaining leaves by the theory they come from

These are unchanged from leaf-fold29, except that Deligne's theorem on connected components is now used only on `X₆`
(`deligneComponentsX6PrintedAb`). On `Y₃`, the only Shimura-variety input left is the composite research row
`shimuraMainThmIDeligneY3AbU`: Shimura's Main Theorem I in Deligne's adelic form on `Y₃` (uniformization, holomorphy,
and reciprocity at CM points).

The pending reading of the removed row moves to that row. The question is whether the PEL moduli scheme with its
uniformization is the canonical model at level `K₃`. dcy3-used §4 lists the clauses the proof reads:
* the uniformization `B^×_+ \ (ℍ × G(𝔸_f)) / K₃ ≃ Y(ℂ)`;
* the holomorphy of `τ ↦ Ψ(τ, g)`;
* the reciprocity law at the one CM point `√2 + i`.

This is VERIFIED by reading DeligneComponentsY3Used.lean. The rest of dcy3-used's proof is proved material: class
number one of `𝒪`, Tau Ceti's Artin map with Steinitz, and a `decide` table over `𝒪/3𝒪`.

## 4. Checks (all VERIFIED; one Lean process at a time)

* **Base (094bdd96 + the local drop-in):**
  * `lake build +ZInQKernel.OneProof.Main` OK, with standard axioms;
  * DumpCompact (scratch/dcy3-fold/DumpCompact.lean: the constants of every `ZInQKernel.OneProof` and
    `ZInQKernel.Contrib.OneProof` module in Main's environment, a superset of scratch/one-proof/DumpCompact.lean)
    found 16935 constants (hashes_before.txt);
  * PruneScan: 51 fields, 0 unused (prunescan-base-out.txt).
* **After step 1:** build OK; PruneScan as in §1.1.
* **After step 2:**
  * `lake build +ZInQKernel.OneProof.Main` OK (13686 jobs);
  * `frozenTarget` has the standard axioms, and its type is identical to the base;
  * PruneScan: OpenResearchLeaves24 26, OpenTextbookLeaves11 11, OpenAddedLeaves17 12, OpenGlue7 1, so 50 fields,
    0 unused, prune set empty (prunescan-after-out.txt).
* **DumpCompact + cmp_hashes.py** (cmp_hashes_out.txt): base 16935, after 17037.
  * **Removed 9:** exactly the 9 projections of the pruned fields.
  * **New 111:** all in `ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used`, the contributor module, which is now in
    Main's closure through the TailZ34 import. There are no new helpers in OneProof/H.
  * **Changed 106**, every one of the allowed kinds:
    * generated auxiliaries of the edited bundles `OpenAddedLeaves9`–`17`: `mk`, `mk._flat_ctor`, `rec`, `recOn` and
      `casesOn` change in type (45). The projections after the deleted field change in value only
      (`deligneComponentsX6PrintedAb`, `geomConnOfAlgClosure`, `phiAmpleIsogeny`, `picRepresentableAbVar`,
      `picZeroAbVar`, `weilPairingMumford` and `shimuraIntegralModelRep`; 33);
    * conversions, value only, by one deleted assignment:
      * `addedLeaves9_of_open10`, `addedLeaves9_of_open14`, `addedLeaves10_of_open11`, `addedLeaves11_of_open12` and
        `addedLeaves12_of_open13`;
      * `openAddedLeaves13_of_OpenAddedLeaves14` through `openAddedLeaves16_of_OpenAddedLeaves17`.
    * `addedLeaves8_of_open9`: type, the binder `hY3`;
    * `sixContactMin_of_open11` to `_open27`: type, the binder `hY3` (17);
    * `sixContactMin_of_open28`: value only.

    `_open29`–`_open31` and `frozenTarget` keep their hashes, and no other constant changed.
* **scratch/contrib-kit/DischargesTest.lean** (output saved in DischargesTest-output.txt): the same 8 discharges and
  controls as before (t1 still assumes `QuotientP1Coordinate`; t3 on `cartierSmooth` is flagged for `sorry`). There
  are now 61 open hypotheses (62 at the base). The previously saved output was stale (OpenResearchLeaves23); the
  bundle name in it is now OpenResearchLeaves24.
* **Docs:**
  * `lake env lean scripts/one_proof/OpenStatements.lean` wrote 61 open hypotheses into open-statements.json, which
    is committed;
  * `render_open.py` fails on this base (§5).
* FaithCheck was not needed: no HDec copy was deleted.

## 5. Not done, and why

* **`render_open.py` fails on the base, independently of this task (VERIFIED).** kinds.tsv keys the six h29-ne3
  `frozenTarget` rows by leaf name:
  * `tyzLemma29PrintedNe3`, `tyzThm21At31`, `tyzProp23Printed`, `tyzTestVectorExists`, `legendreThreeSquares` and
    `jonesPallX2Y2Z16`.

  Main.lean's binders, from the same leaf-fold29 commit, are:
  * `hL29`, `hT21`, `hP23`, `hfx`, `hL3s` and `hJP`.

  Rows of fields that are not removed are outside this task's allowed edits, so **OPEN.md, pages-wanted.md,
  CONTRIBUTING.md and STATUS.md are not regenerated in the repository**. They were already stale at the base
  (STATUS.md says 55 H hypotheses, OpenResearchLeaves23). A temporary copy, with only the six keys renamed to the
  binder names, gave:
  * `render_open.py`: "50 H hypotheses, strictest 39/11, 11 others";
  * `render_open.py --check`: "ok: 61 open hypotheses, all classified; 4 generated files up to date".

  Once leaf-fold29 fixes the keys and applies the drop-in, rerunning the two commands on this branch regenerates the
  docs.
* **The base build defect** (the h29-ne3 drop-in): see the top of this report.
* `docs/one-proof/frontier-crosswalk.tsv` still has the row `H-169 deligneComponentsY3PrintedAb`. That file is
  outside this task's allowed edits and is not touched by the regeneration scripts.
* **One place where the edit goes beyond pure deletion plus binders:** the import of DeligneComponentsY3Used added to
  TailZ34. It is needed because the supplying theorem lives in a Contrib module that comes after TailZ33. As in
  r6-nf's TailZ26 import, no other new module enters TailZ34's environment.

## 6. `frozenTarget`: removed and added hypotheses

* **Removed:** `OpenAddedLeaves17.deligneComponentsY3PrintedAb : ShimuraGlue.DeligneComponentsY3PrintedAb`. This is
  Deligne's theorem on the connected components of `Sh_{K₃}` for `G = B^×` on one fine witness `Y₃`, printed form on
  abelian schemes (Sém. Bourbaki 389 Thm 2.4, §3; PSPM 33 2.1.3, 2.6.3; locators UNVERIFIED). It was GLUE/GLUE.
* **Added:** none. The binders of `frozenTarget` are the same four bundle types and eleven Props. `OpenAddedLeaves17`
  has one field fewer.

## 7. State of the branches

| branch | merged | used |
|---|---|---|
| origin/wip/leaf-fold29 094bdd96 | base | — |
| origin/wip/dcy3-used 36240662 | already in the base | `DCY3Used.y3Connected_of_leaves`; the consumer list of dcy3-used §2 |
| origin/wip/h29-ne3 | already in the base | `scratch/h29-ne3/TYZLemma29Mod2.lean` copied **locally only** (uncommitted) to build Main |
| r6-nf tools | copied to scratch/dcy3-fold/ | PruneScan.lean, DeadCascade.lean, DumpCompact.lean, cmp_hashes.py, prune_lib.py (`drop_assign` also matches `field :=` at end of line) |
