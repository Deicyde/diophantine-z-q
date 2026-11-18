# d2a6-reroute (fleet summary)

**Result.**
- **The SGA 7 IX 3.5 row leaves** (`sga7_IX_3_5_ForwardGeom_Def34`). D2 now goes through sz-raynaud's `RaynaudWildNF`
  (L814-818). A6 goes through the proper model and its universal abelian scheme (L529-530).
- **`ElliotWildInertiaTrivial` discharges a field.** Together with `silverbergZarhinThm35` and
  `shimuraIntegralModelRep`, it replaces the IX 3.5 row.
- **A third reader of R6 is rerouted the same way:** the kernel field's good reduction (L557-558). sz-raynaud's report
  did not list it.
- **The stop rule did not trigger.** A6 needs only the manuscript's L443-477 (sgr-split's `ShimuraIntegralModelRep`)
  plus textbook facts that are proved in Lean (valuative criterion, `ℤ_(p) → O`, rigidity).
- **Cor. 3.3 stays.** Its live readers are SS2 and SS3 (semistable base change, behind the height rows R18-R22 and
  `StableHeightFinite`), not D2 or A6. So only one of the two SGA 7 rows can leave this way.
- **The fold also discharges `raynaudSemistableSHOr`** (IX 4.7) from SZ 3.5. This is sz-raynaud's autofold, included
  because `RaynaudWildNF` needs SZ 3.5.

**Count** (base kinds.tsv): 5/24 on 29 → **5/25 on 30**, strictest the same. GLUE rises by one: ELLIOT and the
integral model both count GLUE. The lead must accept this, since the strict autofold would need `--allow-rise`.

**Compiles** (all standard axioms, no sorry, nothing imports OneProof.Main):
- **New files under `ZInQKernel/Contrib/OneProof/`:**
  - `D2WildNF.lean`: D2 on `RaynaudWildNF`.
  - `A6IntModel.lean`: `D2A6.hasGoodReduction_of_intModel`, `goodRedTorsionT`, `QMModelG3U`,
    `modelG3G6_of_leavesU`.
  - `D2A6Wrap.lean`: `R6U := RaynaudWildNF ∧ ShimuraIntegralModelRep`, with five wrappers.
  - `D2A6Chain.lean`: generated, 102 declarations and 29 structures copied, ending in `sixContactMin_of_open72_u`.
- **The bypass fold** `scratch/d2a6-reroute/BypassFold.lean` (from gen/gen_bypass.py, built on TailZ79). It defines
  `OpenResearchLeaves54` and `sixContactMin_of_open73`. kinds-rows.tsv holds the three new rows.
- **Closure check:** the old statements are absent from the new top; Cor. 3.3 is present.
- **#discharges:** 163 lines, of which 146 are noise from the copied structures.
- **Autofold:** spec and strict dry run for `raynaudSemistableSHOr` give 5/24 → 5/24; the dry-run module compiles.

**Remains.**
- Lead's call on the GLUE +1 trade.
- Removing Cor. 3.3 needs the height rows rerouted to a stable height that does not need SGA 7 IX 3.3.
- `shimuraIntegralModelRep` keeps sgr-split's pending reading (relative Lemma P, level at `3 ∣ D`). The manuscript's
  construction at L443-477 is not formalized: the manuscript-check verdict there is "unverified".
- No PruneScan was run after the reroute.

**Manuscript check** (report §7):
- L529-530 and L817-818: gap filled.
- L443-477 and L819-821: unverified.
- L383-384, L557-558, L752-753/L781, L814-815, L816-817: OK.
- No errors found.

Report: docs/research/d2a6-reroute.md; log and generators: scratch/d2a6-reroute/.
