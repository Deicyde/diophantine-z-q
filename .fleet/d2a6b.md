# d2a6b (fleet summary)

**Verdict: A6 rides on `Y3FullThreeRepZ30`, so the D2/A6 reroute is count-neutral.**
- `shimuraIntegralModelRep` stays out of the bundle. A6 and the kernel field's good reduction (L529-530, L557-558)
  are proved in Lean from y3-route-a's `Y3RouteA.Y3FullThreeRepZ30`. That leaf is already a bundle field on
  f3402e89.
- The proof (`D2A6.hasGoodReduction_of_z30`, new file `ZInQKernel/Contrib/OneProof/A6Z30.lean`) has four steps:
  - the classifying point;
  - the valuative criterion over `ℤ[1/30]`;
  - base change of the universal abelian scheme;
  - its generic fibre identified with `A` by rigidity.
- The only bridge needed is kernel level structure → printed level structure (`Y3Fix.ofKer`) over `ℚ`-schemes. It
  was already proved in the tree; it is on the spot (provenance (c)) and adds no field.
- Every `p > 324` satisfies `p ∤ 30`, so the `ℤ[1/30]` model covers more primes than the manuscript's `S`.

**Count** (kinds.tsv of f3402e89): strict 5/24 on 29 → **5/24 on 29**; strictest the same. d2a6-reroute's version
gave 5/25 on 30.
- Removed: `sga7_IX_3_5_ForwardGeom_Def34`.
- Added: `elliotWildInertiaTrivial` (ELLIOT, L817-818, GLUE).
- Mapped from fields already in the bundle: `silverbergZarhinThm35` (gives `raynaudSemistableSHOr`) and
  `y3FullThreeRepZ30` (gives `y3FineModuliAbP` and R6U).

On this base y3-route-a is already folded, so "this base alone" and "with y3-route-a's autofold" are the same.

**Compiles** (only the standard axioms; no `sorry`; nothing imports OneProof.Main):
- A6Z30.lean (new) and D2A6Wrap.lean (edited: `R6U = RaynaudWildNF ∧ Y3FullThreeRepZ30`).
- D2A6Chain.lean, regenerated on TailZ80's `sixContactMin_of_open73`, the bost-gr9 GR9 copies: 103 declarations
  and 29 structures.
- scratch/d2a6b/BypassFold.lean on TailZ83: `OpenResearchLeaves58` and `sixContactMin_of_open77`.
- 34 `#print axioms`, all standard.

**Checks on f3402e89:**
- **Closure check:** in the closure of `open77`, the IX 3.5 row, R6 and `ShimuraIntegralModelRep` are absent.
- **PruneScan:** every top field is used, before and after, and no field of the live chain lost its last reader.
  `mulEtaleAbelianScheme` is a field only of old, unused textbook generations.
- **Strict dry run:** nothing is discharged outright on this base. Both earlier outright discharges are folded
  (TailZ81/82), and autofold refuses the old spec. The bypass count uses autofold's own `counts`/`must_be_glue`.

**For the lead:**
1. Copy BypassFold.lean to TailZ84.
2. Switch Main to `OpenResearchLeaves58` / `sixContactMin_of_open77`.
3. Replace the `sga7_IX_3_5_ForwardGeom_Def34` kinds row with scratch/d2a6b/kinds-rows.tsv, and drop its claims row.

**Remains:**
- Cor. 3.3 (height-row readers) is unchanged.
- The relative Lemma P point inside `y3FullThreeRepZ30` is still open.
- Buzzard's print for L443-446 is unread.

**Manuscript check** (report §8):
- **gap filled:** L529-530 and L817-818 (citation).
- **OK:** L383-384, L453-462, L557-558, L752-753/L781, L814-816.
- **unverified:** L443-453, L464-472 (the polarization; the torsion-freeness itself is OK), L472-477.
- **No errors found.**

Report: docs/research/d2a6b.md; log and generators: scratch/d2a6b/.
