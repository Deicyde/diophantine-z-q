# leaf-fold4 (2026-11-13)

**Result.** `HDec.HSyn.sixContactMin_of_open4 (r t l g) : ZInQ.SixContactMin` compiles with no `sorry` and only
`[propext, Classical.choice, Quot.sound]`. It compiles both in the olean chain and as the flat file
`scratch/leaf-fold4/Leaves4.lean`, and its conclusion is the kernel's own `ZInQ.SixContactMin`. It has
**66 hypotheses: 26 research + 19 textbook + 20 added leaves (13 LEAF, 7 LEAF?) + 1 glue**
(`HeckeVertWitness`). leaf-fold3 had 68 hypotheses, 6 of them glue. Report: `docs/research/leaf-fold4.md`
(§1 result, §2 table of every field, §3 leaves by theory, §4 h-decomposition patch, §5 checks, §6 what was
not folded).

**Folded.**
- hecke-rest: `ChartProper` and `ChartQuasiFinite` are proved.
- period-glue: `HauptmodulUnique` is proved; `PeriodMapGlue` rests on leaves (new leaf candidate
  `CMDescends`); `QMDenZeroCM3` becomes a theorem from R4 plus the leaf candidates `GammaStarGen` and
  `ValenceBoundGammaStar`. The kernel theorems `autOInnerFinite` and `leafSkolemNoether` are used directly.
- spread-out: `AbVarSpreadsOut` rests on 3 EGA IV leaves, via the kernel's Contrib theorem.
- zariski-conn: `ProperSmoothGenConnected` is replaced by Zariski's connectedness theorem.
- t5-torsion: T26 is a theorem from T5, and `DivisiblePoints` is no longer needed (G12 is re-proved from T5).
- t40-clash: T40 is replaced by `X0Transitive` (the kernel's `x1RationalCusp_of_x0Transitive` is now
  importable).
- Kernel theorems over the chain's HDec copies were accepted by definitional unfolding with no extra proof
  (`toAbVarK4`).

**Not folded.**
- vert-witness: it would raise the glue count from 1 to 3.
- homlattice: it would add one hypothesis (+1).
- kerwild-fix: it lowers no count.
- frobchain-contrib: its Props are the kernel's, not the chain's copies.

**Remaining.**
- The glue Prop `HeckeVertWitness` (Lemma NV).
- Human checks of the flagged leaf candidates `CMDescends`, `GammaStarGen` and `ValenceBoundGammaStar`.
- Merging the h-decomposition patch.
