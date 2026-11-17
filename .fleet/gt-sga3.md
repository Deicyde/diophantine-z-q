# gt-sga3: SGA 3 VI_B 3.10 (`CToPrinted.SGA3_VIB_3_10`), reduced

**Verdict.** The statement is true and not vacuous. It is now **reduced in Lean**, with all glue proved, to a
strictly weaker published-form leaf plus a leaf already in the bundle:

`SGA3IdComp.sga3_VIB_3_10_of_nbhd (hN : SGA3_VIB_3_10_Nbhd) (hG : AVGlue.GeomConnOfRationalPoint) : CToPrinted.SGA3_VIB_3_10`

The theorem is in `ZInQKernel/Contrib/OneProof/SGA3IdComp.lean`. It imports TailZ19 and two vendored CloudW07
modules, has no sorry, and uses only the standard axioms.

* New LEAF `SGA3_VIB_3_10_Nbhd`: `G⁰` contains an open neighbourhood of each `e(s)`. It is a consequence of
  SGA 3 VI_B 3.10 (and EGA IV₃ 15.6.5); locators UNVERIFIED.
* `GeomConnOfRationalPoint` (Stacks 04KV) is already the textbook field `geomConnOfRationalPoint`.
* Strict counts: LEAF unchanged (one out, one strictly weaker in), GLUE unchanged.

**What compiles (VERIFIED).**
* `lake build +Main +Discharges +Contrib.OneProof.SGA3IdComp` exits 0.
* `#discharges` (`scratch/gt-sga3/Discharges.lean`) prints:
  `DISCHARGES [OpenResearchLeaves16.sga3_VIB_3_10] by SGA3IdComp.sga3_VIB_3_10_of_nbhd`,
  still assumes `[SGA3IdComp.SGA3_VIB_3_10_Nbhd, AVGlue.GeomConnOfRationalPoint]`,
  axioms `[propext, Classical.choice, Quot.sound]`.
* Proved along the way:
  * smooth schemes over a field have open compact irreducible neighbourhoods, and any two points of a
    component lie in a common one;
  * `G⁰` is closed under `μ` over any base (`mul_mem`, from 04KV only);
  * the translation through `κ(x)` (`exists_point`);
  * openness via `UniversallyOpen` of the smooth `pr₁`.

**What remains.** The neighbourhood leaf. It carries the full depth of EGA IV₃ §15.6, which the literature
proves through limits to noetherian bases and constructibility of connected fibres, and Mathlib 4.35 has
neither. The reduction shows the leaf is equivalent to the original modulo 04KV.

Report: `docs/research/gt-sga3.md`. Log: `scratch/gt-sga3/log.md`.
