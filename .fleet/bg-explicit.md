# bg-explicit (2026-11-15)

**Result.** The research LEAF `babaGranathRationalAb` (`HDec.QMSplit.Moduli.BabaGranathRationalAb`, Baba–Granath 2008,
with the UNVERIFIED §3.1 CM-table reading) is **proved outright from four fields already in the bundles, with no new
leaf**. Contribution: `ZInQKernel/Contrib/OneProof/BabaGranathRationalAb.lean` (imports TailZ22, ElkiesX6Star,
QMLattice). VERIFIED: builds; standard axioms only.

```lean
theorem BGExplicit.babaGranathRationalAb_of_printed
    (h : HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted)          -- research field elkiesX6StarPrinted
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll)             -- textbook fields
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    HDec.QMSplit.Moduli.BabaGranathRationalAb
theorem BGExplicit.babaGranathRationalAb_of_AL (h : ElkiesX6StarPrinted) (hW : HDec.HeckeRest.ALFixedPoints) : ...
-- axioms (both): [propext, Classical.choice, Quot.sound]
```

**Instances.** Elkies' witness and `π = t`, `t₄ = 1`, `t₃ = ∞`, `t₂₄ = 0`. The field's only content beyond Elkies is
the converse CM clauses, i.e. one CM point of each type. Proof by finite computation on Elkies' conic model
(`conicModelT_of_charts`): the fibres of `t` over `1, 0, ∞` have two points each, so two of the four Atkin–Lehner
images of a point coincide. So the pair is fixed by a nontrivial `w_m` (`rep_rep`, `xr`), so it has CM
(`ALFixedPoints`, a chain theorem from the three textbook fields and the proved T11(b)). Elkies' CM values then
pick the type.

**#discharges:** `DISCHARGES [OpenResearchLeaves22.babaGranathRationalAb] by BGExplicit.babaGranathRationalAb_of_printed`.
It still assumes only the four open fields above. Axioms standard; 63 open hypotheses, 1815 theorems checked.
**Autofold:** `scratch/bg-explicit/autofold.json`. Its dry-run gives strict 46/10 on 56 → 45/10 on 55 and
strictest 45/11 → 44/11. The generated module compiles, with standard axioms.

**Remains / notes.** Nothing open for this field. If elkies-coord's fold of `elkiesX6StarPrinted` lands first,
replace `{n}.elkiesX6StarPrinted` in the spec by its term from `{n}.elkiesX6StarFunctionField`. The CM-assignment
risk now sits only in Elkies' `0/∞` orientation flag, which was already on `elkiesX6StarPrinted`.
Report: docs/research/bg-explicit.md.
