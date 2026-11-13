# g0-assemble2 (2026-11-13)

**Result.** Every wave-26 and wave-27 result is composed in one Lean file over the current
`scratch/h-decomposition/Leaves.lean`, which includes pin-apply. The file is
`scratch/g0-assemble2/G0Assemble2.lean` (70 514 lines). `assemble.sh` generates it from
`Leaves.lean`, g0-assemble's 18 parts and 21 new parts. It proves:

    HSyn.sixContactMin_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
      ZInQ.SixContactMin

VERIFIED: `lake env lean` exits 0 in 829 s, with 0 errors and no `sorry`. All 200
`#print axioms` reports are `[propext, Classical.choice, Quot.sound]`.

**`GluePieces3` has 40 fields: 15 LEAF, 3 LEAF? and 22 GLUE.** g0-assemble's `GluePieces2` had 27
fields: 5 LEAF, 1 LEAF? and 21 GLUE. Every field is listed with its kind and source report in
`docs/research/g0-assemble2.md` §2.

Proved outright by wave 27 and applied here:
- FiniteDescends, RigidityHom, UnramifiedSup, DirichletOfFinite (from T17), and the three Swan
  Props.

Proved from leaves:
- G12Weight and DetTate.

Replaced by smaller named Props:
- the four metrization Props, by product-height's two;
- FS5, by fs5-nocm with mobius-glue, curve-facts and aut-o-finite;
- FibreQMPeriod, KernelFieldExists (kernel-field, including G4), FibreCoverExists, HodgeLineBC and
  G10.

New here:
- fibre-cover's `InnerTwistCount` is proved, from aut-o-finite's four-class computation.
- H5's `NeronModelMinimal` is applied (h5-glue).
- `LinkedTateData` is reduced to a smaller joint glue Prop, `LinkedTateLocal`, plus T7 (from
  g14-trace and g15-ram).
- g0-assemble's QM-PIN field `ModelG3G6` is reduced to `ModelG3` alone. G6's division clause comes
  from `FibreSimple`, and its noncommutativity is **proved** from `MulIsogeny` by a dimension
  argument.
- G9 is folded in from `ZInQKernel/Contrib/G9`: `AbVarBaseChange` (glue) and `R10Weights` (leaf).

**Finding 1: the bundle could never be supplied.** Leaves.lean's `ResearchLeaves` cannot be
inhabited:
- `r1an` and `r17` have `opaque` placeholder types, so no proof of them can exist;
- neither field is used by any proof.

The fix is `ResearchLeaves3` (24 fields). It drops both placeholders and keeps only H5's finiteness
half. The concrete forms of the placeholders are `GluePieces3` fields (`carayolR17`,
`r1bFamily`). The seven consumers on the route are copied with `r : ResearchLeaves3`.

**Finding 2: ten unused fields.** Ten `TextbookLeaves` fields are never used on the route: t1,
t2, t3, t4, t16b, t20, t21, t28, t29a, t29b. They are not pruned here, because 31 declarations take
`t`.

**What remains.**
- 22 glue Props. Two of them, `propTSAll` and `linkedTateLocal`, are SPECULATIVE.
- 18 literature statements in `GluePieces3`, plus 24 + 35 bundle leaves.

All are listed by name in the report's §6 and §7.
