# p1-quot3 (fleet summary)

**Result: `quotientP1Coordinate` now rests on three printed leaves and chain fields only. The fold pays −1**
(autofold dry run, no `--allow-rise`: strict 46/10 on 56 → 49/9 on 58; strictest 45/11 → 48/10).

The final theorem is `HDec.MCRQuot.quotientP1Coordinate_of_fields5` (`ZInQKernel/Contrib/OneProof/QuotientP1Model.lean`).
Its inputs:
- printed leaves: `LichtenbaumProjective`, L2 `FiniteQuotientExists`, `EdixhovenFixedSmooth2`;
- chain fields: `regularSmoothPerfect`, `mumfordTorsionAlgClosed`, `mumfordGroupLaw`, `shimuraMainThmIDeligneY3AbU`,
  `uniformizationLeafAll`, `gagaMorphism`.

1. **L3 is proved.** `TameQuotientSmoothRelDim`, the smoothness half of the SGA 1 tame quotient, follows from
   `regularSmoothPerfect` alone (Stacks 00TV):
   - normality of invariant rings, proved elementwise;
   - the Reynolds operator, so invariants commute with base change;
   - flatness, because the invariants are a retract;
   - EGA IV 17.5.1;
   - relative dimension 1 from the fibre dimensions.
2. **L4 `SmoothModelOfP1` is bypassed, not proved in general.** The generic coordinate (the descent of `π`) takes
   the values `0, ∞, −16/27` at the CM points, whose closures are pairwise disjoint (Edixhoven). `P1Model.exists_p1Coordinate`
   extends it to `𝒵 ≅ P¹_{ℤ_(p)}` by charts. The inputs are Zariski connectedness (proved in CloudW02), the vendored
   extension theorem over codimension ≥ 2, the DVR at the generic point of the special fibre, the third section to
   rule out a zero or pole at `ξ`, a finite map to `P¹`, and polynomial chart rings (the reduced coordinate is
   transcendental).
3. Following the task's note, `HeckeIrreducible` now comes from dcy3-used's `y3Connected_of_leaves`.

**What compiles (VERIFIED):**
- `lake build ZInQKernel.Contrib.OneProof.QuotientP1Model`, including the helpers `QuotientP1/TameInvariants`,
  `TameQuotSmooth` and `P1ModelA`–`E`. About 2,600 new lines; no `sorry`; standard axioms.
- `#discharges` prints `DISCHARGES [OpenGlue7.quotientP1Coordinate] by quotientP1Coordinate_of_fields5`, with
  standard axioms.
- The autofold dry run's generated module compiles (`sixContactMin_of_open30`, standard axioms).

**What remains:**
- General L4 (no sections) is not proved, and nothing needs it now.
- The three leaves keep their earlier ratings. Lichtenbaum and Edixhoven are flagged unread, and every locator is
  UNVERIFIED.

Report: docs/research/p1-quot3.md. Log: scratch/p1-quot3/log.md. Spec: scratch/p1-quot3/autofold.json.
