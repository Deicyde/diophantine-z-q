# p1-quot3 (fleet summary)

**Result: (1) proved; (2) not done.** p1-quot2's residual glue `HDec.MCRGlue.TameQuotientSmoothRelDim` (the smoothness
half of mcr-glue's L3) is now a theorem. It uses only the chain's existing textbook field `regularSmoothPerfect`
(Stacks 00TV) and adds no new leaf. So all of L3 (`TameQuotientSmooth`) is proved. L4 `SmoothModelOfP1` is still
a consequence (GLUE).

`HDec.MCRQuot.quotientP1Coordinate_of_fields4` discharges `OpenGlue7.quotientP1Coordinate`. Its inputs are:
- new leaves: `LichtenbaumProjective` (printed), L2 `FiniteQuotientExists` (printed), L4 `SmoothModelOfP1`
  (consequence), `EdixhovenFixedSmooth2` (printed);
- chain fields: `regularSmoothPerfect`, `mumfordTorsionAlgClosed`, `mumfordGroupLaw`,
  `shimuraMainThmIDeligneY3AbU`, `uniformizationLeafAll`, `gagaMorphism`.

Following the task's note, `HeckeIrreducible` now comes from dcy3-used's `DCY3Used.y3Connected_of_leaves`. The
fold's strict GLUE change is **0** (p1-quot2's was +1). Autofold accepts it without `--allow-rise`: 46/10 on 56 →
49/10 on 59. It would pay −1 only if L4 were replaced by a printed leaf or proved.

**What compiles (VERIFIED):**
- `lake build ZInQKernel.Contrib.OneProof.QuotientP1Smooth`, including the new helpers
  `QuotientP1/TameInvariants.lean` (algebra) and `QuotientP1/TameQuotSmooth.lean` (schemes). No `sorry`, standard
  axioms.
- `#discharges` prints `DISCHARGES [OpenGlue7.quotientP1Coordinate] by quotientP1Coordinate_of_fields4`, with
  standard axioms.
- The autofold dry run's generated module compiles (`sixContactMin_of_open30`, standard axioms).
- The proof of L3-smooth:
  - normality of invariant rings is proved elementwise (prime avoidance and norms);
  - over a perfect field, the invariants of a smooth algebra of dimension ≤ 1 are smooth (Stacks 00TV);
  - with `p ∤ |G|`, invariants commute with base change (Reynolds operator);
  - flatness holds because the invariants are a retract;
  - EGA IV 17.5.1 (Mathlib `Algebra.Smooth.of_formallySmooth_fiber`) gives smoothness;
  - relative dimension 1 because the fibres of `𝒵` and `𝒴` have equal dimension.

**What remains:** L4. I found no printed statement of it. The vendored libraries now have Zariski connectedness
(proved, CloudW02), coherent cohomology of families, local constancy of χ, Riemann–Roch on fibres and cohomology and
base change for positive line bundles (CloudW07). What is missing is the base-point-freeness and fibrewise
isomorphism steps. Report §5 gives a step plan of several thousand lines.

Report: docs/research/p1-quot3.md. Log: scratch/p1-quot3/log.md.
