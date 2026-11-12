import Mathlib
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Compiler.Precision.HeightConstant

/-!
# H = `ZInQ.SixContactMin` decomposed into literature leaves and glue (synthesis)

Companion of `docs/research/h-decomposition.md`. Check with
`lake env lean scratch/h-decomposition/Leaves.lean`.

Layout (each block copied verbatim from a report's compiled draft, inside its own section).
* `PkgI1` (pkg-I1): the quaternion order, genus-2 theta constants, Igusa invariants; the leaves
  `ThetaModularity` (R4), `QMHauptmodul` (a consequence of R2-R4, not counted as a leaf),
  `IgusaClebschSeparation` (T28); proved glue for A1, A5, A7, A10, F1.
* `PkgI2` (pkg-I2): abelian varieties as `Grp (Over (Spec K))`, good reduction as abelian schemes,
  torsion points with Galois/inertia action; the reduction-theory leaves; two proved consequences.
* `PkgI3` (pkg-I3): bundled abelian varieties `AbVar` with `Hom`, Tate modules `T_ℓ`, `V_ℓ` and the
  Galois representation; Faltings 1983 (R9) and Mumford's theorems; proved E1 and C2 glue.
* `PkgI6` (pkg-I6): continuous Galois cohomology leaves for B2, local Kronecker–Weber, local
  reciprocity with upper numbering, ramification leaves; the proved Brauer step of B2.
* `GlueConductor` (glue-conductor): the elementary core of D1-D5, proved; two different-ideal
  leaves stated over Mathlib.
* `GlueAssembly` (glue-assembly): F2 on Mathlib's Weil heights, E2-E4/F3 arithmetic, the final
  constant and F4: `GlueOutputs S → SixContactMinAt S`, proved; C8, E1, E2, F3 glue.
* `HSyn` §0-§1 (from the hdec-faithful draft): the absolute Galois group of `ℚ`, places,
  Frobenius, continuous `GL_n(ℚ̄_ℓ)`-representations, cusp forms with nebentypus, normalized
  eigenforms, and the leaves statable over them.
* `HSyn` §2: every other leaf as a **placeholder** `opaque … : Prop`. **A placeholder carries no
  content**: it is an uninterpreted proposition whose docstring records the exact statement and
  reference. A theorem with a placeholder among its hypotheses says nothing until the placeholder
  is replaced by a genuine statement.
* `HSyn` §3: the leaves bundled (`ResearchLeaves`, `TextbookLeaves`) and the top-level theorem
  `sixContactMin_of_leaves : ResearchLeaves → TextbookLeaves → ZInQ.SixContactMin`, which is
  `glueOutputs_of_leaves` (glue G1-G17, G19, `sorry`) followed by glue-assembly's proved
  `GlueOutputs Mult.S_mul → SixContactMin` (G18-G20, checked against the real
  `ZInQ.SixContactMin`). `GlueOutputs` is a numerical interface, not a leaf.

Other `sorry`s, all glue statements of the reports: `PkgI2.goodReduction_of_QM_rational3` (A6),
`PkgI6.artinConductor_le_of_upper` (D4), `PkgI6.sq_principalUnits` (D3; proved in another form
as `GlueConductor.exists_sq_eq_one_add`).

No `axiom` declarations. Leaf numbering (R1-R22 research-level, T1-T29 textbook) is that of the
note's §2.
-/
