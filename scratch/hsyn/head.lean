import Mathlib
import ZInQKernel.Hypotheses.JHeight

/-!
# H = `ZInQ.SixContactMin` decomposed into literature leaves and glue (synthesis)

Companion of `docs/research/h-decomposition.md`. Check with
`lake env lean scratch/h-decomposition/Leaves.lean`.

Layout.
* `PkgI2` (copied from the report of the reduction-theory package): genuine Mathlib definitions
  of abelian varieties (`Grp (Over (Spec K))`, proper, smooth, geometrically integral), good
  reduction (abelian schemes over a DVR), torsion points and Galois/inertia actions, and the
  reduction-theory leaves stated over them, with two glue lemmas proved.
* `GlueConductor` (copied from the report on Glazer's conductor bound): the elementary core of
  steps D1-D5, proved; the two different-ideal leaves stated over Mathlib.
* `HSyn` §0-§1: cheap definitions (the absolute Galois group of `ℚ`, places, Frobenius,
  continuous `GL_n(ℚ̄_ℓ)`-representations, cusp forms with nebentypus, normalized eigenforms) and
  the leaves statable over them.
* `HSyn` §2: every other leaf as a **placeholder** `opaque … : Prop`. **A placeholder carries no
  content**: it is an uninterpreted proposition whose docstring records the exact statement and
  reference. A theorem with a placeholder among its hypotheses says nothing until the placeholder
  is replaced by a genuine statement.
* `HSyn` §3: glue proved here, and the top-level theorem from all the leaves to
  `ZInQ.SixContactMin`, through `ZInQ.JHeight.JHeightBound` and the existing Lean proof of the last
  step (`ZInQ.JHeight.sixContactMin_of_jHeightBound`). The glue G1-G19 is `sorry`.

No `axiom` declarations. Leaf numbering (R1-R22 research-level, T1-T25 textbook) is that of the
note's §2.
-/
