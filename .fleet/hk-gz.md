# Gross–Zagier route: scoped stop

**Keep `hK` open.** The conditional Lean substitution reaches
`HKRefereed.HKConsumed` without MPI/90-69, but still needs two independent
GLUE inputs: `LiCarayolNewformOfModular` for extracting the newform
from the BCDT cusp form, and `PoleCMTraceDictionary` for realizing the
algebraic conductor-one Heegner trace in the existing dictionary. A fold
would replace one GLUE row with two (net +1) and add three pending printed
slots. Nothing was folded; the actual headline delta is zero.

**VERIFIED (Lean).** The five new modules and the scratch substitution
compile. The new code identifies the two formal levels, constructs the
split imaginary quadratic field from BFH, proves the untwisted quadratic
base-change formula and the nonzero derivative, and descends a positive
multiple of the trace after the conjugation comparison. The module theorems
and dry run use only `propext`, `Classical.choice`, and `Quot.sound`.
The initial dependency build missed the one-process constraint because Lake
ignored the wrapper; the final build and checks enforced serialization.

The reading desk still needs to check the Gross–Zagier height consequence
and the trace conjugation sign and cusp correction, along with the scope
of BFH(ii). The locators are **UNVERIFIED** for this reading; no candidate
has a LEAF rating. See `docs/research/hk-gz.md` for the source and manuscript
checks and `scratch/hk-gz/` for the substitution and axioms output.
