# Report: mult-soundness (blueprint `multiplication/soundness/`)

Modules: `ZInQKernel/Multiplication/Soundness/*.lean`, root `ZInQKernel/Multiplication/Soundness.lean`
(imported from `ZInQKernel.lean`). Namespace `ZInQ.Mult` (the chapter's shared design). No `sorry`, no
axioms: every theorem below depends only on `propext`, `Classical.choice`, `Quot.sound` (checked
with `#print axioms`, after merging `wip/mult-formal-log`, which closes `ellLog_add`).
Merged branches: `wip/mult-certificate` (constants, tests, slope predicate, pole obstruction,
constants' properties), `wip/mult-formal-log`.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| soundness/height-constant-integers.md | `ZInQ.Mult.height_constants_int` | proved (`decide`) |
| soundness/height-constants.md | `ZInQ.Mult.heightB0`, `ZInQ.Mult.heightB0_lt_ten`, `ZInQ.Mult.one_lt_log_41_sub` | proved |
| soundness/rational-height-bounds.md | `ZInQ.Mult.rational_height_bounds` (`ratHeight_add3_le`, `ratHeight_div_le`, `ratHeight_neg`, `ratHeight_nonneg`, `ratHeight_inv`) | proved |
| soundness/field-height-bounds.md | `ZInQ.Mult.field_height_bounds` (`hK0_mul_le`, `hK0_add_le`, `hK0_sqrt2`, `hK0_epsilon`, `hK0_epsilon_pow_four_mul_le`, `hK0_ratCast_add_mul_sqrt2_le`) | proved |
| soundness/generator-height.md | `ZInQ.Mult.generator_height` (`canonHeightE`, `canonHeightE_zsmul_genP0`, `log_41_sub_le_two_canonHeightE_genP0`, `two_canonHeight_genP0_gt_one`, `two_canonHeightE_le`, `canonHeightE_zero`) | proved |
| soundness/contact-valuations.md | `ZInQ.Mult.contact_valuations` (general form `contact_valuations_of`) | proved |
| soundness/tests-to-congruence.md | `ZInQ.Mult.tests_to_congruence` (on the individual quantities: `tests_to_congruence_aux`) | proved |
| soundness/local-congruence.md | `ZInQ.Mult.local_congruence` (general form `local_congruence_of`) | proved, with hypothesis `1 ≤ Syntax.M0` (see corrections) |
| soundness/common-group.md | `ZInQ.Mult.common_group` (general form `common_group_of`) | proved |
| soundness/contact-support.md | `ZInQ.Mult.slope_height_le` (general form `slope_height_le_of`) | proved, with hypothesis `1 ≤ Syntax.M0` |
| soundness/box-inequality.md | `ZInQ.Mult.box_inequality` | proved |
| soundness/finite-box.md | `ZInQ.Mult.finite_box_of_slopes` (height part: `finite_box_of_heights`) | TODO |
| soundness/soundness.md | `ZInQ.Mult.multiply_sound` | TODO |
