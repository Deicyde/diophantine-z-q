# pn-adopt: Proposition N adopted into the project

**Files.**
- `ZInQKernel/Hypotheses/TYZInputs.lean` (new): the encoding, moved verbatim from
  `scratch/pn-design/PropN.lean`: `gNat`, `gi`, `twoTwoI`, `LemmaTwoEight`, `GenusData`,
  `TYZInputs`, with their docstrings and TYZ line locators. Namespace `ZInQ.PropN`.
- `ZInQKernel/RouteK/PropN.lean` (new): everything else, verbatim: `LamAdm`, `Lam`, the
  `part_`/`n2_`/`final_` helpers, `lemmaN1_core`, `lemmaN2`, `finalStep`, `matching`, `lemmaN1`,
  `genusSums_eq_zero`, `tyzRow5b_of_tyzInputs`, `tyzThm35ReadingA_of_tyzInputs`, `Witness`.
- `ZInQKernel/MainLiterature.lean`: new theorem
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzInputs_functionalEquation5_grossZagier`
  `(hH : SixContactMin) (hT : PropN.TYZInputs) (hF : FunctionalEquation5) (hG : GrossZagier) :
  FrozenTarget`, proved from the `tyzRow5b` variant and `PropN.tyzRow5b_of_tyzInputs`.
- `ZInQKernel.lean` (two imports), `scripts/print_axioms.lean` (8 entries),
  `scratch/pn-adopt/` (log, print_axioms output). `scratch/pn-design/PropN.lean` unchanged.

**Docstrings.** TYZInputs.lean: what `TYZInputs` encodes (I1–I7 as printed in
arXiv:1411.4728v1; journal version not compared); each field a consequence of a printed statement
(pn-design §2); the two points not literally printed: the typing of `β` (needs `ℍ'_n/ℚ` Galois,
from TYZ Proposition 3.2(1) and the dihedral structure of ring class fields, Cox Lemma 9.3) and
T1 (Theorem 3.3's constant is not printed; Proposition N needs the `d₁` factor to be `𝓛(d₁)` up to
a 2-adic unit, uniformly in `χ`); the reviews (rv-tyz-inputs, pn-design). PropN.lean: the Lean
proof of Proposition N (nt-tyz §4); it replaces the two model reviews (rv-nt-tyz, rv-prop-n) of
the argument by a kernel-checked proof from the encoding; list of the main steps.
Note: `docs/research/rv-tyz-inputs.md` is cited but lives on branch `wip/rv-tyz-inputs`. It is
not merged into this branch, since this task may not add files outside its list.

**Outcome.** `lake build ZInQKernel` succeeds (9924 jobs). `lake env lean scripts/print_axioms.lean`
prints 77 entries (69 before, plus 8). Every entry shows exactly `[propext, Classical.choice,
Quot.sound]`, including `tyzRow5b_of_tyzInputs`, `tyzThm35ReadingA_of_tyzInputs`, the four lemmas,
`Witness.genusData_nonempty` and the new headline variant. `scripts/check_target.py`:
FrozenTarget matches. grep finds no `sorry`, `axiom`, `native_decide`, `implemented_by` or `extern`
in the new files. The only hit is the word in the comment "sanity check, no `sorry`".

**Changes beyond moving code.** New module docstrings. One section comment changed from "The four
lemmas (statements fixed; proofs `sorry`)" to "The four lemmas". One bullet added to
MainLiterature's module docstring. No statement or proof changed. Lint warnings that remain,
inherited from the scratch file: an unused variable `hn` (PropN.lean ~L1085), and Mathlib's
module-system notice on the GaussianInt import.
