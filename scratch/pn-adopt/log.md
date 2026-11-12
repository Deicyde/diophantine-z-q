# pn-adopt log

## Step 1 (split)
- `ZInQKernel/Hypotheses/TYZInputs.lean`: PropN.lean L1–2 (imports), L31–128 (gNat, gi, twoTwoI,
  LemmaTwoEight, GenusData, TYZInputs), closed with `end ZInQ.PropN`.
- `ZInQKernel/RouteK/PropN.lean`: imports GaussianInt + Hypotheses.TYZInputs; L31–36 header
  (noncomputable section, namespace, open), L130–1680 verbatim.
- diff of concatenated bodies against the scratch file: only blank lines differ.
- Only comment change: section header "The four lemmas (statements fixed; proofs `sorry`)" ->
  "The four lemmas".

## Step 2 (docstrings)
- New module docstrings in both files (lines ≤ 100).

## Step 3 (main variant, imports, print_axioms)
- MainLiterature.lean: import RouteK.PropN; new theorem
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzInputs_functionalEquation5_grossZagier`
  (from the tyzRow5b variant and `PropN.tyzRow5b_of_tyzInputs`); one bullet added to the module doc.
- ZInQKernel.lean: imports Hypotheses.TYZInputs, RouteK.PropN.
- print_axioms.lean: +8 entries (new variant, tyzRow5b_of_tyzInputs, tyzThm35ReadingA_of_tyzInputs,
  lemmaN1_core, lemmaN2, finalStep, matching, Witness.genusData_nonempty).

## Step 4 (checks)
- `lake build ZInQKernel`: success (9924 jobs). Warnings in new files: module-system notice on the
  Mathlib import, one unused variable `hn` (PropN.lean ~L1085, inherited from the scratch file).
- `lake env lean scripts/print_axioms.lean`: 77 entries (69 before + 8), every one
  [propext, Classical.choice, Quot.sound]. Output: scratch/pn-adopt/print_axioms.out.
- `python3 scripts/check_target.py`: "FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean".
- grep: no `sorry` in the new files (only the word in the comment "no `sorry`" of the Witness
  section); no axiom/native_decide/implemented_by/extern.
- scratch/pn-design/PropN.lean unchanged.
