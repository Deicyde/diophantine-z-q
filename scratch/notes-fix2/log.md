# notes-fix2 log

- 10:25 start (fresh; no earlier log).
- Item 7 check: `scratch/hdec-adopt2/axioms_section.lean` has 93 lines and 90 `#print axioms`
  lines (`wc -l`, `grep -c`); 272 − 90 = 182. VERIFIED. log.md:32 corrected.
- Item 4: the five docstring passages of `QMPolar.lean` replaced by the kernel `QM/Polar.lean`
  wording (python exact-replace); `diff` against the kernel file afterwards shows only the
  intended differences (kernel imports `LeafQM`'s order instead of copying it, one line break,
  the `#print axioms` trailer).
- Item 3: `QML3` docstring = kernel `QM/Structures.lean` wording plus a provenance sentence.
- Item 1: kernel statement and proof of `fibre_conjugates_isomorphic` copied (the scratch's
  `exists_fibre_object` and `conj_twist_of_rational` have the same signatures as the kernel's).
- Item 6: header of `R16Transfer.lean` rewritten for its three declarations.
- 10:27 `lake env lean scratch/rv-qm-polar/QMPolar.lean`: exit 0, 59 s, 0 errors (linter and
  deprecation warnings only, as before), 10/10 `#print axioms` outputs exactly
  `[propext, Classical.choice, Quot.sound]` (`qmpolar.out`). VERIFIED.
- 10:28 `lake env lean scratch/rv-blueprints/R16Transfer.lean`: exit 0, 96 s, no warnings;
  `BPModCurves.exists_quotient_transfer` depends on `[propext, Classical.choice, Quot.sound]`
  (`r16.out`). VERIFIED.
- 10:30 `lake build ZInQKernel.HDecomp.A6.A6` (the import of QMLeaves.lean): exit 0, 49 s
  (`build_a6.out`).
- 10:31 `lake env lean scratch/leaf-qm-fp/QMLeaves.lean`: exit 0, 27 s, 0 errors, 28/28
  `#print axioms` outputs standard, including `LeafQM.AV.fibre_conjugates_isomorphic` with the
  strengthened (kernel) statement (`qmleaves.out`). VERIFIED. So item 1 is the copy, not the
  "superseded" fallback.
- Load during all runs 18-22, available memory > 120 GB; one Lean process at a time.
