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
