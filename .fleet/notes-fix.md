# notes-fix (fleet summary)

**Result.** factcheck-w34b is applied, except its items about `Leaves.lean` and h-decomposition.md
(those are leaf-adopt3's). Report: docs/research/notes-fix.md. Log: scratch/notes-fix/log.md.

**Lean (ZInQKernel/HDecomp/QM/).**
- Item 1 is fixed in Lean, not just in the docs. `LeafQM.AV.fibre_conjugates_isomorphic` now
  exhibits:
  - `Y₃` with `R1fpProps` and `π` with `R2fpProps`;
  - a ℚ̄-point `y` with `π(y) = j₀` and `Φ y = [P]`;
  - for every σ, the twist-isomorphic conjugate.

  Same proof (`exists_fibre_object` + `conj_twist_of_rational`), same name, no consumers, so
  print_axioms.lean is unchanged.
- Items 2-4 are docstring-only. Characteristic 0 is now in every Lemma P mention (`R5fp` and
  `R5fpCount` added; `QML3`, `R1fp` and `QMLeaves` already had it). The Lemma P docstrings now say
  the lattice cores are compiled "for N5's μ on Λ = 𝒪 only" and list the uncompiled steps.
  rv-qm-polar's repair 3 is applied to the `R1R2fp` docstring. Polar.lean (header, §8, the
  `lemmaP_lattice` docstring) no longer claims "every QM torus" as compiled.
- `lake build ZInQKernel`: exit 0, 9991 jobs. `scripts/print_axioms.lean`: 399/399 exactly
  `[propext, Classical.choice, Quot.sound]` (VERIFIED, 01:55-01:57 PST).

**Notes.** Smallest edits, one commit per note: hdec-adopt2, leaf-adopt, def-faltings, rv-jac-ext,
rv-qm-polar, leaf-qm-fp, leaf-push2, rv-blueprints, bp-analytic, leaf-modcurves, glue-t32a,
bp-qmmoduli, bp-hecke-fe, plus a pointer in hdec-adopt3. Where a count or line could be
re-checked I did so first (git at 9a826482 and 01267822, wc, diff); all matched the fact-check.

**Remains (outside this task's files).**
- scratch/hdec-adopt2/log.md:32 still says "93".
- The scratch originals of QMLeaves.lean, QMPolar.lean and R16Transfer.lean keep the old text;
  their kernel copies are fixed where they exist.
- The "Lemma QP" rename is recommended but not done.
- All Leaves.lean / h-decomposition.md items, including the weak `fibre_conjugates_isomorphic`
  copy at Leaves.lean:15532 and the duplicate `#print axioms` line.
