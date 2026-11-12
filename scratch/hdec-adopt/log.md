# hdec-adopt results log

## Generation (scripts in scratch/hdec-adopt/)
- `adopt.py` generates `ZInQKernel/HDecomp/**` from the scratch drafts (strips `#print`/`#check`,
  maps `import GlueDescent.X` to `ZInQKernel.HDecomp.Descent.X`, adds the module docstring) and
  then runs `wrap.py` (lines > 100 characters wrapped; `by` blocks broken after `by`).
- Verbatim copies replaced by imports:
  - C10/Trace.lean: the pkg-I3 §1-2 copy and `CharPolyIndepOfEll` dropped; imports
    `HDecomp.Objects` (§A of obj-bridge = pkg-I3 verbatim). Only `trace_indep_of_ell`,
    `trace_eq_trace_of_ell` remain.
  - Conductor/D1Local.lean: the verbatim copy of glue-conductor's Breaks.lean (Local.lean lines
    1-402) dropped; imports `HDecomp.Conductor.Breaks`.
  - Conductor/ArtinUpper.lean (= glue-I6-rest/Conductor.lean): the copied pkg-I6 Part II
    definitions dropped; imports `HDecomp.Conductor.I6Base` (which contains pkg-I6 verbatim).
  - Assembly.lean (= glue-assembly/GlueAssembly.lean = F2+Ext+Transfer+F4Copy+Assembly): F4Copy's
    verbatim copy of `ZInQKernel/Hypotheses/JHeight.lean` dropped; imports `ZInQKernel.Hypotheses.
    JHeight` with `open ZInQ.JHeight`; kept `SixContactMinAt`, `sixContactMinAt_of_jHeightBound`.
  - A6/A6.lean: §1-§9 (pkg-I2 copy, identical to Objects §B lines 735-1135 up to the namespace
    name: VERIFIED by diff) dropped; imports `HDecomp.Objects` with `open PkgI2`.
- Not adopted (superseded): glue-a6-alg/Quat.lean (its content is A6.lean's `GlueA6Alg.Alg`),
  glue-assembly/{C8,E1Lin,E2Index,F3Glue,Leaves}.lean (outside GlueAssembly.lean).
- Remaining verbatim copy: `PkgI6.exists_sq_eq_one_add` in I6Base (copy of GlueConductor's in
  Dyadic.lean, different namespace; harmless).

## Builds
- build1 (`lake build ZInQKernel.HDecomp`, before wrapping): every module built except
  Conductor/ArtinUpper (dangling docstring from the cut; fixed in adopt.py).
- build2 (`lake build ZInQKernel`, first wrap): 2 failures from wrapping (Constants: break after
  `;` inside a same-line `by`; A1Quaternion: continuation inside a same-line `by` at a column
  left of the tactic). wrap.py now breaks after `by` and indents continuations deeper (calc +8).
- build3: Constants (calc first step) failed; fixed.
- build4 (`lake build ZInQKernel`, 00:48 PST): EXIT 0, no errors. VERIFIED.
- `PkgI6.exists_sq_eq_one_add` (I6Base) is now proved by `GlueConductor.exists_sq_eq_one_add`
  (import of Conductor.Dyadic) instead of a verbatim copy; statement unchanged. VERIFIED (build4).

## Axioms
- `lake env lean scripts/print_axioms.lean` (00:49 PST): EXIT 0, 179 `#print axioms`, every one
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` (output scratch/hdec-adopt/axioms.txt).
  88 of them are the HDecomp theorems (list scratch/hdec-adopt/axioms_list.txt plus
  `GlueAssembly.jHeightBound_of_glueOutputs`, `GlueAssembly.sixContactMinAt_of_jHeightBound`).
  VERIFIED.
- No line over 100 characters in ZInQKernel/HDecomp/ (python check). No `sorry` / `axiom`
  (grep; the only hits are in comments). VERIFIED.
