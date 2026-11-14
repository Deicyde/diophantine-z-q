# kw-basic

**Result.** `ZInQKernel/Contrib/KroneckerWeber/Basic.lean` is a module upstream can take now. It
imports only the vendored Tau Ceti module `...ClassFieldTheory.ClassFields.KroneckerWeber` and no
`HDecomp` module. It states and proves over Mathlib definitions only:

* the general Kronecker–Weber theorem: `hSynKroneckerWeber : HSynKroneckerWeber` (leaf T17,
  verbatim) and `glueKroneckerWeber`;
* the cyclic case: `kroneckerWeber_cyclic : KroneckerWeberCyclic` (verbatim body of
  `TSkolemKW.KW.KroneckerWeberCyclic`) and `kroneckerWeberCyclic_of_kroneckerWeber`.

`Leaves.lean` imports `Basic`. It identifies the two `HDecomp` Props with the Mathlib ones by
`Iff.rfl` and keeps every existing name and type (`tSkolemKW_kroneckerWeber`,
`kroneckerWeberCyclic`, the C8 theorems).

**What compiles.**
* `lake build` of `Basic` and `Leaves` succeeds.
* The only importer, `scratch/h-decomposition/Leaves.lean`, compiles with 0 errors and no sorry
  (9.5 min), and its `#hdec_same` KW checks still say "verbatim".
* `scratch/kw-basic/Check.lean`: all six theorems use only propext, Classical.choice and
  Quot.sound.

**Note.** The Tau Ceti import closure is 940 modules (`scratch/kw-basic/tc-closure.txt`), not the
5 the task expected. Five is what you get by following plain `import` lines; the vendored files
use `public import`.

**Remains (optional).** A Mathlib-only copy of the C8 Dirichlet-character glue (over
`AlgebraicClosure ℚ`) was not written.
