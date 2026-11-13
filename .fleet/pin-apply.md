# pin-apply (2026-11-13)

**Verdict.** qm-pin's repair is integrated. Two clauses are added to `R1fpProps`:
- `R1famProps`: `Φ` is induced by a family over `Y`.
- `R1univProps`: families over proper smooth curves are classified by a morphism to `Y`.

Both places compile with no `sorry` and only `propext`, `Classical.choice`, `Quot.sound`
(VERIFIED):
- **The kernel** (`ZInQKernel/HDecomp/QM/Leaves.lean`, plus the new module `QM/Pin.lean`, imported
  from `HDecomp.lean`). `lake build ZInQKernel` succeeds. `scripts/print_axioms.lean` has 542
  lines, 16 of them new for `Pin`, all standard.
- **`scratch/h-decomposition/Leaves.lean`.** 0 errors, no `sorryAx`, and 190 axiom lines, all
  standard. They include the unchanged `HSyn.sixContactMin_of_leaves` and the new
  `HSyn.sixContactMin_of_leaves_pin`.

**The comparison.** Given the named glue Prop `MobiusGlue`, `FibreSimple`, `ThetaPointOfFibre` and
`ModularConstituent` are each equivalent to their statement for any one triple satisfying the
clauses (`G0Split.*_iff_at`, `qmPieces_iff_w`).
- `HSyn.GluePiecesPin` is `GluePieces` with these three pieces in `∃`-form, plus `MobiusGlue`.
- It is interconvertible with `GluePieces` + `MobiusGlue` (`gluePieces_of_pin`,
  `gluePiecesPin_of`).
- `GluePieces` itself is unchanged.

**The attack** (`scratch/pin-apply/AttackCheck.lean`, compiled).
- rv-g0pieces' proof of `r1fp_relabel` fails verbatim.
- Every surviving relabeling has the form `y ↦ y ≫ g` for a morphism `g` (`relabel_is_morphism`,
  now in the kernel; it needs no `MobiusGlue`).
- rv-g0pieces' `relabelOver s φ` survives only if `s` is the point map of a morphism, so a
  non-continuous `s` is excluded (`not_r1fp_exotic`).
- Caveat: a swap of two closed points is continuous on a curve. Excluding it needs the argument
  "a morphism fixing all but two closed points is the identity", which is not compiled.

**Docs.** `docs/research/h-decomposition.md` is updated:
- the R1 paragraph: the pin clauses, with source R1(a) under Lemma P;
- a §0 bullet and the §2.3 Lean check;
- glue rows 4, 9, 10, plus a new row 12 for `MobiusGlue`.

The report is `docs/research/pin-apply.md`.

**What remains.**
- Integrating mobius-glue's proof of `MobiusGlue` from named facts.
- A human check that `R1univProps` is faithful (polarization extension; locator numbers UNVERIFIED).
- Restating FS5, `FibreQMPeriod` and `KernelFieldExists` for the pinned triple.
- `docs/research/g0-split.md` line 99 (another task's file) is not edited.
