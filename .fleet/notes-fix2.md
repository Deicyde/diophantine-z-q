# notes-fix2 (fork issue #2, items 1, 3, 4, 6, 7): done

**Result.** All five items fixed; items 2, 5, 8 (in `scratch/h-decomposition/Leaves.lean`) left
alone as instructed.

- (1) `scratch/leaf-qm-fp/QMLeaves.lean`: `LeafQM.AV.fibre_conjugates_isomorphic` now has the
  kernel's strengthened statement (the conclusion includes `Y₃`, `π`, a `ℚ̄`-point `y` with
  `π(y) = j₀` and `Φ y = [P]`) and the kernel's proof, which compiles unchanged in the scratch file.
- (3) Same file: the `QML3` docstring uses the kernel wording (fixed `μ`, characteristic 0,
  lattice cores only, unique only after fixing `μ`).
- (4) `scratch/rv-qm-polar/QMPolar.lean`: header, §8 title and `lemmaP_lattice` docstring mirror
  `ZInQKernel/HDecomp/QM/Polar.lean`, so they claim only the lattice statement for N5's `μ` on
  `Λ = 𝒪` and list the steps that are not compiled.
- (6) `scratch/rv-blueprints/R16Transfer.lean`: header rewritten for its three declarations
  (`AbVar`, the commutativity instance, `exists_quotient_transfer`).
- (7) `scratch/hdec-adopt2/log.md`: 93 → 90 new axiom entries (182 before), explained:
  `axioms_section.lean` has 93 lines = 3 header lines + 90 `#print axioms`.

**What compiles** (`lake env lean`, one process at a time, outputs in `scratch/notes-fix2/`):
QMLeaves.lean (exit 0, 28/28 axiom checks standard), QMPolar.lean (exit 0, 10/10 standard, only
the linter warnings it already had), R16Transfer.lean (exit 0, standard). No error and no `sorry`.

**What remains.** Nothing in scope. Items 2, 5 and 8 of issue #2 are for the tasks porting
`scratch/h-decomposition/Leaves.lean`. Report: `docs/research/notes-fix2.md`.
