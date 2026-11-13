# tc-port results log

## Step 1 (VERIFIED)
- tcport.py ~/tc-oct16 (5a01f5fe3621) port1.txt: copied 397 files. Commit 9c0a5684.

## Step 2 (VERIFIED, read ~/tc-oct16/lakefile.toml)
- Tau Ceti leanOptions: weak.linter.mathlibStandardSet = true, weak.linter.style.longFile = 1500,
  weak.linter.style.longFileDefValue = 1500, weak.linter.style.header = true, warningAsError = true.
- No autoImplicit / maxHeartbeats / pp options set globally: Lean defaults (autoImplicit true,
  maxHeartbeats 200000) apply in both projects. All Tau Ceti global options are linters or
  warningAsError, which only make the build stricter; none is needed for elaboration.
  So no file-level set_option was added for Step 2.

## Mathlib gap
- Mathlib 56a00585..ccbef15e = 85 commits (git log in .lake/packages/mathlib; blobs not local).
  Notable: #41506 Set one-field structure, #42704 Is*Apply args implicit, #43966 KummerDedekind
  from a prime, #44884 IsRoot.map explicit RingHom, #44903 deprecations removed, #44823 renames.

## Step 3 (VERIFIED, compiled)
- `lake build` of FrobeniusPrimeCount, Different.Exponent, Different.Permutation: Build completed
  successfully (4729 jobs), with NO local change to any vendored file. 397 TauCeti oleans built.
  Cold build of the 397 modules (Mathlib oleans prebuilt): real 1m22.5s, user 14m56.8s, sys 3m20.2s.

## Step 4 (VERIFIED, compiled)
- kw-rest ∖ kw-new-nov01 = 714 modules, all exist at oct16; vendored. Their oct16 import closure
  (with port1) has 1118 modules: 7 extra oct16 modules outside both lists, vendored too
  (scratch/tc-port/extra-oct16.txt): Algebra.Group.Coprime, Algebra.Order.Hom.MonoidWithZero,
  FieldTheory.IsRealClosed.Real, GroupTheory.GroupAction.Stabilizer,
  NumberTheory.NumberField.FinitePlace, NumberTheory.NumberField.Global.Adeles.Away,
  RepresentationTheory.FDRep.
- First build of the 721: 5 failing modules (rest built or blocked downstream).
  Fixes (one line each):
  - Topology/Algebra/Group/Profinite/Generation.lean: `rfl` after `simp` in convergesToOne_iff
    (goal `s \ U = {x | x ∈ s ∧ x ∉ U}` left; Set-as-structure #41506 not at our pin).
  - RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean: explicit `G A` in
    the three IsZeroApply/IsAddApply/IsSMulApply instances (#42704 not at our pin).
  - `.isPGroup` -> `.isPGroup'` (Sylow field name at our pin, #44454 not at our pin) in
    GroupCohomology/PrimeIndex.lean (2), TateCohomology/TrivialityCriterion.lean,
    ClassFieldTheory/Formation/InvariantKernel.lean, Profinite/Sylow/Basic.lean,
    Profinite/Sylow/Existence.lean.
  - Profinite/Sylow/Containment.lean: imports new MathlibBackport/Sylow.lean, which proves
    `Sylow.maximal_isPGroup : Maximal (fun Q : Subgroup G ↦ IsPGroup p Q) (P : Subgroup G)`.
- Final: `lake build` of all 721 + backport: Build completed successfully (5256 jobs).
  1119 TauCeti oleans (1118 vendored + 1 backport). No `declaration uses sorry` warning.
