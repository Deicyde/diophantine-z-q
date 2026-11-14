# kw-basic: a Kronecker–Weber module upstream can take now

**Result.** `ZInQKernel/Contrib/KroneckerWeber/Basic.lean` states and proves the Kronecker–Weber
theorem (general form and the cyclic case) over Mathlib definitions only. It imports one module,
the vendored Tau Ceti `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber`.
It does not import `ZInQKernel/HDecomp/` or any other non-Tau-Ceti `ZInQKernel` module. It builds,
and its theorems use only `propext`, `Classical.choice` and `Quot.sound`.
`ZInQKernel/Contrib/KroneckerWeber/Leaves.lean` now imports `Basic` and derives its
`HDecomp`-typed theorems from it. Every name and type downstream code uses is unchanged.

## 1. Statements in `Basic.lean` (namespace `ZInQ.Contrib.KroneckerWeber`)

| declaration | kind | statement |
|---|---|---|
| `HSynKroneckerWeber` | `def : Prop` | `∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) → ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)` (leaf T17, verbatim `HSyn.KroneckerWeber`) |
| `GlueKroneckerWeber` | `def : Prop` | the same with `∃ n : ℕ, 0 < n ∧ …` (verbatim `KroneckerWeber` of `scratch/glue-assembly/Leaves.lean`) |
| `KroneckerWeberCyclic` | `def : Prop` | `∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], IsCyclic (L ≃ₐ[ℚ] L) → ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)` (the body of `TSkolemKW.KW.KroneckerWeberCyclic`, verbatim) |
| `isAbelianGalois_of_comm` | theorem | Galois with commuting automorphisms ⇒ `IsAbelianGalois ℚ L` |
| `exists_pos_algHom_cyclotomicField` | theorem | Tau Ceti's `kroneckerWeber` with a positive level, under the commuting hypothesis |
| `hSynKroneckerWeber` | theorem | `HSynKroneckerWeber` |
| `glueKroneckerWeber` | theorem | `GlueKroneckerWeber` |
| `kroneckerWeberCyclic_of_kroneckerWeber` | theorem | `HSynKroneckerWeber → KroneckerWeberCyclic` (the proof of `TSkolemKW.KW.kroneckerWeberCyclic_of_kroneckerWeber`, verbatim) |
| `kroneckerWeber_cyclic` | theorem | `KroneckerWeberCyclic` |

The first seven declarations (the defs `HSynKroneckerWeber` and `GlueKroneckerWeber` and the four
theorems `isAbelianGalois_of_comm` through `glueKroneckerWeber`) were moved verbatim from
`Leaves.lean`. They keep the same namespace, names, docstrings and proofs, so downstream
references still resolve. `KroneckerWeberCyclic`, `kroneckerWeberCyclic_of_kroneckerWeber` and
`kroneckerWeber_cyclic` are new: verbatim copies of the `HDecomp` definition and proof, restated
in this namespace. Here the cyclic theorem is called `kroneckerWeber_cyclic`, because
`kroneckerWeberCyclic` stays the name of the `HDecomp`-typed theorem in `Leaves.lean`.

## 2. `Leaves.lean` (imports `Basic` and `HDecomp.Textbook.KroneckerWeberUse`)

The agreement with the `HDecomp` definitions is shown in this file, not in `Basic`:

* `tSkolemKW_kroneckerWeber_iff : TSkolemKW.KW.KroneckerWeber ↔ HSynKroneckerWeber := Iff.rfl`
* `tSkolemKW_kroneckerWeberCyclic_iff : TSkolemKW.KW.KroneckerWeberCyclic ↔ KroneckerWeberCyclic := Iff.rfl`

The `HDecomp`-typed theorems keep their names and types:

* `tSkolemKW_kroneckerWeber : TSkolemKW.KW.KroneckerWeber` (from `hSynKroneckerWeber`);
* `kroneckerWeberCyclic : TSkolemKW.KW.KroneckerWeberCyclic` (from `kroneckerWeber_cyclic`).

The step-C8 section is unchanged: `dirichletCharacter_of_openKer`,
`dirichletCharacter_of_continuous`, `ker_ge_of_openKer` and `eq_of_agree_on_roots`.

## 3. Imports

* `Basic.lean`: `import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber`
  only.
* Its Tau Ceti import closure is listed in `scratch/kw-basic/tc-closure.txt`. It has **940 modules**,
  all under `ZInQKernel.Contrib.TauCeti`: the direct import plus its transitive closure, 32 of
  them `Backport/` helpers. No module outside Tau Ceti and Mathlib is in the closure. The task
  expected 5 modules. That count comes from following plain `import` lines only:
  `KroneckerWeber.lean` → `RaySubgroup` → `NormLimitation`, `ClassQuotient` → `Reciprocity`. The
  vendored Tau Ceti files are `module` files whose imports are `public import` lines, and following
  those gives 940. The list was computed by `scratch/kw-basic/tc_closure.py`.
* `Leaves.lean`: `Basic` and `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`. The direct import of
  the Tau Ceti module was dropped because it now comes through `Basic`.

## 4. Build result (Lean 4.35.0, Mathlib v4.35.0)

* `lake build ZInQKernel.Contrib.KroneckerWeber.Basic`: success. The 5261 jobs were mostly
  replays of Tau Ceti oleans; compiling `Basic` itself took 36 s.
* `lake build ZInQKernel.Contrib.KroneckerWeber.Leaves`: success (9990 jobs).
* Importers of the changed files: no module under `ZInQKernel/` imports
  `Contrib/KroneckerWeber/*`. The only importer is `scratch/h-decomposition/Leaves.lean`, which
  uses `kroneckerWeberCyclic`, `hSynKroneckerWeber` and `HSynKroneckerWeber`. After building its
  imports (10474 jobs, success), `lake env lean scratch/h-decomposition/Leaves.lean` finished with
  0 errors and no `sorry` in 9 min 28 s. Its `#hdec_same` checks of
  `HDec.TSkolemKW.KW.KroneckerWeberCyclic` and `HDec.HSyn.KroneckerWeber` still report "verbatim".
* `scratch/kw-basic/Check.lean` is a copy of `Basic.lean` with `#print axioms` lines added. Run with
  `lake env lean scratch/kw-basic/Check.lean`, every one of the six theorems depends on
  `[propext, Classical.choice, Quot.sound]` (`scratch/kw-basic/check-output.txt`).

## 5. Not done / possible follow-up

The step-C8 glue (`TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic`, `cycChar`, …) is
still stated over `PkgI4.Qbar`/`PkgI4.GQ` in `HDecomp`. Those are `abbrev`s for
`AlgebraicClosure ℚ` and its Galois group, so a Mathlib-only copy (a `Contrib/KroneckerWeber/Dirichlet.lean`
importing only `Basic`) would be a mechanical follow-up if upstream wants the corollary too. This
task did not do it.
