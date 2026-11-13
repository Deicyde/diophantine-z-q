# kw-new — fleet report

**Main result.** Tau Ceti's Kronecker–Weber theorem now builds inside the fork (Lean 4.35.0,
Mathlib 56a00585), and the Kronecker–Weber leaves are proved from it. All axioms are
[propext, Classical.choice, Quot.sound] (VERIFIED with `#print axioms`, recorded in
`scratch/kw-new/axioms-output.txt`).

- `TauCeti.ClassFieldTheory.kroneckerWeber (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E] : ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)`
  (module `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber`;
  `lake build` of it completes, 5260 jobs).
- In `ZInQKernel/Contrib/KroneckerWeber/Leaves.lean`, namespace `ZInQ.Contrib.KroneckerWeber`:
  - `hSynKroneckerWeber : HSynKroneckerWeber`. This is leaf T17, a verbatim restatement of
    `HSyn.KroneckerWeber` (`scratch/h-decomposition/Leaves.lean`).
  - `glueKroneckerWeber : GlueKroneckerWeber`, a verbatim restatement of
    `scratch/glue-assembly/Leaves.lean` `KroneckerWeber`.
  - `tSkolemKW_kroneckerWeber : TSkolemKW.KW.KroneckerWeber` and
    `kroneckerWeberCyclic : TSkolemKW.KW.KroneckerWeberCyclic`. These defs are imported from
    `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`.
  - Step C8, proved outright with no hypothesis: `dirichletCharacter_of_openKer` (a `ψ : G_ℚ →* Eˣ`
    with open kernel equals `χ ∘ cyc_m` for a Dirichlet character `χ` mod `m`),
    `dirichletCharacter_of_continuous`, `ker_ge_of_openKer` and `eq_of_agree_on_roots`.

**What compiles.** All 44 nov01 modules of `kw-new-nov01.txt` build. They are backported through
37 files under `ZInQKernel/Contrib/TauCeti/Backport/`:
- additive helpers holding the declarations added to oct16 modules after 5a01f5fe;
- whole-module nov01 replacement copies of `Global.PrescribedInvariant`, `Global.Kummer.Norm` and
  `Global.Kummer.AuxiliaryPlaces`, whose oct16 versions are imported in the closure only by nov01
  modules;
- one Mathlib lemma (`Polynomial.X_pow_sub_X_ne_zero`).

tc-port's files are untouched. The Tau Ceti module `Global.Kummer.Index` (nov01) is in the
closure because it discharges the Kummer hypothesis of the oct16 second inequality. Five nov01
modules are moved files that clash with their oct16 predecessors if both are imported (listed in
`docs/research/kw-new.md`). The other 39 load together with the bridge.

**What remains.** Nothing in this task's scope. Local Kronecker–Weber (`PkgI6.LocalKroneckerWeber`,
leaf T16a) was not in scope.

**Notes.** Duplicate relaunched sessions (kw-new-9f, kw-new-e3) appeared in this worktree. kw-new-9f
merged origin/main and rewrote `Leaves.lean` to use the importable Textbook defs; I compiled and
kept that version, and both duplicates stood down. Details: `docs/research/kw-new.md`,
`scratch/kw-new/log.md`.
