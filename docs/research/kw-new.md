# kw-new: the Kronecker–Weber theorem in the fork, and the Kronecker–Weber leaves

## Main result

Tau Ceti's Kronecker–Weber theorem now compiles inside this project (Lean 4.35.0, Mathlib
56a00585), and the Kronecker–Weber leaves are proved from it. Every theorem below has the
standard axioms only. VERIFIED: compiled, and `#print axioms` run through
`scratch/kw-new/Axioms.lean`, output in `scratch/kw-new/axioms-output.txt`.

The headline theorem is `TauCeti.ClassFieldTheory.kroneckerWeber`, in module
`ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber`:

```lean
theorem kroneckerWeber (E : Type) [Field E] [NumberField E] [IsAbelianGalois ℚ E] :
    ∃ n : ℕ, n ≠ 0 ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)
-- depends on axioms: [propext, Classical.choice, Quot.sound]
```

The bridge is `ZInQKernel/Contrib/KroneckerWeber/Leaves.lean` (namespace
`ZInQ.Contrib.KroneckerWeber`). It imports `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`, which
fork main now contains (it is the t-skolem-kw file). Its declarations:

| theorem | exact type | axioms |
|---|---|---|
| `hSynKroneckerWeber` | `HSynKroneckerWeber` | propext, Classical.choice, Quot.sound |
| `glueKroneckerWeber` | `GlueKroneckerWeber` | same |
| `tSkolemKW_kroneckerWeber` | `TSkolemKW.KW.KroneckerWeber` | same |
| `kroneckerWeberCyclic` | `TSkolemKW.KW.KroneckerWeberCyclic` | same |
| `dirichletCharacter_of_openKer` | `∀ {E : Type*} [Field E] (ψ : GQ →* Eˣ), IsOpen (ψ.ker : Set GQ) → ∃ (m : ℕ+) (χ : DirichletCharacter E (m : ℕ)), ∀ σ : GQ, (ψ σ : E) = χ ((TSkolemKW.KW.cycChar m σ : (ZMod m)ˣ) : ZMod m)` | same |
| `dirichletCharacter_of_continuous` | the same conclusion, for `[TopologicalSpace Eˣ] [T1Space Eˣ]`, `ψ` continuous with `(Set.range ψ).Finite` | same |
| `ker_ge_of_openKer` | `∀ {G} [CommGroup G] (ψ : GQ →* G), IsOpen (ψ.ker : Set GQ) → ∃ m : ℕ+, ∀ σ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = ζ) → ψ σ = 1` | same |
| `eq_of_agree_on_roots` | `∀ {G} [CommGroup G] (ψ : GQ →* G), IsOpen (ψ.ker : Set GQ) → ∃ m : ℕ+, ∀ σ τ : GQ, (∀ ζ : Qbar, ζ ^ (m : ℕ) = 1 → σ ζ = τ ζ) → ψ σ = ψ τ` | same |

Here `GQ` and `Qbar` are `PkgI4.GQ` and `PkgI4.Qbar`. Two of the statements exist only in scratch
files, so they are restated verbatim as `def`s, each with its source in the docstring (both
checked against fork main c303557d):

* `HSynKroneckerWeber` is leaf T17, `HSyn.KroneckerWeber` in `scratch/h-decomposition/Leaves.lean`,
  line 21206:
  `∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) → ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)`.
  Its text is identical to that of `TSkolemKW.KW.KroneckerWeber`.
* `GlueKroneckerWeber` is `GlueAssembly.KroneckerWeber` in `scratch/glue-assembly/Leaves.lean`,
  line 19:
  `∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K], (∀ a b : K ≃ₐ[ℚ] K, a * b = b * a) → ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)`.

So leaf T17 (Kronecker–Weber) is proved. It is also proved in the importable
`TSkolemKW.KW.KroneckerWeber` form, and its cyclic case `TSkolemKW.KW.KroneckerWeberCyclic` is
proved too. Step C8's consequence (a finite-order character of `G_ℚ` with values in a field is a
Dirichlet character) is now proved outright as `dirichletCharacter_of_openKer` and
`dirichletCharacter_of_continuous`.

## How Kronecker–Weber was brought to Lean 4.35

* **What was vendored.** Task tc-port vendored the oct16 Tau Ceti modules (5a01f5fe). This task
  vendored the 44 modules of `kw-new-nov01.txt` from nov01 (97a5b235) with `tcport.py`. Only 11 of
  those 44 are in the import closure of the Kronecker–Weber module once it is built on oct16 files.
  Building revealed a twelfth: `Global.Kummer.Index`. VERIFIED
  (`scratch/kw-new/tools/closure_local.py`).
* **Backport helpers.** The nov01 modules use declarations that were added to oct16 modules after
  5a01f5fe. Those declarations are copied into
  `ZInQKernel/Contrib/TauCeti/Backport/<oct16 module path>.lean`. Each helper `public import`s the
  oct16 module and adds only the missing declarations, copied verbatim from nov01. There are 37
  files under `Backport/`, counting the 3 replacement copies below and the one Mathlib backport;
  tc-port's files were not edited.
* **Replacement copies.** Three modules were reworked after oct16:
  * `Global.PrescribedInvariant` was generalized from layers `V ◁ G_K` to all normal layers;
  * `Global.Kummer.Norm` and `Global.Kummer.AuxiliaryPlaces` got changed or strengthened statements.

  In the Kronecker–Weber closure these three are imported only by nov01 modules. So each one's
  whole nov01 text is vendored under `Backport/` as a replacement, with the same declaration names.
  A replacement must never be imported together with the oct16 version.
* **The second inequality.** At oct16 the global second inequality is conditional on the Kummer
  index bound. At nov01 the new module `Global.Kummer.Index` proves that bound, which is how it
  enters the closure.
* **Lean and Mathlib differences found (VERIFIED):**
  * A helper must be `public import`ed when its declarations appear in theorem statements.
    Otherwise dot notation silently resolves to a parent structure's declaration.
  * A `rfl` about an oct16 definition fails in another module, because the definition's body is
    not exposed there. Fixed with `import all` or with an oct16 `_def` lemma.
  * One Mathlib lemma, `Polynomial.X_pow_sub_X_ne_zero`, was backported with a new proof.
  * Three proofs were adapted: a `simpa` in PrescribedInvariant, explicit continuity in place of a
    `fun_prop` that timed out in `Topology.Algebra.Star.Completion`, and an explicit
    `ratModulus_infinitePart` rewrite.
* **Status of the 44 nov01 modules: all build.** Five of them are moved files that redefine the
  declarations of their oct16 predecessors, so each must not be imported together with that
  predecessor:
  * `GroupAction.Stabilizer.Basic`, with `GroupAction.Stabilizer`;
  * `Cyclic.PowMonoidHom`, whose `IsCyclic.mem_range_powMonoidHom_iff` has a different statement
    from the one in `Cyclic.Basic`;
  * `UnitFiltration.Pow.Basic`, with `UnitFiltration.Pow`;
  * `FinitePlace.Basic`, with `FinitePlace`;
  * `FDRep.Basic`, with `FDRep`.

  The other 39 modules, together with the bridge, load in one environment
  (`scratch/kw-new/AllNov01.lean`, compiled). `GroupAction.Norm` now takes its five `groupNorm*`
  declarations, whose statements are identical, from oct16 `GroupCohomology.Cocycle`.

## What remains

The Kronecker–Weber leaves of this task are all proved. Local Kronecker–Weber
(`PkgI6.LocalKroneckerWeber`, leaf T16a) is not addressed here.
