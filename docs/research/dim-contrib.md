# dim-contrib: dimension theory adopted as `ZInQKernel/Contrib/Dim/`

Task dim-contrib, 2026-11-13. Base 80b032c9 (wip/integrate-w43), with origin/wip/curve-infra
(0eb4618a) merged. Scratch: `scratch/dim-contrib/` (results log `log.md`). The only files added under
`ZInQKernel/` are the ten new modules in `ZInQKernel/Contrib/Dim/`. No pinned file, no file under
`blueprint/`, and no other task's notes or scratch files were changed. This is model work; no human
has reviewed it.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means a published
fact with a reference. **UNVERIFIED** marks a theorem number or tag recalled from memory (there is
no network here).

## 0. Result

- **Two developments are adopted as ten Mathlib-style modules under `ZInQKernel/Contrib/Dim/`.**
  - curve-infra's dimension theory: `dim R = trdeg_K Frac R` for domains of finite type over a
    field, and `dim X = trdeg_K K(X)` for integral schemes locally of finite type over a field.
    The `ffAlgebra` forms are included.
  - infra-smooth-dim's dimension theory of smooth schemes over a field: local rings at closed
    points are regular of dimension `n`, `dim X = n`, and integral surjective morphisms preserve
    dimension.
- **Builds.** Every module builds with `lake build` (VERIFIED). Nine of them use Mathlib alone.
  `LeafPush2.lean` also imports the kernel's `ZInQKernel.HDecomp.LeafPush2.R18`, for
  `ffAlgebra`.
- **Axioms.** All 21 main theorems depend only on `[propext, Classical.choice, Quot.sound]`
  (VERIFIED, `scratch/dim-contrib/run_CheckDim.txt`).
- **Settings.** There is no `sorry`, no `set_option maxHeartbeats` and no other `set_option`.
- **Statement check (§1).** It found no conclusion weaker than its docstring claims and no
  vacuous statement. It found four hypotheses stronger than needed. Three are removed in the
  adopted modules:
  1. an unused hypothesis in infra-smooth-dim's chart lemma;
  2. `trdeg = 1` in place of `trdeg ≤ 1` in `AlgDepOfTrdegOne`;
  3. "irreducible" in place of "nonempty" in `dim X = n`.

  Two other generalizations were made: `IsFinite` is weakened to `IsIntegralHom` (§1.2, row 6),
  and a universe restriction is removed.
- **Named Props.** curve-infra's eight named Props (`DimEqTrdeg`, …,
  `CurveAlgOverTranscendental`) are carried over. A script compared their texts with
  curve-infra's: they are identical except that `fnFieldAlgebra` is renamed
  `functionFieldAlgebra` (VERIFIED, `props_compare.txt`).

## 1. Statement check

Each adopted theorem statement was read against its docstring and its mathematical source.
**curve-infra**: `scratch/curve-infra/Dim.lean`, `tail_part.lean.part`. **infra-smooth-dim**:
`SmoothStalk.lean` §0–§4 (as copied into `CurveInfraAll.lean` lines 3–526), `FiniteDim.lean`.
Sources: Hartshorne I.1.7, I.1.8A, II Ex. 3.20, II.8; Stacks, *Commutative Algebra*, "Dimension
of finite type algebras over fields"; numbering UNVERIFIED.

### 1.1 Faithful statements (no change needed)

| Statement (origin) | Reading |
| --- | --- |
| `dim_eq_trdeg` / `DimEqTrdeg` (curve-infra) | Faithful. `X` is integral and only *locally* of finite type over `K`, which is more general than Hartshorne II Ex. 3.20 (finite type). The conclusion `dim X = (trdeg_K K(X)).toENat` is exactly the claim. The algebra structure is `K ≅ Γ(Spec K) → Γ(X) → K(X)`, the natural one. |
| `dim_affineOpen_eq_trdeg` | Faithful. `[Nonempty U]` is needed, since `dim ∅ = ⊥`. |
| `exists_dim_eq_trdeg`, `DimEqTrdegAlg` | Faithful (Hartshorne I.1.8A). The named Prop lives in universe 0 only; the theorem is general (see §1.2). |
| `SmoothTrdeg`, `CurveFnFieldAlgDep` (curve-infra) | Faithful. Integrality is needed for `K(X)`. "Smooth of relative dimension `n`" is Mathlib's `SmoothOfRelativeDimension n`. |
| `DimEqTrdegOver`, `SmoothTrdegOver`, `CurveAlgOverTranscendental` | Faithful. Kernel `ffAlgebra` is definitionally `fnFieldAlgebra` (VERIFIED: the proofs are the Mathlib-only theorems, applied with no conversion). `CurveAlgOverTranscendental` claims "algebraic over `K[x]`", which is exactly the conclusion. It is weaker than "finite over `K(x)`", but no stronger claim is made. |
| `stalk_dim_of_smoothOfRelativeDimension` (infra-smooth-dim) | Faithful. Closed points only, which is necessary: non-closed points have smaller stalk dimension. |
| `exists_stalk_dim_of_smooth`, `isRegularLocalRing_stalk_of_smooth`, `finrank_cotangentSpace_…`, `stalk_dims_of_section`, `isClosed_of_section` | Faithful to their docstrings ("at closed points", "at a `K`-point"). |
| `topologicalKrullDim_eq_of_smooth` | Faithful. Irreducibility is used, because it compares stalks at *different* closed points. |
| `ringKrullDim_and_spanFinrank_localization` | Faithful. `ι σ : Type` matches Mathlib's `IsStandardSmooth`, which quantifies over `Type`. |
| `height_isMaximal_mvPolynomial` | Faithful, but `ι : Type` (universe 0 only). This suffices for the presentation theorem. |
| `spanFinrank_add_card_le` | Faithful. |
| `topologicalKrullDim_le_of_isIntegralHom` | Faithful. |

### 1.2 Hypotheses stronger than needed (all six fixed or generalized)

| # | Statement (origin) | Finding | Status in `Contrib/Dim` |
| --- | --- | --- | --- |
| 1 | `stalk_dim_of_chart` (infra-smooth-dim) | **Unused hypothesis** `hU : IsAffineOpen U`. The unused-variable linter flagged it (VERIFIED, compile). The statement stays true, but the hypothesis is stronger than needed. | Removed in `ringKrullDim_stalk_of_chart`. |
| 2 | `algDepOfTrdegOne` / `AlgDepOfTrdegOne` (curve-infra) | The hypothesis `trdeg_K F = 1` is stronger than needed: `trdeg ≤ 1` suffices, by the same proof. | New `exists_aeval_eq_zero_of_trdeg_le_one`. The named Prop is kept verbatim and proved from it. |
| 3 | `topologicalKrullDim_eq_of_smoothOfRelativeDimension` (infra-smooth-dim) | `[IrreducibleSpace X]` is stronger than needed; `[Nonempty X]` suffices. Every point specializes to a closed point (`X` is Jacobson), and every closed point has stalk dimension `n`. | Restated with `[Nonempty X]`, with a new proof (VERIFIED, compiles). |
| 4 | `topologicalKrullDim_eq_of_finite_surjective` (infra-smooth-dim) | `[IsFinite f]` is stronger than needed; `[IsIntegralHom f]` suffices. | New `topologicalKrullDim_eq_of_isIntegralHom_of_surjective`. The finite form is kept as a corollary. |
| 5 | `exists_dim_eq_trdeg` (curve-infra) | `K` and `R` must lie in one universe. This is not needed. | Universe-polymorphic `exists_ringKrullDim_eq_and_trdeg_eq`, via `lift_trdeg_add_eq`. |
| 6 | `trdeg_eq_of_isLocalization` (curve-infra) | The name and docstring say "localization (e.g. the fraction field)", but the hypothesis is `IsFractionRing`. So the statement is narrower than the name, not wrong. | Renamed `trdeg_eq_of_isFractionRing`. |

**No conclusion is weaker than claimed. No hypothesis is vacuous or a disguised form of the
conclusion.** All statements are over Mathlib's own definitions: `topologicalKrullDim`,
`ringKrullDim`, `Algebra.trdeg`, `Scheme.functionField`, `SmoothOfRelativeDimension`,
`IsRegularLocalRing`, `Submodule.spanFinrank`. One exception: the `…Over` forms use the
kernel's `ffAlgebra`, which is itself an explicit ring map.

## 2. Modules (all in namespace `ZInQ.Contrib.Dim`)

Build command: `lake build ZInQKernel.Contrib.Dim.<M>`. All ten succeed (VERIFIED, 09:47–09:59).
The only warning is the generic note "imports `Mathlib` … designed for use with the module
system", which every file importing Mathlib in this project gets. Lines are ≤ 100 characters, and
every declaration has a docstring.

| Module | Imports | Content (main declarations) | Origin |
| --- | --- | --- | --- |
| `Basic.lean` | Mathlib | `topologicalKrullDim_eq_iSup_of_isOpenEmbedding`, `topologicalKrullDim_le_of_specializingMap` (with `exists_ltSeries_lift_of_specializingMap`, `closureIrreducibleCloseds`), `topologicalKrullDim_scheme_eq_iSup_cover`, `topologicalKrullDim_eq_of_iso`, `topologicalKrullDim_spec` | g0-dim, g0-reverseisog (via infra-smooth-dim `FiniteDim.lean`) |
| `IntegralHom.lean` | Basic | `ringKrullDim_le_of_isIntegral`, `ringKrullDim_eq_of_isIntegral_of_injective`, `topologicalKrullDim_le_of_isIntegralHom`, **`topologicalKrullDim_eq_of_isIntegralHom_of_surjective`**, `topologicalKrullDim_eq_of_finite_surjective` | infra-smooth-dim `FiniteDim.lean`, g0-dim |
| `MvPolynomial.lean` | Mathlib | `height_eq_natCard_of_isMaximal_mvPolynomial` (maximal ideals of `k[x_ι]` have height `|ι|`), `ringKrullDim_mvPolynomial_fin` | infra-smooth-dim `MaxHeight.lean`, g0-dim |
| `Cotangent.lean` | Mathlib | `spanFinrank_maximalIdeal_add_card_le` (killing elements with independent cotangent classes lowers the embedding dimension), `derivation_mem_of_mem_sq` | infra-smooth-dim `CotQuot.lean`, `StdSmoothLocal.lean` §1 |
| `SubmersivePresentation.lean` | MvPolynomial, Cotangent | `relationCotangent`, `linearIndependent_relationCotangent`, **`ringKrullDim_and_spanFinrank_localization`** (`S_𝔪` has dim = edim = `P.dimension`) | infra-smooth-dim `StdSmoothLocal.lean` §2–§3 |
| `SmoothStalk.lean` | SubmersivePresentation | **`ringKrullDim_stalk_of_smoothOfRelativeDimension`**, `exists_ringKrullDim_stalk_of_smooth`, `exists_nhds_ringKrullDim_stalk`, `ringKrullDim_stalk_eq_of_isClosed`, **`topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`**, `isRegularLocalRing_stalk_of_smooth`, `finrank_cotangentSpace_of_smoothOfRelativeDimension`, `isClosed_singleton_of_section`, `ringKrullDim_stalk_of_section`, **`topologicalKrullDim_eq_of_smoothOfRelativeDimension`** (now `[Nonempty X]`) | infra-smooth-dim `SmoothStalk.lean` §4 |
| `Trdeg.lean` | IntegralHom, MvPolynomial | `exists_ringKrullDim_eq_and_trdeg_eq`, `trdeg_eq_of_isFractionRing`, `ringKrullDim_eq_trdeg`, **`ringKrullDim_eq_trdeg_fractionRing`**, `exists_aeval_eq_zero_of_trdeg_le_one`; named `DimEqTrdegAlg`/`dimEqTrdegAlg`, `AlgDepOfTrdegOne`/`algDepOfTrdegOne` | curve-infra `Dim.lean` §1, §3 |
| `FunctionField.lean` | Trdeg | `functionFieldAlgebra`, `sectionsAlgebra`, instance `nonempty_top_opens`, `topologicalKrullDim_affineOpen_eq_trdeg_functionField`, **`topologicalKrullDim_eq_trdeg_functionField`**; named `DimEqTrdeg`/`dimEqTrdeg` | curve-infra `Dim.lean` §2, §3 |
| `SmoothTrdeg.lean` | FunctionField, SmoothStalk | **`trdeg_functionField_eq_of_smoothOfRelativeDimension`**, `exists_aeval_eq_zero_of_smoothOfRelativeDimension_one`, `isAlgebraic_adjoin_of_transcendental_of_trdeg_eq_one`; named `SmoothTrdeg`/`smoothTrdeg`, `CurveFnFieldAlgDep`/`curveFnFieldAlgDep` | curve-infra `tail_part` |
| `LeafPush2.lean` | SmoothTrdeg, `ZInQKernel.HDecomp.LeafPush2.R18` | named `DimEqTrdegOver`/`dimEqTrdegOver`, `SmoothTrdegOver`/`smoothTrdegOver`, `CurveAlgOverTranscendental`/`curveAlgOverTranscendental` (over the kernel's `ZInQ.LeafPush2.ffAlgebra`) | curve-infra `tail_part` |

### 2.1 Names: old to new

| Old (scratch) | New (`ZInQ.Contrib.Dim.`) |
| --- | --- |
| `InfraSmoothDim.height_isMaximal_mvPolynomial` | `height_eq_natCard_of_isMaximal_mvPolynomial` |
| `…spanFinrank_add_card_le` | `spanFinrank_maximalIdeal_add_card_le` |
| `…relCot`, `…linearIndependent_relCot` | `relationCotangent`, `linearIndependent_relationCotangent` |
| `…stalk_dim_of_chart` | `ringKrullDim_stalk_of_chart` (without `hU`) |
| `…stalk_dim_of_smoothOfRelativeDimension` | `ringKrullDim_stalk_of_smoothOfRelativeDimension` |
| `…exists_stalk_dim_of_smooth`, `…exists_nbhd_stalk_dim` | `exists_ringKrullDim_stalk_of_smooth`, `exists_nhds_ringKrullDim_stalk` |
| `…stalk_dim_eq_of_closed` | `ringKrullDim_stalk_eq_of_isClosed` |
| `…topologicalKrullDim_eq_of_smooth` | `topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth` |
| `…isClosed_of_section`, `…stalk_dims_of_section` | `isClosed_singleton_of_section`, `ringKrullDim_stalk_of_section` |
| `…topologicalKrullDim_eq_of_finite_surjective` | same name (corollary of `…_of_isIntegralHom_of_surjective`) |
| `…closureIC`, `…lift_series`, `…topologicalKrullDim_le_of_specializing` | `closureIrreducibleCloseds`, `exists_ltSeries_lift_of_specializingMap`, `topologicalKrullDim_le_of_specializingMap` |
| `…topologicalKrullDim_eq_iSup_of_openEmbedding`, `…scheme_dim_eq_iSup_cover`, `…scheme_dim_eq_of_iso`, `…spec_dim` | `topologicalKrullDim_eq_iSup_of_isOpenEmbedding`, `topologicalKrullDim_scheme_eq_iSup_cover`, `topologicalKrullDim_eq_of_iso`, `topologicalKrullDim_spec` |
| `CurveInfra.ringKrullDim_mvPolynomial_field` | `ringKrullDim_mvPolynomial_fin` |
| `CurveInfra.exists_dim_eq_trdeg` | `exists_ringKrullDim_eq_and_trdeg_eq` (universe-polymorphic) |
| `CurveInfra.trdeg_eq_of_isLocalization` | `trdeg_eq_of_isFractionRing` |
| `CurveInfra.fnFieldAlgebra`, `secAlgebra`, `nonempty_top` | `functionFieldAlgebra`, `sectionsAlgebra`, `nonempty_top_opens` |
| `CurveInfra.dim_affineOpen_eq_trdeg`, `dim_eq_trdeg` | `topologicalKrullDim_affineOpen_eq_trdeg_functionField`, `topologicalKrullDim_eq_trdeg_functionField` |
| `CurveInfra.<named Prop>`, `CurveInfra.<proof>` | `ZInQ.Contrib.Dim.<same names>` |

### 2.2 Proofs

The proofs are those of the scratch files, with renamed references. They were cut by
`scratch/dim-contrib/gen.py` from `scratch/curve-infra/CurveInfraAll.lean` lines 3–526, which are
infra-smooth-dim's `SmoothStalk.lean` verbatim; long lines and docstrings were then edited by hand.
Three proofs are new or changed:

- **`topologicalKrullDim_eq_of_smoothOfRelativeDimension`** is a new proof under `[Nonempty X]`.
  It takes the supremum of coheights over all points and bounds each by the coheight at a closed
  specialization.
- **`exists_ringKrullDim_eq_and_trdeg_eq`** uses `lift_trdeg_add_eq` in place of `trdeg_add_eq`.
- **`exists_aeval_eq_zero_of_trdeg_le_one`** and
  **`isAlgebraic_adjoin_of_transcendental_of_trdeg_eq_one`** use the `lift` forms of the Mathlib
  lemmas, so that `F` can lie in any universe.

`ringKrullDim_eq_of_isIntegral_of_injective` now gets its `≤` direction from
`ringKrullDim_le_of_isIntegral`.

### 2.3 Check files

- **`scratch/dim-contrib/CheckDim.lean`** imports `Contrib.Dim.IntegralHom` and
  `Contrib.Dim.LeafPush2` and prints the axioms of 21 main theorems.
  - Run with `lake env lean`: all 21 are `[propext, Classical.choice, Quot.sound]` (VERIFIED,
    `run_CheckDim.txt`).
- **`scratch/dim-contrib/Check.lean`** is `scratch/contrib-check/Check.lean` plus two imports and
  the same 21 `#print axioms` lines, for the integrator to merge. Its compile result is in §4.

## 3. Not adopted, and what can follow

- **Closures of kernel Props.** infra-smooth-dim also closes kernel Props: `HodgeLatticeClosed.lean`
  (`ZInQ.DefFaltings.HodgeLattice.regularAtOrigin`, `dimAtOrigin`, `dimBaseChange`,
  `tangentDimAtOrigin`, `hodgeLatticeTheorem`), `SmoothDimProps.lean` and `CurveFactsClosed.lean`.
  - These are applications, not the dimension theory, and the task did not ask for them.
  - Each can now be a short module importing `ZInQKernel.Contrib.Dim.SmoothStalk` in place of its
    copied §0–§4.
- **The aggregate build.** The new modules are not imported by `ZInQKernel.lean`, so a bare
  `lake build ZInQKernel` does not build them. They are built by name, like the other Contrib
  modules.
