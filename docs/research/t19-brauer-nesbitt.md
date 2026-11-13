# T19: Brauer–Nesbitt in characteristic zero (trace form)

## Proposed result and scope

`ZInQ.Contrib.BrauerNesbitt.t19` in `ZInQKernel/Contrib/BrauerNesbitt/Matrix.lean` proves the
exact closed body of the proposed H target `ZInQ.Targets.H.T19`. The statement reference is
the frozen packet of draft PR 41 at head `2757349fbd8ca613340b679bbd149f78c2baba6b`, scope
`REFERENCE_ONLY_NOT_REGISTERED_NOT_PROOF`:

| Reference file | SHA-256 (matches the packet's `REFERENCE.json`) |
|---|---|
| `ZInQKernel/Targets/H/T19.lean` | `e35ffa3140f8386d15ed0ba019553e0466df99b534db7cfe3a8a5b2ed797fb71` |
| `ZInQKernel/Targets/H/Defs/HSyn.lean` | `180072ef6d408586f281c7f25ff7f78fbcafd45383f61c9d5269ba696d252402` |
| `docs/h-targets/TASKS.md` | `3577f178c69d6a025d08fbc41d15cf3213d07259a5972784954c76c7483f566f` |

PR 41 is unregistered and its targets are not mathematically accepted. **No `Targets/H` file
is imported by any repository module, and `KERNEL_CONTRACT.json` is unchanged.** `t19`
restates the target body verbatim; a provider can later be the one-line
`theorem T19_holds : ZInQ.Targets.H.T19 := ZInQ.Contrib.BrauerNesbitt.t19`
once the target is registered after statement review. This change does not declare
`ZInQ.Contrib.H.T19_holds` or the module `ZInQKernel.Contrib.H.T19`.

The proved statement: for every `G : Type` with `[Group G]`, every `E : Type` with
`[Field E] [CharZero E]`, every `n : ℕ`, and all `ρ₁ ρ₂ : G →* GL (Fin n) E` such that, for each
`ρᵢ`, every subspace `W` of `Fin n → E` with `W.map (Matrix.toLin' (ρᵢ g)) ≤ W` for all `g` has
an invariant complement `W'` (`IsCompl W W'`), if `Matrix.trace (ρ₁ g) = Matrix.trace (ρ₂ g)`
for all `g`, then one `P : GL (Fin n) E` satisfies `ρ₂ g = P * ρ₁ g * P⁻¹` for every `g`.

There is no additional hypothesis: `G` is not assumed finite, finitely generated or
topological; `E` is not assumed algebraically closed, perfect or of any size beyond
characteristic `0`; `n = 0` is included and is not a special case; the conjugating element is
uniform in `g`. `t19` has no universe parameters.

The same proof also gives:

- `nonempty_linearEquiv_of_character_eq`: the module form (Lang's Cor. XVII.3.8, locator
  UNVERIFIED) for an **arbitrary** algebra `A` over a field `k` of characteristic `0`.
- `brauerNesbittChar0`: the verbatim closed body of the baseline leaf
  `PkgI6.BrauerNesbittChar0` (`ZInQKernel/HDecomp/Conductor/I6Base.lean`), for an arbitrary
  group.
- `pkgI6_brauerNesbittChar0 : PkgI6.BrauerNesbittChar0` and
  `glueC10_brauerNesbittChar0 : GlueC10.BrauerNesbittChar0`, closing the two existing baseline
  definitions by unfolding.
- `t19_of_brauerNesbittChar0` and `brauerNesbittChar0_of_t19`: the two encodings imply each
  other. The second is the GLUE-03 bridge of the reference `TASKS.md` §5 (T19 ⇒ the form that C10
  consumes). It uses only its hypothesis, not the project proof of either statement.

This is a proof-only, non-release proposal on main `a5937595cde3e3db00975b81e5171cdef92c801a`,
branch `work/issue37-phase2-t19`, with the changes left uncommitted. It does not register a
target, add a provider, change the headline, edit any C10/H consumer, modify a manuscript,
promote a record, or publish acceptance. Manuscript/TeX/PDF release duties do not apply to
this scoped helper contribution; a later assembled-proof or record release keeps its own
obligations.

## Files and declarations

All declarations are in namespace `ZInQ.Contrib.BrauerNesbitt`.

| File | Imports | Main declarations |
|---|---|---|
| `Basic.lean` | five narrow Mathlib modules | `character`, `character_congr`, `character_prod`, `character_eq_add_of_isCompl`, `finiteDimensional_submodule`, `isSemisimpleModule_prod`, `exists_smul_eq_projection`, `exists_linearEquiv_submodule_of_character_eq`, `nonempty_linearEquiv_of_character_eq` |
| `Representation.lean` | `Basic`, `Mathlib.RepresentationTheory.Basic` | `character_asModule`, `character_asModule_eq`, `nonempty_asModule_linearEquiv_of_trace_eq`, `brauerNesbittChar0` |
| `Matrix.lean` | `Representation` and three narrow Mathlib modules | `matrixRep`, `trace_matrixRep`, `isSemisimpleModule_matrixRep`, `exists_conj_of_linearEquiv`, `t19_of_brauerNesbittChar0`, `t19` |
| `Glue.lean` | `Matrix` and two narrow Mathlib modules | `asModuleEquivOfIntertwining`, `coordHom`, `toMatrixRep`, `trace_toMatrixRep`, `invariant_compl_of_isSemisimpleModule`, `brauerNesbittChar0_of_t19` |
| `Bridge.lean` | `Representation`, `ZInQKernel.HDecomp.Conductor.I6Base`, `ZInQKernel.HDecomp.C10.C10` | `pkgI6_brauerNesbittChar0`, `glueC10_brauerNesbittChar0` |

Only `Bridge.lean` loads the whole of Mathlib, through the two existing baseline modules
(both begin with `import Mathlib`). The proof modules use narrow imports. No `sorry`, `admit`,
`axiom`, `opaque`, `partial`, `unsafe`, `extern`, `implemented_by`, `native_decide`, `macro`,
`elab` or `set_option` occurs in the five files, and no definition of the target is changed.

## Statement fidelity

- `t19`'s binder list and body were copied from the frozen `T19.lean`; `brauerNesbittChar0`'s
  from `PkgI6.BrauerNesbittChar0`. The two baseline `def BrauerNesbittChar0` blocks
  (`I6Base.lean` and `C10.lean`) are byte-identical; only their docstrings differ.
- In a session-local scratch directory **outside the repository**, the frozen `HSyn.lean` and
  `T19.lean` were compiled into scratch object files (with the packet as module root), and a
  scratch file importing them with the owned modules elaborated
  `theorem scratch_T19_holds : ZInQ.Targets.H.T19 := ZInQ.Contrib.BrauerNesbitt.t19`.
  A separate process (`replay_owned.lean`, below) checked
  `Kernel.isDefEq (type of t19) (.const ZInQ.Targets.H.T19 [])`: **true**.
- A structural comparator (`DiffFrozen.lean`) walked the stored body of each reference
  definition against the elaborated type of the owned theorem, instantiating binders and
  identifying only subterms that are proofs. Results: `ZInQ.Targets.H.T19` vs `t19`,
  `PkgI6.BrauerNesbittChar0` vs `brauerNesbittChar0`, `GlueC10.BrauerNesbittChar0` vs
  `brauerNesbittChar0`: **identical up to proof subterms**. Plain `Expr` equality is false only
  because Lean abstracts Prop-valued instance proofs in a `def` into auxiliary `_proof_i`
  theorems (for example `RingHomSurjective.ids` and `smulCommClass_self` appear inline in the
  theorem). Negative controls: a scratch variant of T19 with an extra `[Finite G]` reports
  `DIFFER at Finite …`, and T19 vs `brauerNesbittChar0` reports `DIFFER at Group …`.
- A scratch `example` applying `t19` with `n = 0` and `E = ℚ` elaborates; the invariant
  complement hypothesis is then discharged by `⊤` because `Fin 0 → ℚ` is a subsingleton.

## Provenance, reuse and licensing

This is an original project proof of the classical argument. Attribution, not a
dependency: Lang, *Algebra*, rev. 3rd ed., XVII §3 (Thm. 3.7 and Cor. 3.8), and Curtis–Reiner
§30 as cited by the target docstring. Both locators are recalled, **UNVERIFIED**; the Lean proof
does not rely on either text.

Only the pinned Mathlib (`v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`,
Apache-2.0) is imported. No third-party source was copied or ported, so no new license text is
added. The pinned Mathlib contains no Brauer–Nesbitt formalization (a source search for
`nesbitt` finds nothing). Its character orthogonality (`Representation.char_orthonormal` in
`Mathlib/RepresentationTheory/Character.lean`) is not used: it assumes `[Fintype G]`,
`[Invertible (Nat.card G : k)]` and `[IsAlgClosed k]`. Tau Ceti was not used.

The T13 proof at public commit `4b619619fc4548a799f0476ab3c0cc9d4c1ec9eb` was read
(`ZInQKernel/Contrib/SkolemNoether/ModuleClassification.lean`). Nothing was reused: it
classifies modules over a **simple** algebra by dimension, while here the image of the group
algebra is only semisimple and multiplicities must be separated by isotypic idempotents. No
T13 file or PR is touched, and no Astra-accepted status of T13 is assumed.

AI contribution: Metamate wrote the proof, the scratch comparison tools and this note, and ran
the checks. Serving-model identity is unknown. No reviewer identity or acceptance is asserted.

## Author's dependency inventory and connecting derivation

This is the author's inventory, not a non-author source-first reconstruction or a coverage
decision. Every supplier is a kernel-checked Mathlib declaration at the pinned commit; the
exact form used is the one stated.

1. **Characters** (`Basic.lean`). For an `A`-module `V` with a compatible `k`-structure
   (`IsScalarTower k A V`), `character k V a = trace_k (a • ·)`. Invariance under an `A`-linear
   equivalence `e` comes from `LinearMap.trace_conj'` applied to `e.restrictScalars k`;
   additivity on `V × W` from `LinearMap.trace_prodMap'`; additivity on `IsCompl p q` from the
   `A`-linear `Submodule.prodEquivOfIsCompl`. An `A`-submodule is finite-dimensional over `k`
   through the injective `k`-linear inclusion (`Module.Finite.of_injective`).
2. **Separating element** (`exists_smul_eq_projection`). `M` is a semisimple `A`-module,
   finite-dimensional over `k`, and `S ≤ M` is simple. Let `c = isotypicComponent A M S` and
   `C = sSup (isotypicComponents A M \ {c})`. `sSupIndep_isotypicComponents` gives
   `Disjoint c C`; `sSup_isotypicComponents` (semisimple `M`) gives `c ⊔ C = ⊤`. Both are fully
   invariant (`IsFullyInvariant.isotypicComponent`; `fullyInvariantSubmodule` is closed under
   `sSup`). Hence the projection `p` onto `c` along `C` commutes with every `f : End_A M`
   (decompose `m = x + y`). So `p` is an `End_A M`-linear endomorphism of `M`. `M` is finite over
   `End_A M` because `k` acts through it (`Module.Finite.of_restrictScalars_finite`).
   Mathlib's Jacobson density theorem `Module.Finite.toModuleEnd_moduleEnd_surjective` then
   gives `a : A` with `a • m = p m` for all `m`. So `a` fixes `c` and maps `M` into `c`.
3. **Key step** (`exists_linearEquiv_submodule_of_character_eq`). Let `V`, `W` be semisimple and
   finite-dimensional with equal characters, and `S ≤ V` simple. Suppose no `T ≤ W` has
   `S ≃ₗ[A] T`. Then `isotypicComponent A W S = ⊥` (an empty `sSup`). In `V × W`, which is
   semisimple (`isSemisimpleModule_prod`), take `S' = S.map inl ≅ S` and `a` from step 2.
   `LinearMap.le_comap_isotypicComponent` for `snd` and `LinearEquiv.isotypicComponent_eq` put
   `snd (a • (0, w))` into `isotypicComponent A W S = ⊥`, so `a` kills `W`. `inl` maps `S` into
   the isotypic component, so `a` fixes `S`. Applying `a` twice gives `a • a • v = a • v`. The
   action of `a` on `V` is therefore a **nonzero idempotent**: a nonzero vector of the
   nontrivial simple `S` is fixed. `LinearMap.IsIdempotentElem.trace_eq_zero_iff`
   (characteristic `0`) makes its trace nonzero, while the trace on `W` is `trace 0 = 0`. This
   contradicts `character k V a = character k W a`.
4. **Induction** (`nonempty_linearEquiv_of_character_eq`), by strong induction on
   `finrank k V`. If `V` is trivial, `character (1)` gives `(finrank k W : k) = 0`, so `W` is
   trivial (`Nat.cast_eq_zero`, `Module.finrank_zero_iff`). Otherwise
   `IsSemisimpleModule.exists_simple_submodule` gives `S`, and step 3 gives `T ≅ S` in `W`.
   Complements `S'` and `T'` exist by semisimplicity. Additivity and invariance give equal
   characters on `S'` and `T'`. `finrank k S' < finrank k V` because `S` is nontrivial. The
   induction hypothesis gives `S' ≅ T'`, and `V ≅ S × S' ≅ T × T' ≅ W`.
5. **Representation form** (`Representation.lean`). With `A = MonoidAlgebra k G`,
   `character k ρ.asModule a = trace (ρ.asAlgebraHom a)` (conjugation by `ρ.asModuleEquiv`).
   Equality on group elements extends to all of `A` by `MonoidAlgebra.induction_linear`, using
   `asAlgebraHom_single : asAlgebraHom ρ (single g c) = c • ρ g` and linearity of the trace.
   Mathlib supplies `IsScalarTower k k[G] ρ.asModule` and finiteness of `ρ.asModule`.
6. **Matrix form** (`Matrix.lean`). `matrixRep ρ g = Matrix.toLin' (ρ g)` is a
   `Representation E G (Fin n → E)`. The T19 hypothesis turns every `Subrepresentation` into an
   invariant subspace with an invariant complement. The complement is built as a
   subrepresentation, and `IsCompl` transfers through the definitional
   `toSubmodule (σ ⊓ τ) = …`, `⊥` and `⊤`. This proves `ComplementedLattice`, which is
   `IsSemisimpleModule` by
   `Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`.
   `Matrix.trace_toLin'_eq` converts the traces. An `E[G]`-linear equivalence `e` gives an
   `E`-linear `f` with `f ∘ ρ₁' g = ρ₂' g ∘ f` (from `e.map_smul (single g 1)` and
   `Representation.single_smul`). Then `P = ⟨toMatrix' f, toMatrix' f⁻¹, _, _⟩`, and
   `ρ₂ g = P * ρ₁ g * P⁻¹` follows by `Units.ext` and injectivity of `Matrix.toLin'`.
   `t19` is `t19_of_brauerNesbittChar0 brauerNesbittChar0`.
7. **GLUE-03** (`Glue.lean`, hypothesis = the T19 body). `trace (ρ 1) = finrank`, so equal
   traces at `1` give `finrank k V = finrank k W` in characteristic `0`. Choose
   `Module.finBasisOfFinrankEq` bases `eV`, `eW`. `toMatrixRep e ρ` is
   `Units.map (coordHom e) ∘ ρ.asGroupHom`, with `toLin' (toMatrixRep e ρ g) = e.conj (ρ g)`.
   Semisimplicity moves to `matrixRep (toMatrixRep e ρ)` along the intertwining equivalence
   `e.symm`, made `k[G]`-linear by `Representation.IntertwiningMap.equivLinearMapAsModule`.
   `invariant_compl_of_isSemisimpleModule` turns it into the T19 hypothesis. T19 gives `P`;
   `σM g * P = P * ρM g`; and `eV ≫ toLin' P ≫ eW⁻¹` is an intertwining equivalence `V ≃ W`.
8. **Bridge** (`Bridge.lean`). `PkgI6.BrauerNesbittChar0` and `GlueC10.BrauerNesbittChar0` are
   closed by `brauerNesbittChar0` through definitional unfolding.

The dependency closure was computed in scratch: `brauerNesbittChar0_of_t19` uses no constant
from steps 1–6 except the matrix glue `matrixRep`, `matrixRep_apply` and its own helpers. In
particular it does not use `t19`, `brauerNesbittChar0`, `character` or step 4.

### Nine application obligations

The substantive transitions are steps 2–4 (module form), 5 (module → representation),
6 (representation → T19) and 7 (T19 → representation).

- **Source hypotheses.** Jacobson density needs a semisimple `M` finite over `End_A M`: `M` is
  semisimple by assumption or `isSemisimpleModule_prod`, and finiteness is derived from
  `FiniteDimensional k M`. `sSup_isotypicComponents` needs semisimplicity, which is supplied.
  The idempotent-trace lemma needs a commutative `CharZero` ring and free finite range and
  kernel: the field `k`, with `k`-subspaces of a finite-dimensional space. Lean's elaborator
  checked every instance argument.
- **Constructed objects.** The acting ring is exactly `MonoidAlgebra E G` (step 5) acting on
  `(matrixRep ρᵢ).asModule`, whose carrier is `Fin n → E`. The projection, separating element,
  complements, matrix `P` and its inverse are all constructed, not assumed.
- **Domain/index coverage.** The trace hypothesis covers all `g : G`, and its linear extension
  covers all of `MonoidAlgebra E G` (step 5). `P` is one element working for every `g`. The
  semisimplicity hypothesis is used for every subrepresentation.
- **Transition/comparison maps.** `Matrix.toLin'` in both directions; `asModuleEquiv` (the
  identity on carriers); `e.restrictScalars E`; `toMatrix'`/`toLin'` inverse pair;
  `LinearEquiv.conj` and `coordHom` (step 7). The conjugation direction is exactly
  `ρ₂ g = P * ρ₁ g * P⁻¹`, with `P = toMatrix' f` for `f : ρ₁-space → ρ₂-space`.
- **Identity of consumed object.** The equivalence produced by step 4 is between the two given
  modules; step 6 consumes it for `matrixRep ρ₁` and `matrixRep ρ₂` of the *given* `ρ₁`, `ρ₂`.
  The final statement concerns the original `GL (Fin n) E`-valued homomorphisms.
- **Coefficient/normalization conventions.** One field throughout (`k = E`). Traces are
  `Matrix.trace` and `LinearMap.trace`, identified by `Matrix.trace_toLin'_eq`. There is no
  determinant, scalar, sign or proportionality normalization.
- **Local conditions.** No topology, continuity, completion or localization occurs. The
  target has none: `G` carries no topology here.
- **Exceptional cases.** `n = 0` and zero modules are the trivial base case of step 4 and a
  checked `example`. The core proof uses characteristic `0` exactly twice: the nonzero trace of
  a nonzero idempotent, and `dim = 0` from `trace 1 = 0`. The GLUE-03 bridge uses it once more,
  to equate dimensions from the traces at `1`. It cannot be dropped: over `𝔽_p` (`p ≥ 3`), with
  `G = 𝔽_p^×`, the semisimple scalar representations `g ↦ I_p` and `g ↦ g · I_p` have all traces
  `0` but are not conjugate; in the module form, the trivial representations of dimensions `p`
  and `0` have equal characters. Semisimplicity is needed too: over any field,
  `t ↦ [[1, t], [0, 1]]` of `ℤ` and the trivial 2-dimensional representation have equal traces
  but are not conjugate. No finiteness of `G` is used. Algebraic closure is not used: Schur's
  lemma is never applied over `k`, and Jacobson density works relative to `End_A M`, so an
  endomorphism division algebra larger than `k` is allowed.
- **Downstream consumption.** No consumer is edited. `glueC10_brauerNesbittChar0` has exactly
  the hypothesis type `hBN : BrauerNesbittChar0` of `GlueC10.iso_of_trace_eq_frob_finite`,
  `iso_of_trace_eq_on_frob`, `iso_three_of_five` and `c10`; a scratch file elaborated each of
  them applied to it. They still need their other inputs (`ChebotarevExists` for
  `iso_of_trace_eq_frob_finite` and `c10`, `FrobDense S` for the other two, plus their trace and
  semisimplicity hypotheses). Any integration needs its own consumer check.

## Verification evidence

Compiler: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Root `lake-manifest.json` SHA-256
`f7ce830d517bfbcb4cdcc90bef299da854c9b28653b9accc2b13df2822233779`; `lean-toolchain`
`ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; `KERNEL_CONTRACT.json`
unchanged at `2c66ac6bc539829173269b7ff0474a0b7def9beca335711d3d3ceeb7b6ba9ba9`. No setup,
update, cache or pin operation was run. Contribution object files were written only to a
session-local scratch directory outside the repository; shared packages, the baseline build
cache and the reference packet were only read.

Each module was compiled directly with `lake env lean --threads=2` (`LEAN_NUM_THREADS=2`,
at most two compiler processes, through the session resource gate). The build was
contribution-cold over warm pinned dependencies: Basic 4.05 s, Representation 3.06 s,
Matrix 3.12 s, Glue 3.42 s, Bridge 4.68 s. Maximum RSS was 2,548,700 KiB for the four narrow
modules and 6,937,268 KiB for Bridge (full Mathlib). There were no errors or warnings. This is
not a cold Mathlib or full-repository build.

- `#print axioms` for `t19`, `brauerNesbittChar0`, `nonempty_linearEquiv_of_character_eq`,
  `exists_linearEquiv_submodule_of_character_eq`, `exists_smul_eq_projection`,
  `nonempty_asModule_linearEquiv_of_trace_eq`, `t19_of_brauerNesbittChar0`,
  `brauerNesbittChar0_of_t19`, `pkgI6_brauerNesbittChar0` and `glueC10_brauerNesbittChar0`
  returned only `propext`, `Classical.choice`, `Quot.sound`.
- The **unchanged** `scripts/audit_kernel.lean` (SHA-256
  `673af3d23f5433cb17145e9de8cac97b40a7d513281b7c2a726fb19ca089facc`) ran on a scoped spec. It
  listed exactly the five modules, the seven main theorem names as exports, `targets: []`, and
  `t19` as both `headline.declaration` and `headline.type_declaration`. Report:
  `status: passed`, 52 declarations, 52 raw occurrences, 0 duplicate bodies,
  `runtime_declarations_not_replayed: []`,
  `allowed_axioms_used: [Quot.sound, Classical.choice, propext]`,
  `protocol_acceptance: false`. Time 16.07 s, RSS 16,175,056 KiB. The headline
  self-comparison is not a statement lock; fidelity is checked separately above.
- Scratch `replay_owned.lean` replayed the same 52 declarations on their external imports. It
  found no unsafe or partial declarations and the same three axioms. It checked the
  `Kernel.isDefEq` provider shape against the frozen `T19` (true) and that `t19` has no
  universe parameters.
- `python3 -B scripts/check_target.py`: `FrozenTarget matches
  lean/Frozen/BoundedIntegerPolynomial.lean`.
- `scripts/check_kernel_contract.py` requirements were read: contribution files are ordinary
  `.lean` files under `ZInQKernel/Contrib/`, need no contract entry, and contain no
  `skipKernelTC`.
- `git status`: the only changes are the untracked directory
  `ZInQKernel/Contrib/BrauerNesbitt/` and this note. No tracked file changed.

Proof-source SHA-256 (UTF-8, LF, no CR):

| File | SHA-256 |
|---|---|
| `ZInQKernel/Contrib/BrauerNesbitt/Basic.lean` | `9db9e0e5c6b8a72ef12ea3d0f6d9be77ccee27f7a6f50d99e60394f65dcf446c` |
| `ZInQKernel/Contrib/BrauerNesbitt/Representation.lean` | `7f3a1c8d6ed1058b2ca324c1406f9b5e84575e00dffccf3f05ca39f334566f56` |
| `ZInQKernel/Contrib/BrauerNesbitt/Matrix.lean` | `9c5ef7ee925b691e8d542efcaa8adfee7b6effbdf4f5e2f26410d12673f0c6ae` |
| `ZInQKernel/Contrib/BrauerNesbitt/Glue.lean` | `898791049ac61daaf7971da3200321c5658ff9fd0f135c0da0c3abcf62cce6ac` |
| `ZInQKernel/Contrib/BrauerNesbitt/Bridge.lean` | `521cda388cea1066699365219644fb8c998e56e125c0b479facbf062132341a0` |

Baseline files read as suppliers: `ZInQKernel/HDecomp/Conductor/I6Base.lean`
(`3a2688e5271203cb1d28663fefe3c017426a43dd4c5f4a710f0dabe6de96ce2d`) and
`ZInQKernel/HDecomp/C10/C10.lean`
(`cbada4686b5961de63b7d10c1b042e4a61dba6dd40a997d5fa3d0eb4e5d530fa`).

### Reproduction without shared-cache writes

From the repository root, with the pinned Mathlib cache present and `$OUT` a fresh scratch
directory outside the repository:

```sh
mkdir -p "$OUT/lib/lean/ZInQKernel/Contrib/BrauerNesbitt"
# Lean resolves all ZInQKernel.* modules under one root: expose the baseline HDecomp objects.
ln -s "$PWD/.lake/build/lib/lean/ZInQKernel/HDecomp" "$OUT/lib/lean/ZInQKernel/HDecomp"
export LEAN_NUM_THREADS=2
for m in Basic Representation Matrix Glue Bridge; do
  lake env sh -c "LEAN_PATH=$OUT/lib/lean:\$LEAN_PATH lean --threads=2 -R . \
    -o $OUT/lib/lean/ZInQKernel/Contrib/BrauerNesbitt/$m.olean \
    ZInQKernel/Contrib/BrauerNesbitt/$m.lean" || exit 1
done
lake env sh -c "LEAN_PATH=$OUT/lib/lean:\$LEAN_PATH \
  lean --run scripts/audit_kernel.lean SPEC.json REPORT.json"
python3 -B scripts/check_target.py
```

`SPEC.json` is the scoped spec described above. For the statement comparison, compile the
frozen packet's `Defs/HSyn.lean` and `T19.lean` with `-R <packet root>` into the same
`$OUT/lib/lean` tree. Then elaborate a scratch file that imports `ZInQKernel.Targets.H.T19` and
the owned modules and states `theorem scratch_T19_holds : ZInQ.Targets.H.T19 :=
ZInQ.Contrib.BrauerNesbitt.t19`. Never place these imports in a repository module. The
scratch tools have SHA-256: `CheckFrozen.lean`
`39ed9d7f42d630cbe478452acccdc4d2ed92c6c70b717047320aaf0d0aea4e9c`, `DiffFrozen.lean` (with the
negative controls) `be837af819f9a29952ec3779c65246c26048de458da2a131763b5c5ba12df7c8`, `replay_owned.lean`
`f9a50fdd996c9e97fef9dea08b2db80bc771fb099814852338a0acec4c06262d`, `ConsumerCheck.lean`
`1668255f2ac445c0026e1ecceca8d5b4bce7760d6f35feaf30c1576184985f1f`; the scoped `SPEC.json` is
`ca2f9d45e7df64f69e6a07272d833eb7b1efbbf75c4ea3d48ef52bd0a51432c6`. They are not part of the
proposed change.

## Review status and open items

This is an author proof packet. Compilation, axiom checks and the scoped replay are not
protected Astra protocol acceptance. They do not establish source-first coverage, statement
review of the unregistered target, or the full-head kernel run, which the parent performs. No
commit, push, PR, registration, provider, reviewer receipt or human contact is produced here.

Open, outside this change: registration of T19 after maintainer statement review (the
reference packet marks its definitions unreviewed), the provider wrapper, the full root/CI
audit, independent non-author review with a designated coverage decision, and any C10/R15
consumer integration (the C10 glue still assumes `ChebotarevExists` or `FrobDense S`).
