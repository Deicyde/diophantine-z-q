# javanpeykar-rebase: `javanpeykarBound` over height-fix's printed stable height

Task javanpeykar-rebase, 2026-11-16. Base: `wip/javanpeykar-fix` 3d1ce928. Merged in, in this order:
`origin/main` e41a7169, `origin/wip/integrate-w82` 5e235a40 (it was not on main), and `wip/height-fix` 49e6d97d.
There were no conflicts. Scratch is in `scratch/javanpeykar-rebase/` (results log `log.md`). The Lean is in
`ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean` (namespace `JavanpeykarRebase`). Nothing else under
`ZInQKernel/` was edited.

Marks: **VERIFIED** (compiled, or read in a file of the repository), **STANDARD** (published, with a reference),
**UNVERIFIED** (a theorem number recalled from memory; there is no network here).

## 1. Result

The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound` is proved from two restated leaves, one
textbook field and one glue Prop. Everything uses only the standard axioms (VERIFIED, §3).

```lean
theorem JavanpeykarRebase.javanpeykarBound_of_printed_rebase_final (hJ : JavanpeykarPrintedMap)
    (hS : ConstantFieldExtensionUnramifiedFinite) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hD : ZInQ.HeightFix.SemiAbelianDescendsPerfect) : ZInQ.HeightSplit.JavanpeykarBound
```

The four hypotheses:

* **`JavanpeykarPrintedMap`.** javanpeykar-fix's `JavanpeykarFix.JavanpeykarPrintedMap`, verbatim, with
  height-dict's `ZInQ.HeightDict.IsPrintedStableHeight` replaced by height-fix's
  `ZInQ.HeightFix.IsPrintedStableHeight`. The height-fix version is the one whose metric is sound and whose step
  R3 is a definition with proved lemmas.
* **`ConstantFieldExtensionUnramifiedFinite`.** Stichtenoth 3.6.3(a) narrowed to **finite** `K'/K` (fix (2) of
  the review, §2.2).
* **`mumfordTorsionAlgClosed`.** An existing textbook field, kind published, LEAF. `uniformizationLeafAll` was
  also a hypothesis before; it has since been proved upstream (`uniformizationLeafAll_proof`, folded at TailZ44),
  and the `_final` theorem fills it with that proof.
* **`SemiAbelianDescendsPerfect`.** height-fix's glue. It is the only unproved step between the print and the
  kernel (§2.3), and height-fix's `bostLowerBound` and `gaudronRemondThm14` discharges use it too.

**What the two review fixes required:**
1. *The spec must give PrintedMap kind consequence until a reading says LEAF.* Done. The leaf is kind
   `consequence`, flagged "pending reading: …".
2. *Narrow Stichtenoth to finite `K'/K` if every consumer needs only finite extensions.* The grep shows that the
   only consumer, `JavanpeykarFix.isBelyiFunction_baseChange_full` via `belyiBaseChange_of_full`, applies the
   leaf at `K' = AlgebraicClosure K`, an infinite extension (VERIFIED). So the consumer needs more than the
   finite case. The leaf is narrowed anyway, and the algebraic case is **proved in Lean from the finite case**
   (`full_of_finite`). `finite_of_full` proves the converse, so the narrowed leaf loses nothing.

**Target −1 GLUE against the re-rated base: not met by this fold alone.** It is met once height-fix's fold is in
and a reading clears `JavanpeykarPrintedMap`. All counts below are autofold dry runs against this base's
`kinds.tsv`, where `javanpeykarBound` is rated consequence / GLUE. The format is strict LEAF/GLUE count on the
number of rows. All VERIFIED.

| fold | count | effect of `javanpeykarBound` on GLUE |
| --- | --- | --- |
| `autofold.json`: this fold alone (PrintedMap consequence, Stichtenoth published, `semiAbelianDescendsPerfect` as a new glue row) | 16/21 on 37 → 17/22 on 39 (needs `--allow-rise`) | +1 |
| height-fix's spec alone (reference) | 16/21 → 18/20 on 38 | n/a |
| `autofold-with-height-fix.json`: height-fix's two discharges plus this one, with the shared glue added once | 16/21 → 19/20 on 39 | **0** (and LEAF +1) |
| the same, if a reading rates PrintedMap published (not a deliverable spec) | 16/21 → 20/19 on 39 | **−1** |

Why the fold does not go lower:
* `JavanpeykarPrintedMap` counts GLUE (kind consequence) until a statement check against Javanpeykar's print
  rates it LEAF.
* `SemiAbelianDescendsPerfect` is new glue in the consumer direction. Kernel height ⇒ printed height needs
  semistability over `k(𝔭)`, but the kernel only gives it over `κ̄(𝔭)`. This is the same step height-fix
  needs, so after height-fix's fold it costs nothing extra.

There are two ways to reach −1:
* a statement check reads Javanpeykar Thm 1.1.1 and rates the leaf LEAF;
* `SemiAbelianDescendsPerfect` is proved. A `semiab-descend` worktree exists on this host, presumably for that.

## 2. The steps between the print and the kernel

| step | content | status |
| --- | --- | --- |
| (1) | the kernel Jacobian `J` is the `Pic⁰` representative `V` (`abVarIso_picZero_of_isJacobian`) | proved (javanpeykar-dict) |
| (2) | `dim J = genus(X_K̄)` (`dim_eq_genusK`, `genusBar_eq`) | proved (javanpeykar-dict) |
| (3) | a `K`-rational Belyi function stays Belyi over `K̄` with the same degree (`belyiBaseChange_of_full`) | proved from the leaf `ConstantFieldExtensionUnramifiedFinite` through `full_of_finite` (new, §2.2); the full constant field is proved (`fullConstantField_of_bijective`, javanpeykar-fix) |
| (b) | Belyi function ⇒ finite Belyi map `X_K̄ → ℙ¹` of the same degree (`belyiMapOfFunction_proof`) | proved (javanpeykar-fix) |
| (c) | `X_K̄` projective (`exists_closedImmersion_projectiveSpace`) | proved (javanpeykar-fix) |
| (d) | `V_K̄ ≅ Jac(X_K̄)` (`exists_jacBar`) | proved (javanpeykar-fix) |
| (a) | kernel `IsStableFaltingsHeight` ⇒ height-fix `IsPrintedStableHeight` (`ZInQ.HeightFix.isPrintedStableHeight_of`) | T35 is proved (`uniformizationLeafAll_proof`) plus the textbook field `mumfordTorsionAlgClosed`; metric identification proved (height-fix: `isPrintedMetricSq_iff`, Haar uniqueness); semistability `κ̄(𝔭) ⇒ k(𝔭)` is the glue `SemiAbelianDescendsPerfect` (**open**) |

**Remaining step:** only `SemiAbelianDescendsPerfect`, in step (a). The other direction, printed ⇒ kernel, is
proved without it (`isStableFaltingsHeight_of_printed`, from Stacks 04KV). That direction is used for
faithfulness, §2.1.

### 2.1 `JavanpeykarRebase.JavanpeykarPrintedMap`: rated printed form, kind consequence (pending reading)

What the leaf states. Javanpeykar, *Algebra Number Theory* 8 (2014), Thm 1.1.1, p. 90 (locators recorded by the
audit, `locators.md` row R18, VERIFIED as recorded) states `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵` for a smooth
projective connected `X/ℚ̄` of genus `g ≥ 1`. The leaf states this at `X = X₀ ×_K ℚ̄`:
* `X₀` is a smooth proper geometrically connected curve over a number field `K`;
* `X` is assumed projective;
* `Jac(X)` is a `Pic⁰` representative `W` over `ℚ̄`, and `V` is a model of `W` over `K`;
* `deg_B(X)` is bounded above by the degree `d` of a given Belyi map (`IsBelyiMap`);
* `h_Fal` is height-fix's `IsPrintedStableHeight` of `V`. This is a Néron model over a field of semistable
  reduction read over `k(𝔭)`, with `ω = ⋀^g Γ(S, e*Ω¹)`, and the metric is the mass of the measure
  `(i/2)^g η ∧ η̄` defined chart by chart, which must exist.

Rating: **printed form**, entered as kind **consequence** with flag "pending reading" (review fix (1)).
* It is not stronger than the print: each hypothesis implies the corresponding one of the print.
* It is not stronger than javanpeykar-fix's leaf: `javanpeykarPrintedMap_of_fix` proves it from that leaf, given
  T35 and Stacks 04KV (VERIFIED). A height-fix printed height is a kernel height
  (`isStableFaltingsHeight_of_printed`), hence a height-dict printed height.
* It is not vacuous: the consumer proves every hypothesis, and a printed height exists under T35 for every
  group model (height-fix's `existsUnique_isPrintedMetricSq`).

Readings that remain before the leaf can count as LEAF. These are definitions, not theorem steps:
1. the stable height over `ℚ̄` read on a model over `K`;
2. "unramified" read at closed points through the ramification index;
3. "projective" read as a closed immersion into `ℙ(n; Spec ℚ̄)`;
4. height-fix's definition-level readings: the chart-wise density, and semistability over `k(𝔭)`.

### 2.2 `JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite`: rated printed form, locator UNVERIFIED

The leaf is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, §3.6, Thm 3.6.3(a)
(number from memory, UNVERIFIED). It is javanpeykar-fix's `ConstantFieldExtensionUnramifiedFull` with
`[Algebra.IsAlgebraic K L]` replaced by `[FiniteDimensional K L]`. It keeps the full-constant-field hypothesis
and `F ⊗_K L ≅ FL`, with places as valuation subrings `w ⊇ L` and `e = 1` as "a generator of `𝔪_{w ∩ F}`
generates `𝔪_w`".

Rating: **printed form**, flagged unread. It is the narrowest reading of the print, finite constant field
extensions. Whether or not Stichtenoth's §3.6 allows any algebraic `K'`, the finite case is printed.

Proved glue (VERIFIED):
* `exists_fd_of_tensor`: every element of `F ⊗_K L` (`L/K` algebraic) lies in the image of `F ⊗_K L'` for a
  finite subextension `L'`. The proof is by induction on tensors; `K⟮l⟯` is finite and finite sups are finite.
* `full_of_finite : ConstantFieldExtensionUnramifiedFinite → JavanpeykarFix.ConstantFieldExtensionUnramifiedFull`.
  For `x ∈ 𝔪_w`, take `L'` finite with `x` in the image of `F ⊗ L'`, and `E = ι(F) ⊔ L' ⊆ FL`.
  * `F ⊗_K L' → E` is injective because `F` is flat over `K` (`Module.Flat.lTensor_preserves_injective_linearMap`)
    and `F ⊗ L → FL` is injective.
  * It is surjective by `Algebra.TensorProduct.productMap_range` and
    `IntermediateField.sup_toSubalgebra_of_right`.
  * Apply the finite leaf at `(F, L', E, w ∩ E)`. The restriction of `w ∩ E` to `F` is `w ∩ F`, and
    `x ∈ 𝔪_{w ∩ E}` because `(A.comap f).nonunits` is `f⁻¹(A.nonunits)` (`mem_nonunits_comap`). This gives
    `x = ι π · y` with `y ∈ w`.
* `finite_of_full`: the converse, so the two forms are equivalent.

### 2.3 `ZInQ.HeightFix.SemiAbelianDescendsPerfect`: GLUE (height-fix, not new here)

This Prop is height-fix's (`docs/research/height-fix.md` §4). For a finite-type group scheme over a perfect
field, a semi-abelian identity component over `k̄` descends to a semi-abelian identity component over `k` with a
torus. The standard argument is Chevalley over perfect fields (Conrad 2002, Thm 1.1, UNVERIFIED). It is not
proved here: proving it needs Galois descent of the abelian quotient, which neither Mathlib 4.35 nor the tree
has.

## 3. What compiles (all VERIFIED on this host, 2026-11-16)

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.JavanpeykarRebase`
  succeeds (14114 jobs; `scratch/javanpeykar-rebase/build2.txt`).
* `#discharges` (`scratch/javanpeykar-rebase/Discharges.lean`, output `Discharges-output.txt`):

  ```
  DISCHARGES [OpenResearchLeaves28.javanpeykarBound] by JavanpeykarRebase.javanpeykarBound_of_printed_rebase_final
    still assumes: [JavanpeykarRebase.JavanpeykarPrintedMap,
   JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite,
   AvSplit.MumfordTorsionAlgClosed,
   ZInQ.HeightFix.SemiAbelianDescendsPerfect]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 45 open hypotheses, 6998 theorems checked, 29 discharge one
  ```

  `javanpeykarBound_of_printed_rebase` (with `UniformizationLeafAll` as a hypothesis), `full_of_finite`,
  `finite_of_full` and `javanpeykarPrintedMap_of_fix` each depend only on `[propext, Classical.choice, Quot.sound]`.
* Autofold:
  * `scratch/javanpeykar-rebase/autofold.json` is the deliverable spec. Its proof is
    `javanpeykarBound_of_printed_rebase_final {n}.javanpeykarPrintedMapHF {n}.constantFieldExtensionUnramifiedFinite
    {t}.mumfordTorsionAlgClosed {n}.semiAbelianDescendsPerfect`. Its leaves are:
    * `javanpeykarPrintedMapHF`: kind consequence, flag pending reading;
    * `constantFieldExtensionUnramifiedFinite`: kind published, flag unread with locator UNVERIFIED;
    * `semiAbelianDescendsPerfect`: kind project glue.
  * The dry run with `--allow-rise` exits 0 (`FoldDryRun-output.txt`). The generated module (`FoldDryRun.lean`)
    compiles, and `HDec.HSyn.sixContactMin_of_open39` depends only on the standard axioms
    (`FoldDryRun-compile.txt`).
  * `scratch/javanpeykar-rebase/autofold-with-height-fix.json` is the combined fold. Its dry run exits 0 without
    `--allow-rise`, and the generated `FoldDryRunHF.lean` compiles with standard axioms
    (`FoldDryRunHF-compile.txt`).
* The new file has no `sorry`, no `axiom`, and no code that runs at build time.

## 4. Notes for the integrator

* **height-fix's spec is stale on this base.** `scratch/height-fix/autofold.json` reads
  `{t}.uniformizationLeafAll`, which is no longer a field (proved, TailZ44); its dry run would fail to compile.
  The combined spec here replaces that argument with `_root_.uniformizationLeafAll_proof`.
* **If height-fix's fold lands first,** remove the `semiAbelianDescendsPerfect` leaf entry from `autofold.json`.
  The proof's `{n}.semiAbelianDescendsPerfect` then reads the existing field, which is in the same `research`
  bundle.
* This spec supersedes javanpeykar-fix's spec.
* Proposed `locators.md` rows (not edited here):
  * R18 printed: Javanpeykar 2014 Thm 1.1.1 at `X₀ ×_K ℚ̄`, over height-fix's printed stable height;
    `JavanpeykarRebase.JavanpeykarPrintedMap`.
  * Stichtenoth GTM 254 Thm 3.6.3(a), finite `K'/K`; `JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite`;
    locator UNVERIFIED.
* `origin/main` moved to c1e4ed1b after the merge. That commit was not merged; the fold was checked against
  e41a7169 + integrate-w82.
