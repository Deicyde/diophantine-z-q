# The special-fibre Atkin–Lehner action: foundations (rc-model-generic7)

**Retired frozen fields: none yet.** This run retires no frozen field and discharges no hypothesis of `GoodRowWire.oddStagedOfSamePlace` (`ZInQKernel/Contrib/OneProof/RC/GoodRowWire/Assembly.lean:83`). The hRC GLUE row (`docs/one-proof/OPEN.md`, section hRC) and its odd-side input `PreLeaves.odd_staged` (`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:305`) are unchanged.

**No error verdict.** No false manuscript claim, failed computation or misread citation was found. No leaf was added or proposed.

**Main result.** Items 1, 2 (for formula-carrying seams) and the item-3 foundations (a), (b), (c), the naturality, the cyclicity lemma, R0, R1′ and R2 are complete. **Scoped stop** for two pieces: R3 (the composite Vélu quotient commutes with reduction) and the every-seam form of item 2 (it needs T3, seams along a ring isomorphism); generic8 needs only the R0-seam form. Exact open statements are in "What remains".

**Pieces of `SamePlaceData` fields supplied (none of them retires a field):**
- `point_W`: `PointW` (the `point_W` field as a named Prop, `Interface.lean:43`; SP2's assembly takes it as a hypothesis and the point_W assembly proves it), `atkinLevelAlg` (`Interface.lean:33`) and the Wint lemma `Wint_left` (`Interface.lean:70`), stated under `ModelGeneric5.levelCommRing`, the `CommRing` instance `Wint` is built with (`RC/ModelGeneric5/Extension.lean:55`). The point_W assembly applies them with the same-place lane's φ lemma. The special-fibre action itself (`atkinLevel_moduli_special`) belongs to generic8. Inputs of it that closed here: item 2 for R0 seams at fields of cardinality 𝔠, the computation lemma (b), the lift (c), the naturality, the cyclicity lemma, R0, R1′ and R2.
- `point_frob`: the naturality of `Y0LevelPoints` along ring isomorphisms (`Y0LevelPoints_algEquiv`, `Y0Points.lean:192`; general form `Y0LevelPoints_comp`, `Y0Points.lean:171`, for every `LocalIntegers ell`-algebra map of algebraically closed fields). This is an input of point_frob's `Y0LevelPoints` half. SP2 proves point_frob, using its identification of the same-place lane's Frobenius twist with `pairClassesMap` along the Frobenius automorphism.

All 8 new modules are under `ZInQKernel/Contrib/OneProof/RC/ModelGeneric7/`: `Interface`, `PairMap`, `Y0Points`, `Lift`, `SeamFormula`, `FormulaTransport`, `Reduction` and `ReductionTwo`. Each builds with `lake build`, with no `sorry` and no axiom declaration. Every `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound` (build tails: `scratch/rc-model-generic7/builds/*.tail`). Helpers without a print line (`pointMapAlong_apply`, `pointMapAlong_injective`, `pairClassesMap_mk`, `pointMapAlong_id`, `pointMapAlong_comp`, `pairClassesMap_apply_symm`, `shortCoverPair_class_comp`, `coverPair`, `pointCast_apply`, `pointCast_injective`, `ker_pointCast_comp`, `OddStepFormula`, `TwoStepFormula`, `StepFormula`, the `Red` and `PtRel` lemmas, `velu2X_map`, `velu2Y_map`, `smulSubgroup_map`, `mem_of_torsion`, `reduceHom_ne_zero`, `red_*`) are covered through printed dependents.

Item 1 (the reviewer's doc fixes to the generic6 and generic5 reports, (a)–(n)) is one commit (e131c3c7f), doc only plus the two docstring lines of (g) and (i); both files keep their line counts and were rebuilt.

## New definitions and theorems

`Interface.lean` (piece (a); the INTERFACE block)
- `atkinLevelAlg h₅ htame h₂ hQ` and `PointW h₅ htame h₂ point`: placed exactly as written in the INTERFACE block, in namespace `ZInQ.Manuscript.RC.ModelGeneric7`. Both elaborate on the base; no change to the block was needed. `atkinLevel_moduli_special` is not stated here.
- `Wint_left`: `(ModelGeneric5.Wint h₅ htame h₂ hQ).left = Spec.map (CommRingCat.ofHom (atkinLevelAlg h₅ htame h₂ hQ : _ →+* _))` (by `rfl`), under `attribute [local instance 2000] ModelGeneric5.levelCommRing`, in a section separate from the block. `atkinLevelAlg_toRingHom`: the ring map is `atkinLevel` (`rfl`).
- `smulSubgroup_cyclic`: for `C` cyclic of order `N = Q * M`, `M ≠ 0`, `smulSubgroup M C` is cyclic of order `Q`. `smulSubgroup_div_cyclic`: the form at `M = N / Q`, `Q ∣ N`, `N ≠ 0` (exists_quotientSeam's `hH` at `C_Q`).

`PairMap.lean` (item 2, T1 and T2; no characteristic hypothesis)
- `pointMapAlong σ W`: TauCeti's `Point.mapAlong` along a ring map `σ` of fields, as an additive map. `ptMap_eq_pointMapAlong`: the vendored `ptMap` is the same map.
- `pairClassesMap σ N : PairClasses k₁ N → PairClasses k₂ N`: the class of `(E, C)` goes to the class of `(E.map σ, C.map (pointMapAlong σ E))`. It is well defined because `v` goes to `v.map σ` (Mathlib's `map_variableChange`) and the variable-change point maps commute with `pointMapAlong` (`addEquivVariableChange_pointMapAlong`). `pairClassesMap_id`, `pairClassesMap_comp`, `pairClassesMap_symm_apply` and `pairClassesMap_injective` (for ring isomorphisms).
- `cyclicQuotientCurve_map` (T2): `(V.map σ).cyclicQuotientCurve (H.map (pointMapAlong σ V)) N = (V.cyclicQuotientCurve H N).map σ`, for algebraically closed source, in every characteristic. It re-derives the `hc` step of the vendored `cyclicQuotientJ_map` from the public `iterate_cqjStep_stMap`.
- `shortCoverPair_comp`: `shortCoverPair (σ ∘ f) = enhancedMap σ (shortCoverPair f)`, for every algebra map `σ` of fields.
- `rationalPoints_comp`: `rationalPoints h₂ (σ ∘ x) = pairClassesMap σ (rationalPoints h₂ x)` for every `ℚ`-algebra map of algebraically closed fields of characteristic 0. `rationalPoints_ringEquiv` gives the ring-isomorphism form.

`Y0Points.lean` (pieces (b) and the naturality; any characteristic)
- `coverPair h₅ htame f`: `shortCoverPair` at a point `f` of `UniversalExactOrderAlgebra ell (n + 2) h₅ htame`, with the cover's global instances.
- `Y0LevelPoints_comp_inclusion`: `Y0LevelPoints h₅ htame h₂ (f.comp (Y0LevelInclusion h₅ htame h₂)) = Quot.mk _ (coverPair h₅ htame f)` at level `n + 2`, for every algebraically closed `k` with `Algebra (LocalIntegers ell) k`.
- `exists_comp_inclusion`: every `k`-point of the level algebra is `f.comp Y0LevelInclusion`.
- `Y0LevelPoints_comp`: `Y0LevelPoints (σ.comp x) = pairClassesMap σ N (Y0LevelPoints x)` for every `LocalIntegers ell`-algebra map `σ` of algebraically closed fields. `Y0LevelPoints_algEquiv` gives the algebra-isomorphism form.

`Lift.lean` (piece (c); no Hensel citation)
- `wittLocalAlgebra ell k`: `IsLocalization.lift` of `Int.castRingHom (WittVector ell k)` (`wittVector_isUnit_intCast`).
- `localIntegers_ringHom_ext`: ring maps out of `LocalIntegers ell` are unique. `constantCoeff_comp_algebraMap` follows.
- `exists_wittLift`: for `k` algebraically closed of characteristic `ell` with any `Algebra (LocalIntegers ell) k`, every cover point `f` over `k` has a lift `F` over `W(k)` with `constantCoeff (F a) = f a`. The proof uses the tree's private `detectorCover_smooth` (reached with `open private`), `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`, `WittVector.isAdicCompleteIdealSpanP` and `WittVector.quotientPEquiv`.

`SeamFormula.lean` (R0; every characteristic prime to `n`)
- `OddStepFormula E c' p f`: off `⟨c'⟩`, `f (x, y) ≠ 0` and `(f (x, y)).coordsOrZero = (E.veluX S x, E.veluY S x y)`, with `S = E.oddOrderSummingSet c' (p / 2)`. `TwoStepFormula E c' f`: `c' = (x₀, y₀)`, and `f` agrees with the vendored `veluPointMap2` at `(x₀, y₀)` on the zero locus and on `coordsOrZero`. `StepFormula` is the conjunction by cases on `p = 2`. Both are read on coordinates, so they survive the Sigma equations of the bridges.
- `FormulaSeam E H c n g` (inductive predicate; its recursor is the induction principle generic8's R4 uses):
  - `one`: for `H = ⟨c⟩` with `addOrderOf c = 1`, `g` is `pointCast (cyclicQuotientCurve_one E H).symm`.
  - `step`: for `n ≥ 2` and `p = n.minFac`, `g = pointCast (stepEq …) ∘ g' ∘ f`. Here `(E.stepCurve H p).IsElliptic`, `f.ker = ⟨(n/p) • c⟩`, `StepFormula E ((n/p) • c) p f` and `H.map f = E.stepSubgroup H p`, and `g'` satisfies `FormulaSeam (E.stepCurve H p) (H.map f) (f c) (n/p)`.
  - `stepEq`: `(E.stepCurve H n.minFac).cyclicQuotientCurve (H.map f) (n / n.minFac) = E.cyclicQuotientCurve H n`.
- `exists_oddStep_formula`, `exists_twoStep_formula`: the prime steps at a given generator, with kernel `⟨Q⟩` and formula (they refine `exists_oddStep` and `stepSeam_two`).
- `exists_formulaSeam`: for `H = ⟨c⟩` with `addOrderOf c = n` and `(ℓ : k) ≠ 0` for each prime `ℓ ∣ n`, it gives `(E.cyclicQuotientCurve H n).IsElliptic`, `ι`, `hι`, `FiniteAlong k ι`, `finrankAlong k ι = n`, and `g` with `g.ker = H`, `IsSeam ι hι g` and `FormulaSeam E H c n g`. `exists_quotientSeam_of_formulaSeam` proves the statement of `ModelGeneric6.exists_quotientSeam` from it, so the variant is at least as strong.

`FormulaTransport.lean` (item 2)
- `veluX_map`, `veluY_map`, `velu2X_map`, `velu2Y_map`, `oddOrderSummingSet_map`: the vendored formulas along a ring map `σ`.
- `PtRel P P'`: both points are zero, or both are nonzero with equal `coordsOrZero`, on possibly different curves. `stepRel` and `formulaSeam_rel`: two `FormulaSeam` composites, at `(E, H, c, n)` over `K₁` and at `(E.map σ, H₂, c₂, n)` over `K₂` with `c₂ ~ σ c`, satisfy `G P₂ ~ σ (g P)` whenever `P₂ ~ σ P`.
- `rationalPoints_atkinRat_formulaSeam` (**item 2 for R0 seams**). Let `K` be algebraically closed of characteristic 0 with `#K = 𝔠`, let `(E, C)` represent `rationalPoints h₂ x`, let `c` generate `C_Q = smulSubgroup (N / Q) C.1` with `addOrderOf c = Q`, and let `g` have kernel `C_Q` with `FormulaSeam E C_Q c Q g`. Then `rationalPoints h₂ (x.comp (atkinRatAlg h₂ hQ)) = [⟨E.cyclicQuotientCurve C_Q Q, hE', atkinImage E … C g hg⟩]`. The proof takes a ring isomorphism `σ : K ≃+* ℂ` (`IsAlgClosed.ringEquiv_of_equiv_of_charZero`, `Cardinal.mk_complex`) and the complex R0 seam at `σ c`. It applies `ModelGeneric6.rationalPoints_atkinRat_complex_moduli` and returns to `K` through `rationalPoints_comp`, `cyclicQuotientCurve_map`, `formulaSeam_rel`, `torsionBy_map_ringEquiv` and the injectivity of `pairClassesMap σ`. Only the algebraic statement is transported; no complex-analytic step is.
- `atkinClass_independent_formulaSeam`: the class depends neither on the representative nor on the generator (corollary).

`Reduction.lean` (R1′; `A` a valuation subring of an algebraically closed `L`)
- `Red A a ā` means `a ∈ A` with residue `ā`. It is closed under `+`, `*`, `-`, powers, numerals, finite sums, and division by elements of nonzero residue.
- `veluX_red`, `veluY_red`: the odd formulas reduce, for an integral summing set that is injective under reduction and whose `x`-residues differ from the residue of `x`.
- `coordsOrZero_reduceHom`, `oddOrderSummingSet_reduceHom`: on torsion prime to the residue characteristic, reduction acts on coordinates and on summing sets by the residue map.
- `oddVelu_reduceHom` (**R1′**): suppose `W/A` has good reduction, `Q₀` has odd prime order `p` with `(p : ResidueField A) ≠ 0`, and `φ`, `φ'` are the odd step maps over `L` and over the residue field, given by their kernel and `OddStepFormula` at `Q₀` and at `reduceHom Q₀`. Let `V/A` have good reduction with `V.map A.subtype = V₁` and `V.map (residue A) = V₂`. Then for every `P` with `m • P = 0`, `(m : ResidueField A) ≠ 0`: `reduceHom hΔV (pointCast hV₁.symm (φ P)) = pointCast hV₂.symm (φ' (reduceHom hΔ P))`.

`ReductionTwo.lean` (R2)
- `veluQuotient2_map_subtype`, `veluQuotient2_map_residue`: the curve-level reduction of the order-two quotient.
- `veluPointMap2_reduceHom`: `veluPointMap2` commutes with `reduceHom` on prime-to-residue torsion (same form as R1′).

## What generic8 needs (names and file:line at the final commit)

| Input | Lean name | file:line (under `ZInQKernel/Contrib/OneProof/RC/ModelGeneric7/`) |
|---|---|---|
| item 2 at fields of cardinality 𝔠 (R0 seams) | `rationalPoints_atkinRat_formulaSeam` | `FormulaTransport.lean:309` |
| T1 | `pairClassesMap`, `_id`, `_comp`, `_symm_apply`, `_injective` | `PairMap.lean:129, 172, 187, 203, 216` |
| T2 | `cyclicQuotientCurve_map` | `PairMap.lean:231` |
| ptMap = Point.mapAlong | `ptMap_eq_pointMapAlong` | `PairMap.lean:58` |
| naturality of rationalPoints | `rationalPoints_comp` | `PairMap.lean:286` |
| atkinLevelAlg, PointW, Wint lemma | `atkinLevelAlg`, `PointW`, `Wint_left` | `Interface.lean:33, 43, 70` |
| (b) computation lemma, cover lifts | `Y0LevelPoints_comp_inclusion`, `exists_comp_inclusion` | `Y0Points.lean:72, 139` |
| (c) lift to W(k) | `wittLocalAlgebra`, `exists_wittLift` | `Lift.lean:58, 80` |
| naturality of Y0LevelPoints | `Y0LevelPoints_comp`, `Y0LevelPoints_algEquiv` | `Y0Points.lean:171, 192` |
| cyclicity of C_Q | `smulSubgroup_cyclic`, `smulSubgroup_div_cyclic` | `Interface.lean:92, 119` |
| R0 predicate, existence | `FormulaSeam`, `exists_formulaSeam` | `SeamFormula.lean:122, 305` |
| R0 naturality along ring maps | `formulaSeam_rel` | `FormulaTransport.lean:224` |
| R1′ | `oddVelu_reduceHom` | `Reduction.lean:249` |
| R2 | `veluQuotient2_map_subtype`, `veluQuotient2_map_residue`, `veluPointMap2_reduceHom` | `ReductionTwo.lean:30, 37, 48` |
| R3 | open (statement below) | — |

## Copies (the two named exceptions)

1. `equivalent`, the internal step of `Pinned.Y0LevelPoints` (`ZInQKernel/Contrib/OneProof/RC/ModelLevels3/Y0LevelPoints.lean:64-90`, base `aba99b7b2e3eea8804ebeffd1834ba5f31fa9c7e`). It is repeated verbatim, statement unchanged, as a `have` inside `Y0LevelPoints_comp_inclusion` (`Y0Points.lean:100-130`, between a provenance line and an end marker). The preamble `let` lines are those of `Y0LevelPoints.lean:42-63`, and the same four private declarations are opened with `open private` (`Y0Points.lean:33-36`).
2. The CharFreeSeam family (adapted, not verbatim; each block carries a provenance line):
   - `exists_oddStep_formula` (`SeamFormula.lean:142-208`) adapts the proof of `exists_oddStep` (`RC/ModelGeneric6/CharFreeSeam.lean:143-201`);
   - `exists_twoStep_formula` (`SeamFormula.lean:210-294`) adapts the proof of `stepSeam_two` (`RC/ModelGeneric6/CharFreeSeamTwo.lean:162-234`);
   - `exists_formulaSeam` (`SeamFormula.lean:296-410`) adapts the proof of `exists_quotientSeam_of_steps` (`RC/ModelGeneric6/CharFreeSeam.lean:210-265`).

   The adaptations take the generator as input, record the formula and kernel, and replace the goal rewrite at `CharFreeSeam.lean:255` by `seam_transport` along `stepEq`. Reused exports, not copied: `twoFFHom_seam`, `finrankAlong_twoFFHom_le`, `finrankAlong_ne_one_of_seam`, `isSeam_comp`, `finrankAlong_comp'`.

## What remains

| Item | Tier | Exact open statement / reduces to |
|---|---|---|
| R3: the composite commutes with reduction | medium | For `W/A` with good reduction (`A` a valuation subring of an algebraically closed `L`) and `H ≤ (W.map A.subtype).Point` cyclic of order `n` with `(n : ResidueField A) ≠ 0`, there is `V/A` with good reduction, `V.map A.subtype = (W.map A.subtype).cyclicQuotientCurve H n` and `V.map (residue A) = (W.map (residue A)).cyclicQuotientCurve (H.map (reduceHom hΔ)) n`. Induction along `FormulaSeam` (or along `cyclicQuotientCurve_eq_of_two_le`). Each step uses the odd curve reduction (vendored `exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom`) or R2 on curves, the bridges `stepCurve_stepSubgroup_eq_of_prime_ne_two` and `stepCurve_stepSubgroup_two_eq` (step curve and step subgroup equal the Vélu quotient and `H.map φ`), and R1′ or R2 on points, to reduce `H.map φ` to `(H.map reduceHom).map φ'`. Well-known background: Vélu, C. R. Acad. Sci. Paris 273 (1971) (formulas), Silverman AEC 2nd ed. VII.3.1 (UNVERIFIED). generic8's R4 may make R3 unnecessary, by comparing images along `FormulaSeam` directly with R1′/R2. |
| item 2 for every seam (not only R0 seams) | medium | The statement of `rationalPoints_atkinRat_formulaSeam` for every `g` with `ModelGeneric6.IsSeam ι hι g`, `FiniteAlong K ι` and `g.ker = C_Q`. It reduces to T3 (a seam over `K` gives a seam over `ℂ` between the base-changed curves, commuting with `pointMapAlong σ`), or to class-level uniqueness of separable quotients (Silverman III.4.11–4.12, UNVERIFIED). generic8 does not need it: its route uses R0 seams over `K'`. |
| T4, T5 | — | not needed on the ring-isomorphism route (`pairClassesMap_injective` from `map_comp`/`map_id`). |
| the INTERFACE theorem `atkinLevel_moduli_special` | large (generic8) | generic8's route: lift through `exists_comp_inclusion` and `exists_wittLift`; read over `K'` with `rationalPoints_atkinRat_formulaSeam` at the R0 seam; descend the class reading; compare seam images with R4 (induction on `FormulaSeam`, with R1′, R2 and torsion reduction); change the representative. |

## Tiers for point_W

The point_W assembly still needs, to prove `PointW` for the same-place lane's point map:
- the same-place lane's `point`, point form, φ lemma and `sigmaQ` (`X.W`);
- the `X.W` comparison for every separable seam (SP2, which carries uniqueness of separable quotients up to isomorphism in characteristic ℓ, Silverman III.4.11–4.12, UNVERIFIED);
- generic8's special-fibre action `atkinLevel_moduli_special`.

For `sp`, it also needs SP2's `SamePlaceData` assembly with `PointW` as a hypothesis. This lane needs no uniqueness, because the INTERFACE theorem is existential.

## Known issues

- `Wint_left` holds by `rfl` only under `ModelGeneric5.levelCommRing`. The synthesized `CommRing` on `Pinned.Y0LevelAlgebra` takes another path (`RC/ModelGeneric5/Extension.lean:50-52`), so consumers must use the same local instance.
- `Y0Points.lean` depends on four private declarations through `open private` (`detectorShort_domain`, `detectorLevel_isUnit`, `detectorCoverAlgebra`, `detectorCoverTower`), and `Lift.lean` on the private `detectorCover_smooth`; a rename there breaks these files.
- `coverPair` is needed because instance search does not find the cover's global `Algebra (LocalIntegers ell)` instance at `ExactOrderAlgebra (shortFamily _) (coverLevel_isUnit …)` (the proof argument differs from the abbrev's).
- The R1′/R2 statements take `[IsAlgClosed L]` and `[IsAlgClosed (ResidueField A)]`, because `OddStepFormula` lives in a section with `[IsAlgClosed k]`. The residue instance follows from `isAlgClosed_residue_of_valuationSubring`.
- `T2` uses the vendored internal names `iterate_cqjStep_stMap` and `stepCurve_map` (namespace `P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.P2MKcCQJbc`), with the same re-vendoring caveat as `mrtw60aVCFunHom`.
- Inherited: the Milne locators at tex 1784-1788; Jetchev–Kane (arXiv v1) cites Ribet 1990 Prop. 3.3 and prints none of the three compatibilities; Ribet's Prop. 3.3 and Rem. 3.5 are not sources (Prop. 3.6 is); the vendored `nonempty_functionField_algEquiv_of_variableChange` states only `Nonempty`.

## Manuscript check

- tex 8487-8489 (`W_{p^e}` with eigenvalue `w_{p^e}`; the moduli form of `W_Q` on geometric points): the manuscript gives no moduli form. The `K`-point form for R0 seams is formalized here (`rationalPoints_atkinRat_formulaSeam`), ON THE SPOT (c): transport of the complex moduli formula along a ring isomorphism `K ≃+* ℂ`, using that Vélu formulas commute with ring maps. Verdict: gap filled (characteristic 0); the special fibre is open (generic8).
- tex 8476-8478 (good reduction of the modular curve, `ℓ₀ ∤ N`): relied on through the pinned integral model; the lift to `W(k)` (`exists_wittLift`) uses smoothness of the cover (Mathlib, no citation). Verdict: OK.
- tex 8479-8492 (the same-place compatibilities, Atkin–Lehner and Frobenius): the manuscript asserts them; this run supplies pieces only (`PointW`, `atkinLevelAlg`, `Wint_left`, the naturality of `Y0LevelPoints`, R0, R1′, R2). Verdict: unverified (assembly pending: generic8, SP2, point_W assembly).
