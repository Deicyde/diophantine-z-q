# javanpeykar-fix: `javanpeykarBound` from printed leaves only

Task javanpeykar-fix (2026-11-16). Base: `wip/javanpeykar-dict` d3868494, with `origin/main` 0caafe66 and
`origin/wip/height-dict` 15cc5a60 merged in. Scratch: `scratch/javanpeykar-fix/`.
Lean: the top theorem is in `ZInQKernel/Contrib/OneProof/JavanpeykarFix.lean`. The helpers are
`ZInQKernel/Contrib/OneProof/JavanpeykarFix/{Basic,BelyiMap}.lean`, in namespace `JavanpeykarFix`.

## 1. Result

The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound` is **proved from two printed-form
leaves**, plus the two existing textbook fields that give T35. Only the standard axioms are used.

```lean
theorem JavanpeykarFix.javanpeykarBound_of_printed_fix (hJ : JavanpeykarPrintedMap)
    (hS : ConstantFieldExtensionUnramifiedFull)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightSplit.JavanpeykarBound
```

The review rated javanpeykar-dict's `JavanpeykarPrinted` as GLUE because of four dictionary steps. All four
are now closed. So is the Stichtenoth restatement.

| step | before (javanpeykar-dict) | now |
|---|---|---|
| (a) kernel height `IsStableFaltingsHeight` = `GroupModel.height` of the Néron model | leaf over the kernel height | **restated** over height-dict's `IsPrintedStableHeight`. The proof uses `isPrintedStableHeight_of`: the kernel's height implies the printed one, given T35 from `uniformizationLeafAll` and `mumfordTorsionAlgClosed`. `isPrintedStableHeight_iff` gives the converse. |
| (b) function field to morphism (Hartshorne I.6.8 / II.6.8) | only the `K`-to-`ℚ̄` half was proved | **restated and proved.** The leaf now takes a Belyi *map* `β : X → ℙ¹_ℚ̄ = Proj ℚ̄[X₀, X₁]` (`IsBelyiMap`). The glue `BelyiMapOfFunction` is proved (`belyiMapOfFunction_proof`, §3). |
| (c) projective vs proper | the print says projective, the leaf said proper | **restated and proved.** The leaf assumes `X` projective: a closed immersion into the vendored `ℙ(n; Spec ℚ̄)`. Every smooth proper integral curve over a field is projective (`exists_closedImmersion_projectiveSpace`). |
| (d) `V_ℚ̄ = Jac X` | asserted in the docstring | **restated and proved.** The leaf takes `W/ℚ̄` representing `Pic⁰_{X/ℚ̄}` (tensor-compatible) together with a model `V/K`, `V_ℚ̄ ≅ W`. The model exists by `exists_jacBar`, which uses the vendored `exists_abelianVariety_picardDegreeZero` over `ℚ̄` and `PicardTensorCompatible.baseChangeIso`. |
| Stichtenoth's full-constant-field hypothesis | missing from the leaf | **restated** as `ConstantFieldExtensionUnramifiedFull`. The hypothesis is proved at the consumer (`fullConstantField_of_bijective`): `K(X) ⊗_K K̄ ≅ K̄(X_K̄)` is javanpeykar-dict's `functionField_baseChange`, which holds because `X` is geometrically integral. |

**Target "-1 against the re-rated base": met.** The fold replaces `javanpeykarBound`, which the re-rated base
counts as GLUE, by two printed leaves. The autofold dry run against this base's `kinds.tsv` reads
`strict count: 34/11 on 45 -> 35/11 on 46; strictest 34/11 -> 35/11`. That `kinds.tsv` still lists the field as
LEAF, so GLUE stays at 11 there. Against a base that counts it as GLUE (34/12 on 45), the result is 35/11 on 46:
**GLUE −1**.

## 2. What compiles

All VERIFIED: compiled on this host on 2026-11-16.

* `lake build ZInQKernel.Contrib.OneProof.JavanpeykarFix` succeeds (12760 jobs).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.JavanpeykarFix`
  succeeds (13709 jobs).
* `#discharges`: the scratch file is `scratch/javanpeykar-fix/Discharges.lean`, its full output is in
  `Discharges-output.txt`.

  ```
  DISCHARGES [OpenResearchLeaves26.javanpeykarBound] by JavanpeykarFix.javanpeykarBound_of_printed_fix
    still assumes: [JavanpeykarFix.JavanpeykarPrintedMap,
   JavanpeykarFix.ConstantFieldExtensionUnramifiedFull,
   BPAnalytic.Uniformization.UniformizationLeafAll,
   AvSplit.MumfordTorsionAlgClosed]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 56 open hypotheses, 3119 theorems checked, 17 discharge one
  ```

  `belyiMapOfFunction_proof`, `exists_closedImmersion_projectiveSpace`, `exists_jacBar` and
  `belyiBaseChange_of_full` each depend only on `[propext, Classical.choice, Quot.sound]`.
* Autofold:
  * The spec is `scratch/javanpeykar-fix/autofold.json`. It discharges the field `javanpeykarBound` with the
    proof `javanpeykarBound_of_printed_fix {n}.javanpeykarPrintedMap {n}.constantFieldExtensionUnramifiedFull
    {t}.uniformizationLeafAll {t}.mumfordTorsionAlgClosed`. Both new leaves are kind `published` and flagged unread.
  * The dry run exits 0; its output is `FoldDryRun-output.txt`.
  * The generated module, `FoldDryRun.lean`, compiles. `HDec.HSyn.sixContactMin_of_open36` depends only on
    the standard axioms (`FoldDryRun-compile.txt`).
* The new files contain no `sorry`, no `axiom` and no build-time code. Nothing else under `ZInQKernel/` was edited.

## 3. The proof of step (b): a Belyi function gives a Belyi map (`JavanpeykarFix/BelyiMap.lean`)

Setting: `C` is a smooth proper integral curve over an algebraically closed field `k`, and `t ∈ k(C)` is a
Belyi function (kernel `IsBelyiFunction`) with `[k(C) : k(t)] = d`.

* **The map.** The chart is `Spec k[s] ≅ D₊(X₁) ⊆ ℙ¹` (vendored `Proj.standardOpenIso`). Through it, `[t : 1]`
  gives a point `Spec k(C) → ℙ¹`. This point extends to `β : C → ℙ¹` over `k` (vendored
  `exists_hom_of_valuationRing_stalk`), because the local rings of `C` are valuation rings and `ℙ¹` is proper.
* **Finite** (`isFinite_beta`). `β` is proper. Its fibres are finite for three reasons:
  * every point of `C` other than the generic point is closed (`isClosed_of_ne_genericPoint`, by a coheight
    argument with `dim 𝒪_z = 1` at closed points);
  * a closed set that misses the generic point is finite (Noetherian decomposition);
  * `β(η)` is not closed, because `s ↦ t` is injective.

  Mathlib's `IsFinite.of_isProper_of_locallyQuasiFinite` then gives finiteness.
* **Unramified at closed points over `ℙ¹ ∖ {0, 1, ∞}`** (`unramified`).
  * The germ at `β(x)` of the coordinate `s` pulls back to `t` (`stalkMap_secR`, the main identity:
    `germ_η(β^* σ) = ψ_t(r)` for the section `σ` given by `r ∈ k[s]`).
  * `t ≡ c (mod 𝔪_x)` with `c ∈ k` (Mathlib `residueFieldIsoBase`). Moreover `c ≠ 0, 1`, because `β(x)` lies in
    `D₊(X₀)` and `D₊(X₀ − X₁)`, whose preimages in the chart are `D(s)` and `D(s − 1)`.
  * The Belyi property at the valuation ring `𝒪_{C,x}` (`wOf`) makes `t − c` a generator of `𝔪_x`, and
    `t − c` is the image of an element of `𝔪_{β(x)}`.
* **Degree `d`** (`degree_eq`). The stalk map at the generic point is injective, and its image is exactly
  `k(t)`: elements of the stalk are fractions of sections `r ∈ k[s]`, and `ψ_t(r) ∈ k[t]`. So
  `[k(C) : k(ℙ¹)] = [k(C) : k(t)] = d` (Mathlib `Algebra.finrank_eq_of_equiv_equiv`).

## 4. The new leaves and their ratings

### `JavanpeykarFix.JavanpeykarPrintedMap`: printed form

Javanpeykar, *Algebra Number Theory* 8 (2014), Thm 1.1.1, p. 90 (read by the locator audit). For a smooth
projective connected curve `X/ℚ̄` of genus `g ≥ 1`, it states `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`. The leaf
states this for `X = X₀ ×_K ℚ̄`, where `X₀` is a smooth proper geometrically connected curve over a number field
`K` and `ℚ̄ = AlgebraicClosure K`. Each object of the print is a genuine definition:

* **`X`**:
  * smooth (base change of `X₀`) and connected (`X₀` is geometrically connected);
  * **projective**: a hypothesis, a closed immersion into the vendored `ℙ(n; Spec ℚ̄)`, which is the base change
    of `Proj ℤ[x_i]`.
* **`Jac(X)`**: `W`, an abelian variety over `ℚ̄` representing the degree-zero Picard functor of `X` with the
  tensor-product group law (vendored Jacobian-Challenge `picardFunctorDegree`, `PicardTensorCompatible`).
* **`h_Fal(X)`**: height-dict's `IsPrintedStableHeight` of a model `V/K` with `V_ℚ̄ ≅ W` (an isomorphism of
  abelian varieties). This is the definition of the stable height of an abelian variety over `ℚ̄`: the height
  over a number field of a model with semistable reduction. `IsPrintedStableHeight` itself passes to a field
  of semistable reduction.
* **`g`**: `genusBar X₀ = dim_ℚ̄ H¹(X, 𝒪_X)`.
* **Belyi map** (`IsBelyiMap`): `β : X → ℙ¹_ℚ̄ = Proj ℚ̄[X₀, X₁]` such that
  * `β` lies over `ℚ̄` and is finite;
  * at every closed point `x` with `β(x) ∈ D₊(X₀ X₁ (X₀ − X₁)) = ℙ¹ ∖ {0, 1, ∞}`, the maximal ideal of
    `𝒪_{ℙ¹, β(x)}` generates that of `𝒪_{X,x}`. This is ramification index `e_x = 1` in Hartshorne's definition
    (IV.2, `e_x = v_x(β^♯ u)`; number UNVERIFIED). The residue extension is trivial at closed points over the
    algebraically closed `ℚ̄`.
  * `d = [ℚ̄(X) : ℚ̄(ℙ¹)]`, the finrank of the stalk map at the generic point (Hartshorne II.6.8's degree).

  Then `deg_B(X) ≤ d`, and the printed bound is increasing in `deg_B`.

Rating: **printed form**, flagged unread. The leaf is the print restricted to curves defined over a number field
(every curve over `ℚ̄` is one), with `deg_B` replaced by an upper bound. It is not stronger than the print: each
hypothesis implies the print's.

It is not vacuous:
* the hypotheses are satisfiable, since this task proves every one of them at the consumer: projectivity, `W`
  and `V` (`exists_jacBar`), and `β` from a Belyi function (`belyiMapOfFunction_proof`);
* every curve over `ℚ̄` has a Belyi function (Belyi);
* `IsPrintedStableHeight` is attained given the kernel's SS1/N1 leaves (height-dict's
  `isPrintedStableHeight_iff`).

Readings that remain (definitions, not theorem steps):
1. height-dict's R1-R3, the stalk-level differentials and the invariant-measure form of `(i/2)^g ∫ η ∧ η̄`;
2. the stable height over `ℚ̄` read on a model over `K`;
3. "unramified" read at closed points via the ramification index;
4. "projective" read as a closed immersion into `ℙ(n; Spec ℚ̄)`.

### `JavanpeykarFix.ConstantFieldExtensionUnramifiedFull`: printed form, theorem number UNVERIFIED

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Thm 3.6.3(a): a constant field
extension of an algebraic function field is unramified. It is javanpeykar-dict's
`ConstantFieldExtensionUnramified` with one hypothesis added: Stichtenoth's standing hypothesis in §3.6 that `K`
is the full constant field of `F`, i.e. every element of `F` algebraic over `K` lies in `K`. It is therefore
weaker than javanpeykar-dict's form, and it is the print's statement. The theorem number is from memory and was
not read, so it is UNVERIFIED.

At the consumer the hypothesis is proved by `fullConstantField_of_bijective`. If `F ⊗_K L ≅ FL` with `L`
algebraically closed, then `a ∈ F` algebraic over `K` gives `ι(a) = c ∈ L`. Then `a ⊗ 1 = 1 ⊗ c`, and a
functional vanishing on `K` shows `a ∈ K`.

Rating: **printed form**, flagged unread, locator UNVERIFIED.

## 5. Proved glue (new in this task)

| theorem | content |
|---|---|
| `fullConstantField_of_bijective`, `isBelyiFunction_baseChange_full`, `belyiBaseChange_of_full` | Stichtenoth with full constant field ⇒ javanpeykar-dict's `BelyiBaseChange` |
| `exists_jacBar` | step (d) |
| `exists_closedImmersion_projectiveSpace` | step (c). Proof: vendored Chow lemma; the inverse of the modification over a dense open extends to `g : X → M` (valuative extension); `g` is a section of the separated `M → X`, so it is a closed immersion (Mathlib `IsClosedImmersion.of_comp`). |
| `P1`, `P1.threePointsCompl`, `IsBelyiMap`, `JavanpeykarPrintedMap`, `BelyiMapOfFunction`, `javanpeykarBound_of_map` | definitions and the reduction (`Basic.lean`) |
| `belyiMapOfFunction_proof` and its lemmas | step (b) (`BelyiMap.lean`, §3) |
| `javanpeykarBound_of_printed_fix` | the top theorem (`JavanpeykarFix.lean`) |

Step (a) uses height-dict's `isPrintedStableHeight_of`. Steps (1)-(2) of javanpeykar-dict (the Jacobian is
`Pic⁰`; `dim J` is the genus of `X_ℚ̄`) and `functionField_baseChange` are reused unchanged.

## 6. Proposed rows for the integrator (not edited here)

* `locators.md`:
  * *R18 printed: Javanpeykar 2014, Thm 1.1.1, p. 90; §2.3 p. 98; `JavanpeykarFix.JavanpeykarPrintedMap`.
    Printed form at `X = X₀ ×_K ℚ̄` (Belyi map as a finite morphism to `Proj ℚ̄[X₀, X₁]`, `Jac(X)` the `Pic⁰`
    representative over `ℚ̄`, printed stable height of a model over `K`).*
  * *Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Thm 3.6.3(a) (full constant field);
    `JavanpeykarFix.ConstantFieldExtensionUnramifiedFull`; locator UNVERIFIED.*
* The javanpeykar-dict autofold spec is superseded by `scratch/javanpeykar-fix/autofold.json`.

## 7. What remains

* Both leaves are flagged unread (no human reading). Stichtenoth's theorem number is UNVERIFIED.
* height-dict's definition-level readings R1-R3 of the printed height are shared by every height leaf and are
  not touched here.
* `locators.md`, `kinds.tsv` and `OPEN.md` are not edited (by the task rules).
