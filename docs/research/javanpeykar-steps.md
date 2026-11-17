# javanpeykar-steps: `javanpeykarPrintedMapHF` as a direct instance of Javanpeykar's Thm 1.1.1

Task javanpeykar-steps (2026-11-17). Scratch: `scratch/javanpeykar-steps/` (results log `log.md`, the
compiled file `JavanpeykarThm111.lean`, the fold spec `autofold.json`, the `#discharges` check
`Discharges.lean` / `discharges_out.txt`). Deliverable: `ZInQKernel/Contrib/OneProof/JavanpeykarThm111.lean`
(namespace `JavanpeykarSteps`), importing `ZInQKernel.Contrib.OneProof.JavanpeykarRebase`, the module that
defines the statement. Base: `main` e1b31749 with `origin/wip/leaf-fold33b` (c66e1c024) merged, since it
was not yet on `main`.

## 1. Result

**VERIFIED (compiled, standard axioms only):**

```lean
theorem JavanpeykarSteps.javanpeykarPrintedMap_of_thm111 (hJ : JavanpeykarThm111) :
    JavanpeykarRebase.JavanpeykarPrintedMap
```

The theorem has **no hypothesis other than the new leaf.** `JavanpeykarThm111` is Javanpeykar's
Thm 1.1.1 as printed, together with the height identification printed on p. 9 of the same paper. The
bundle field `javanpeykarPrintedMapHF` (kind consequence, GLUE, flagged pending reading) becomes a direct
instance of one printed leaf. **GLUE −1, LEAF +1** if a reviewer rates the leaf printed form; see §4 for my
rating. The fold spec is `scratch/javanpeykar-steps/autofold.json`.

`#print axioms` for `javanpeykarPrintedMap_of_thm111`, `isBelyiMorphism_of_isBelyiMap`,
`isPrintedStableHeight_of_iso` and `isPrintedStableHeight_unique` gives `[propext, Classical.choice, Quot.sound]`.

## 2. The leaf, restated as printed

Print (Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8
(2014), Thm 1.1.1, p. 90 = arXiv:1403.6404v1 p. 1; reading recorded in docs/research/locators.md row R18):
for a smooth projective connected curve `X` over `ℚ̄` of genus `g ≥ 1`,
`h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`. Here `deg_B(X)` is the least degree of a finite morphism `X → ℙ¹_ℚ̄`
unramified over `ℙ¹ ∖ {0, 1, ∞}`, and (p. 9, §2.3, citing Moret-Bailly, *Pinceaux*, Lemme 3.2.1)
`h_Fal(X)` is the stable Faltings height of `Jac(X)`.

```lean
def JavanpeykarThm111 : Prop :=
  ∀ (Qbar : Type) [Field Qbar] [IsAlgClosed Qbar] [CharZero Qbar] [Algebra.IsAlgebraic ℚ Qbar]
    (X : Over (Spec (CommRingCat.of Qbar))) [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
    [IsIntegral X.left],
    (∃ (n : Type) (_ : Finite n) (i : X.left ⟶ ℙ(n; Spec (CommRingCat.of Qbar))),
      IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (CommRingCat.of Qbar)) ↘ Spec (CommRingCat.of Qbar) = X.hom) →
    1 ≤ genus X →
    ∀ (W : AbelianVariety Qbar) (repW : (picardFunctorDegree X.hom 0).obj.RepresentableBy W.group.X),
      PicardTensorCompatible X.hom W.group repW →
    ∀ h : ℝ, IsStableHeightBar W h →
    ∀ dB : ℕ, IsBelyiDegree X dB →
    h ≤ javanpeykarBound (genus X) dB          -- javanpeykarBound g d = 13 * 10^6 * g * d^5
```

All definitions are new and short, and each is built on Mathlib or on definitions the repository already has:

| printed object | Lean | dictionary |
| --- | --- | --- |
| `ℚ̄` | any `Qbar`, algebraically closed and algebraic over `ℚ` | all algebraic closures of `ℚ` are isomorphic and the statement is invariant under isomorphism (STANDARD) |
| smooth projective connected curve | smooth of relative dimension 1, proper, integral, closed immersion into `ℙ(n; Spec ℚ̄)` | integral implies connected, and a smooth connected scheme over a field is integral, so this is no stronger than the print |
| `g` | `genus X = dim H¹(X, 𝒪_X)` (vendored `Scheme.arithmeticGenus`) | the genus of a smooth projective curve (Hartshorne IV.1, STANDARD) |
| `Jac(X)` | `W` representing `Pic⁰_{X/ℚ̄}` with the tensor group law (vendored) | as in javanpeykar-fix and javanpeykar-rebase |
| `h_Fal(X)` | `IsStableHeightBar W h`: `h` is height-fix's printed stable height `IsPrintedStableHeight` of a model `V` of `W` over a number field `L ⊆ ℚ̄` (`V_ℚ̄ ≅ W`) | p. 9: the stable Faltings height of `Jac X`. The stable height of an abelian variety over `ℚ̄` is the stable height of any model over a number field (Faltings 1983 §1; Deligne, Bourbaki 616; UNVERIFIED locators) |
| unramified over `ℙ¹ ∖ {0,1,∞}` | `LocallyOfFiniteType (β ∣_ U) ∧ FormallyUnramified (β ∣_ U)` (Mathlib) | "unramified" means locally of finite type and formally unramified (EGA IV 17.3.1, Stacks 02G3; numbers UNVERIFIED) |
| degree of `β` | `finrank` of `k(X)` over `𝒪_{ℙ¹, β(η)}` | `[k(X) : k(ℙ¹)]` (Hartshorne II.6.8). `β(η)` is the generic point of `ℙ¹` because a finite map cannot send the generic point of a curve to a closed point; this is not proved in Lean, but the clause is the same one javanpeykar-fix's `IsBelyiMap` uses |
| `deg_B(X)` | `IsBelyiDegree X dB := IsLeast {d | 0 < d ∧ ∃ β, IsBelyiMorphism X β d} dB` | restricting to positive degrees changes nothing, since degrees of finite maps are positive; if anything it weakens the leaf |

## 3. The steps (all proved in Lean)

* **(1) `X₀ ×_K K̄` is an instance.** In `javanpeykarPrintedMap_of_thm111`, `ℚ̄ := AlgebraicClosure K` is
  algebraic over `ℚ` by `Algebra.IsAlgebraic.trans ℚ K K̄`. The base change is proper and smooth of
  relative dimension 1 (instances, as in javanpeykar-rebase). Integrality and projectivity are hypotheses
  of the old leaf. `genus (baseChangeCurve X₀ K̄)` and `genusBar X₀` are definitionally equal.
* **(2) `deg_B ≤ d`, monotone bound.** `exists_isBelyiDegree_le` (via `Nat.find`) and `javanpeykarBound_mono`
  (via `gcongr`).
* **(3) Ramification index 1 implies unramified.** `isBelyiMorphism_of_isBelyiMap`, over any field of
  characteristic 0, for `C` integral, proper, smooth of relative dimension 1. The property is checked
  stalkwise with Mathlib's `HasRingHomProperty.of_stalkMap` and `RingHom.FormallyUnramified.ofLocalizationPrime`,
  through `morphismRestrictStalkMap`. At `y` over `U` the stalk map is shown formally unramified by
  `Algebra.FormallyUnramified.of_map_maximalIdeal`:
  * the residue field extension is finite (`β` finite, hence quasi-finite: `Scheme.Hom.quasiFiniteAt`,
    `Algebra.QuasiFinite.of_restrictScalars`, `Module.Finite.of_quasiFinite`), hence separable in
    characteristic 0;
  * at a closed point, `𝔪_{β y} 𝒪_{C,y} = 𝔪_y` is the `IsBelyiMap` clause;
  * at the generic point it holds automatically, since `𝒪_{C,η} = k(C)` is a field;
  * every other point is closed (javanpeykar-fix's `isClosed_of_ne_genericPoint`).

  The degree and finiteness clauses carry over unchanged.
* **(H2) `V` is a `K`-form of `Jac`; the height is invariant under isomorphism.** In the instance, `V`
  over `L = K` with `V_K̄ ≅ W` witnesses `IsStableHeightBar W x`. Two related lemmas are also proved:
  * `isPrintedStableHeight_of_iso`: height-fix's printed height is invariant under isomorphism of
    abelian varieties. It uses javanpeykar-dict's `transport` (the same `𝒪_L`-scheme, so the printed
    metric data agree by definition), `isNeronModel_transport`, and `dim_eq_of_iso` (Krull dimension
    through `Scheme.homeoOfIso`);
  * `isStableHeightBar_of_iso`: the same for the height over `ℚ̄`.
* **(H3) One value.** `isPrintedStableHeight_unique (hT35 hGC hN1 hSS2)`: two printed heights of one
  abelian variety over a number field are equal. Both are kernel stable heights
  (`ZInQ.HeightFix.isStableFaltingsHeight_of_printed`; checked: it takes T35 and Stacks 04KV), and
  `ZInQ.HeightSplit.isStableFaltingsHeight_unique` (N1, SS2) makes the kernel height independent of the
  field. Status of the four inputs:
  * `AVGlue.GeomConnOfRationalPoint` is proved (`geomConnOfRationalPoint_proof`);
  * T35 comes from `uniformizationLeafAll_proof` and the textbook field `mumfordTorsionAlgClosed`;
  * N1 and SS2 are the bundle's fields.

  So the leaf's `∀ x, IsPrintedStableHeight (ofVendored V) x → …` asserts the bound only for the print's
  single value. (H3) is a fidelity lemma; the instance does not use it.

## 4. Rating of the new leaf

**`javanpeykarThm111`: printed form (my rating; LEAF if the reviewer agrees).** It is Thm 1.1.1 with
p. 9's identification. The constant `13·10⁶`, the exponent 5, the factor `g` and `g ≥ 1` are as printed,
and Faltings' normalization is that of height-fix's printed height, as recorded in locators.md row R18.
The hypotheses on `X` are those of the print or weaker. `deg_B` is the printed minimum, and "unramified"
is Mathlib's notion.

Two points are dictionary, not print, and a statement check should look at them:
* **The height of an abelian variety over `ℚ̄`.** `IsStableHeightBar` takes the height of a model over
  some number field. That this value does not depend on the model or the field is a published fact, but
  it is proved in Lean only for one abelian variety over one number field ((H2) and (H3)). Comparing
  models over different fields would need descent of an isomorphism from `ℚ̄` to a number field, which is
  not in Mathlib.
* **The degree** is taken over the stalk at `β(η)` rather than over `k(ℙ¹)`; see the table.

Kind `published`, flag `unread: new printed leaf …` in the spec. If Addendum 1 applies (new printed
leaves count as GLUE until a reviewer rates them, as for the current field), the integrator adds
`pending review` and GLUE does not drop until the review.

## 5. `#discharges`

VERIFIED. `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.JavanpeykarThm111` completed (14289 jobs; `scratch/javanpeykar-steps/build_out.txt`),
then `lake env lean scratch/javanpeykar-steps/Discharges.lean` (full output `discharges_out.txt`):

```
DISCHARGES [OpenResearchLeaves39.javanpeykarPrintedMapHF] by JavanpeykarSteps.javanpeykarPrintedMap_of_thm111
  still assumes: [JavanpeykarSteps.JavanpeykarThm111]
  axioms: [propext, Classical.choice, Quot.sound]
```

The fold dry run `python3 scripts/one_proof/autofold.py scratch/javanpeykar-steps/autofold.json --dry-run`
reports `strict count: 17/16 on 33 -> 18/15 on 33; strictest 17/16 -> 18/15`, i.e. GLUE 16 → 15 in both
columns. The generated module (`FoldDryRun.lean.txt`, first line stripped; renamed `.txt` so it does not
redeclare `HDec.HSyn` bundles in the tree) compiles, and `HDec.HSyn.sixContactMin_of_open57` depends on
`[propext, Classical.choice, Quot.sound]`.

## 6. What remains

* A statement check of `JavanpeykarThm111` against the print (arXiv v1 p. 1 and p. 9).
* Not attempted:
  * `W` unique up to isomorphism of abelian varieties. Yoneda gives the scheme isomorphism
    (`RepresentableBy.uniqueUpToIso`); the group compatibility is private in the vendored code;
  * independence of `IsStableHeightBar` across number fields.
