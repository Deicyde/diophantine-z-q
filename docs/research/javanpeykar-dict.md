# javanpeykar-dict: `javanpeykarBound` from two printed theorems

Task javanpeykar-dict (2026-11-16), base `origin/main` 2880fef1. Scratch: `scratch/javanpeykar-dict/`.
Lean: `ZInQKernel/Contrib/OneProof/JavanpeykarDict.lean` (top theorem) with helpers
`ZInQKernel/Contrib/OneProof/JavanpeykarDict/{Basic,BelyiAlgebra,FunctionField}.lean` (namespace
`JavanpeykarDict`).

## 1. Result

The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound` (`ZInQKernel/OneProof/H/TailY.lean`,
bundle `OpenResearchLeaves26`) is **proved, with only the standard axioms, from two theorems in printed form**:

```lean
theorem JavanpeykarDict.javanpeykarBound_of_printed_stichtenoth (hJ : JavanpeykarPrinted)
    (hS : ConstantFieldExtensionUnramified) : ZInQ.HeightSplit.JavanpeykarBound
```

* **`JavanpeykarDict.JavanpeykarPrinted`**: Javanpeykar, *Algebra Number Theory* 8 (2014), Thm 1.1.1, for
  `X = X₀ ×_K ℚ̄` in the print's own terms: `Jac(X)` as the degree-zero Picard scheme, `g` the genus of `X_ℚ̄`,
  a Belyi map of `X_ℚ̄` over `ℚ̄`. Rated **printed form** (§4).
* **`JavanpeykarDict.ConstantFieldExtensionUnramified`**: Stichtenoth, *Algebraic Function Fields and Codes*,
  Thm 3.6.3(a) (a constant field extension of an algebraic function field is unramified), in valuation-subring
  form. Rated **printed form**, theorem number UNVERIFIED (§5).

Of the three dictionary steps of the 11-16 pass, all are now proved in Lean:

| step | status |
|---|---|
| (1) kernel Jacobian (`IsJacobian`, Albanese predicate) vs the print's `Jac(X)` (Milne, *Jacobian varieties*, 6.1; base change) | **proved**: every kernel Jacobian is isomorphic to every tensor-compatible representative of `Pic⁰_{X/K}` (isj1-dict's proof, copied), and the published stable height is an isomorphism invariant (new: `isStableFaltingsHeight_of_iso`) |
| (2) `dim J = genus` (Milne 2.1) | **proved**: `dim J = dim_K H¹(X, 𝒪_X) = dim_ℚ̄ H¹(X_ℚ̄, 𝒪)` (`dim_eq_genusK`, `genusBar_eq`, from the vendored Jacobian-Challenge library) |
| (3) kernel `IsBelyiFunction` over `K` vs a Belyi map of `X` over `ℚ̄` | **restated and proved**: the leaf takes a Belyi function of `X_ℚ̄` over `ℚ̄`; the passage from `K` to `ℚ̄` (`BelyiBaseChange`) is proved from Stichtenoth's theorem: `ℚ̄(X_ℚ̄) = K(X) ⊗_K ℚ̄` (`functionField_baseChange`, new), degree and ramification under the constant field extension (`finrank_adjoin_eq`, `belyi_unram`, new) |

**Target "javanpeykarBound back to LEAF": met.** The fold replaces one field by two published-form leaves; the
strict GLUE count does not rise (autofold dry-run: strict `34/11 on 45 → 35/11 on 46`, strictest likewise), and
the generated module compiles with `sixContactMin_of_open36` on the standard axioms.

## 2. What compiles

All VERIFIED (compiled on this host, 2026-11-16):

* `lake build +ZInQKernel.Contrib.OneProof.JavanpeykarDict` (9818 jobs) and
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` (13699 jobs): success.
* `#discharges` (`scratch/javanpeykar-dict/Discharges.lean`, output `Discharges-output.txt`):

  ```
  DISCHARGES [OpenResearchLeaves26.javanpeykarBound] by JavanpeykarDict.javanpeykarBound_of_printed
    still assumes: [JavanpeykarDict.JavanpeykarPrinted, JavanpeykarDict.BelyiBaseChange]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenResearchLeaves26.javanpeykarBound] by JavanpeykarDict.javanpeykarBound_of_printed_stichtenoth
    still assumes: [JavanpeykarDict.JavanpeykarPrinted, JavanpeykarDict.ConstantFieldExtensionUnramified]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 56 open hypotheses, 2926 theorems checked, 9 discharge one
  ```
* Autofold spec `scratch/javanpeykar-dict/autofold.json` (proof `javanpeykarBound_of_printed_stichtenoth`, leaves
  `javanpeykarPrinted` and `constantFieldExtensionUnramified`, both kind `published`, flagged unread);
  `autofold.py --dry-run` output `FoldDryRun-output.txt`; the generated module (`FoldDryRun.lean`) compiles,
  `HDec.HSyn.sixContactMin_of_open36` on `[propext, Classical.choice, Quot.sound]` (`FoldDryRun-compile.txt`).
* No `sorry`, no `axiom`, no build-time code in the four Contrib files; nothing else under `ZInQKernel/` edited.

## 3. The Lean statements

Old field (verbatim copy: `scratch/javanpeykar-dict/Statement.lean.txt`): for `X/K` a curve (`IsCurve`,
integral) with a `K`-point `P₀`, `J : PkgI3.AbVar K` with `IsJacobian X P₀ J aj`, `J.dim = g ≥ 1`, `t ∈ K(X)`
with `IsBelyiFunction K K(X) t`, `d = [K(X) : K(t)] > 0`, and `IsStableFaltingsHeight J x`:
`x ≤ 13·10⁶ g d⁵`.

New leaf (`ZInQKernel/Contrib/OneProof/JavanpeykarDict/Basic.lean`):

```lean
def JavanpeykarPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    (V : AbelianVariety K) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
    PicardTensorCompatible X.hom V.group rep →
    1 ≤ genusBar X →
    ∀ [IsIntegral (baseChangeCurve X (AlgebraicClosure K)).left]
      (t : (baseChangeCurve X (AlgebraicClosure K)).left.functionField),
      letI := ffAlgebra (baseChangeCurve X (AlgebraicClosure K))
      IsBelyiFunction (AlgebraicClosure K) (baseChangeCurve X (AlgebraicClosure K)).left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin (AlgebraicClosure K) {t})
        (baseChangeCurve X (AlgebraicClosure K)).left.functionField = d → 0 < d →
      ∀ x : ℝ, IsStableFaltingsHeight (ofVendored V) x → x ≤ javanpeykarBound (genusBar X) d
```

* `baseChangeCurve X L = (Over.pullback (Spec L → Spec K)).obj X`, `genusBar X` the arithmetic genus
  `dim H¹(X_K̄, 𝒪)` of `X_K̄` (`K̄ = AlgebraicClosure K`; vendored `Scheme.arithmeticGenus`);
* `AbelianVariety`, `picardFunctorDegree`, `PicardTensorCompatible`: vendored Jacobian-Challenge library
  (`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/`), `ofVendored V` the same group scheme as a kernel
  `PkgI3.AbVar`;
* `IsBelyiFunction`, `ffAlgebra`, `javanpeykarBound`, `IsStableFaltingsHeight`: the kernel's, unchanged.

There is no base point (the print has none) and no kernel `IsJacobian`.

Intermediate statement (`BelyiBaseChange`, proved): for `X/K` a curve, integral, and `t ∈ K(X)` with
`IsBelyiFunction K K(X) t` and `[K(X) : K(t)] = d > 0`: `X_K̄` is integral and some `t' ∈ K̄(X_K̄)` has
`IsBelyiFunction K̄ K̄(X_K̄) t'` and `[K̄(X_K̄) : K̄(t')] = d`.

Second leaf (`JavanpeykarDict/BelyiAlgebra.lean`):

```lean
def ConstantFieldExtensionUnramified : Prop :=
  ∀ (K F L FL : Type) [Field K] [Field F] [Field L] [Field FL] [Algebra K F] [Algebra K L]
    [Algebra L FL] [Algebra K FL] [IsScalarTower K L FL] [CharZero K] [Algebra.IsAlgebraic K L]
    (ι : F →ₐ[K] FL),
    (∃ t : F, Transcendental K t ∧ FiniteDimensional (IntermediateField.adjoin K {t}) F) →
    Function.Bijective (Algebra.TensorProduct.productMap ι (IsScalarTower.toAlgHom K L FL)) →
    ∀ w : ValuationSubring FL, (∀ c : L, algebraMap L FL c ∈ w) → ∀ π : F,
      π ∈ (w.comap (ι : F →+* FL)).nonunits →
      (∀ x ∈ (w.comap (ι : F →+* FL)).nonunits, ∃ y ∈ w.comap (ι : F →+* FL), x = π * y) →
      ∀ x ∈ w.nonunits, ∃ y ∈ w, x = ι π * y
```

Proved glue (`JavanpeykarDict/{Basic,BelyiAlgebra,FunctionField}.lean`, top theorem in `JavanpeykarDict.lean`):

| theorem | content |
|---|---|
| `isStableFaltingsHeight_of_iso` | `e : J.X ≅ J'.X` a homomorphism, `IsStableFaltingsHeight J x → IsStableFaltingsHeight J' x` (Néron model `𝒩` of `J_L` becomes one of `J'_L` with `gen' = gen ≫ e_L`; same scheme, so same semistability and same metrized models, hence same height) |
| `abVarIso_picZero_of_isJacobian` | isj1-dict's: `IsJacobian X P₀ J aj` and `V` a tensor-compatible `Pic⁰_{X/K}` representative give `J ≅ ofVendored V` |
| `dim_eq_genusK` | `IsJacobian X P₀ J aj → J.dim = dim_K H¹(X, 𝒪_X)` |
| `genusBar_eq` | `dim_K̄ H¹(X_K̄, 𝒪) = dim_K H¹(X, 𝒪)` (vendored `arithmeticGenus_pullback`) |
| `javanpeykarBound_of_printed` | the old field from `JavanpeykarPrinted` and `BelyiBaseChange` |
| `functionField_baseChange` | `X` integral over `K`, `X_L` integral, `L/K` algebraic: `K(X) ⊗_K L → L(X_L)` is bijective (Mathlib `isIso_pushoutSection_of_isAffineOpen` on an affine open through the generic point, as in the vendored `free_finite_app`; then `productMap_bijective_of_fraction`: `Frac(A) ⊗_K L ≅ Frac(A ⊗_K L)` for `L/K` algebraic) |
| `finrank_adjoin_eq` | `F ⊗_K L ≅ FL`, `L/K` algebraic: a `K⟮t⟯`-basis of `F` is an `L⟮ι t⟯`-basis of `FL` (linear disjointness of `ι(F)` and `L`, every element of `L⟮ι t⟯` is `∑ ι(eⱼ) ℓⱼ`) |
| `belyi_unram`, `transcendental_ι`, `isBelyiFunction_baseChange` | the `K`-Belyi property gives the `L`-Belyi property: for `t − a ∈ 𝔪_w`, `p = minpoly_K a` gives `ι p(t) = (t − a)·u`, `u ∈ w`, so `p(t)` is a nonunit at `w ∩ F`, hence a uniformizer there, hence at `w` (the leaf), hence `t − a` is one |
| `belyiBaseChange_of_unramified` | `ConstantFieldExtensionUnramified → BelyiBaseChange` |
| `javanpeykarBound_of_printed_stichtenoth` | the old field from the two leaves |

## 4. Rating of the new leaf: printed form

`JavanpeykarPrinted` is Javanpeykar's Thm 1.1.1 (read by the locator audit: `h_Fal(X) ≤ 13·10⁶·g·deg_B(X)⁵` for
a smooth projective connected curve `X/ℚ̄` of genus `g ≥ 1`; `h_Fal(X)` the stable Faltings height of `Jac X`,
§2.3; `deg_B(X)` the least degree of a finite morphism `X → ℙ¹_ℚ̄` unramified outside three points) instantiated
at `X = X₀ ×_K ℚ̄`, with each object of the print read as follows (none is a structure invented for the purpose):

* **curve**: `X₀` smooth proper geometrically connected over `K` (proper curves are projective), so `X₀ ×_K ℚ̄`
  is a smooth projective connected curve over `ℚ̄ = AlgebraicClosure K` (an algebraic closure of `ℚ`). Every
  curve over `ℚ̄` is of this form; the leaf is the print restricted to them (a specialization).
* **genus**: `genusBar X₀ = dim H¹(X, 𝒪_X)`, the genus of the smooth projective curve `X` (computed over `ℚ̄`,
  not over `K`).
* **Jacobian**: `Jac(X)` is the degree-zero Picard scheme. The leaf takes `V/K` representing `Pic⁰_{X₀/K}` with
  the tensor-product group law; `V_ℚ̄` represents `Pic⁰_{X/ℚ̄}` (representability commutes with base change), so
  `V_ℚ̄ = Jac(X)`. The kernel's Albanese-property Jacobian is not used.
* **height**: `IsStableFaltingsHeight V x`, the published stable height of `V` (Néron model over a field of
  semistable reduction, Faltings' `(i/2)^g` normalization, as in Javanpeykar §2.1/§2.3 per the audit). The stable
  height of an abelian variety over `ℚ̄` is by definition that of a model over a number field, here `V`. The
  height must be read over `K`: the kernel's heights are defined over number fields only. The archimedean
  dictionary of `IsStableFaltingsHeight` (metrics from analytic uniformizations) is height-dict's subject, shared
  by every height leaf, and not changed here.
* **Belyi degree**: a Belyi function `t ∈ ℚ̄(X)` over `ℚ̄` (the kernel's `IsBelyiFunction` over the algebraically
  closed field `ℚ̄`: `t` transcendental, and ramification index `1` at every place of `ℚ̄(X)/ℚ̄` over a point
  `a ∈ 𝔸¹(ℚ̄) ∖ {0, 1}`, since the monic irreducible `q ≠ T, T − 1` over `ℚ̄` are the `T − a`), of degree
  `d = [ℚ̄(X) : ℚ̄(t)]`. The morphism `X → ℙ¹_ℚ̄` given by `t` is finite of degree `d` and unramified over
  `ℙ¹ ∖ {0, 1, ∞}`, a Belyi map, so `deg_B(X) ≤ d`; the bound `13·10⁶ g d⁵` is increasing in `d`.

Rating: **printed form**, flagged unread. The remaining readings are vocabulary, not mathematics: Belyi maps
in function-field form (the equivalence of smooth projective curves over `ℚ̄` with their function fields,
Hartshorne I.6, UNVERIFIED number), the Jacobian as `Pic⁰` over `K` (base change of the Picard functor), and
the stable height over `ℚ̄` read on a model. Not stronger than the print: each hypothesis implies the print's
(`deg_B ≤ d`, `g` and `h_Fal(X)` equal to the leaf's). Not vacuous: `V` exists for every curve
(`exists_abelianVariety_picardDegreeZero`), `X_ℚ̄` is integral, every curve over `ℚ̄` has a Belyi function
(Belyi), and `IsStableFaltingsHeight` is attained given the kernel's SS1/N1 leaves.

## 5. The second leaf `ConstantFieldExtensionUnramified`: printed form, number UNVERIFIED

Printed (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254 (2009), §3.6, Thm 3.6.3(a); the
number is from memory and was not read here, so UNVERIFIED): for an algebraic function field `F/K` and an
algebraic constant field extension `F' = FK'`, `F'/F` is unramified, `e(P'|P) = 1` for all places `P'|P`.

Reading in the leaf:
* `F/K` an algebraic function field: `F/K(t)` finite for a transcendental `t`; `char K = 0` (so `K` perfect and
  `K'/K` separable, the cases where the print applies without conditions);
* `F' = FK'`: a field `FL` with `F ⊗_K L → FL` bijective (`L/K` algebraic), i.e. `F' ≅ F ⊗_K L`, the compositum
  of `F` and `L` with `F`, `L` linearly disjoint;
* places of `F'` (over `K' = L`): valuation subrings `w ⊆ FL` containing `L`; `P = w ∩ F` (`w.comap ι`);
* `e(P'|P) = 1`: if `π` generates the maximal ideal of `P` then `ι π` generates that of `P'`
  (`v_{P'}(π) = e·v_P(π) = 1`; places of a function field of transcendence degree `1` are discrete valuation
  rings). For `w = FL` both maximal ideals are `0` and the statement is trivially true; `w ∩ F = F` forces
  `w = FL`.

Not stronger than the print (each hypothesis is one of the print's, `char 0` included), not vacuous (used at
`F = K(X)`, `L = K̄` for every curve `X/K`). If a reader wants the classical proof instead of the citation: the
integral closure of `P` in `F(α)` (`α ∈ L`) is `𝒪_P ⊗_K K(α)`, étale over `𝒪_P`, hence unramified.

Proposed `locators.md` rows (to be added by the integrator):
* *R18 printed: Javanpeykar 2014, Thm 1.1.1, p. 90 (arXiv:1403.6404v1 p. 1); §2.3 p. 98;
  `JavanpeykarDict.JavanpeykarPrinted`: printed form at `X = X₀ ×_K ℚ̄` (Jac = `Pic⁰`, Belyi map in
  function-field form); same source as R18.*
* *Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Thm 3.6.3(a) (constant field
  extensions are unramified); `JavanpeykarDict.ConstantFieldExtensionUnramified`; locator UNVERIFIED (not
  read).*

## 6. What remains

* Both leaves are flagged unread (no human reading). Stichtenoth's theorem number is UNVERIFIED.
* The archimedean dictionary of `IsStableFaltingsHeight` (metrics from analytic uniformizations against
  Javanpeykar's `(i/2)∫ω∧ω̄`) is not touched here; it is height-dict's subject and shared by every height leaf.
* `locators.md`, `kinds.tsv`, `OPEN.md` are not edited (rules); the rows above and the autofold spec are for the
  integrator.
