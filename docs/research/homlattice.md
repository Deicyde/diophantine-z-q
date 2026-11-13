# homlattice: `HomLatticeCorr` reduced to AN3 at every embedding and GAGA

Task homlattice, 2026-11-13.
- Lean: `scratch/homlattice/HomLattice.lean`, one file, namespace `ZInQ.HomLattice`. It imports
  `ZInQKernel.Contrib.HomUnify.Corr`, `ZInQKernel.HDecomp.LeafPush2.UnifBridge` and three Mathlib
  modules. Check it with `lake env lean scratch/homlattice/HomLattice.lean` after
  `lake build ZInQKernel.Contrib.HomUnify.Corr ZInQKernel.HDecomp.LeafPush2.UnifBridge`.
  Compile output: `scratch/homlattice/out_HomLattice.txt`.
- Results log: `scratch/homlattice/log.md`. Verbatim check of the one copied block:
  `scratch/homlattice/verbatim_check.py`.
- No existing file was edited.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference),
**SPECULATIVE**. Theorem numbers recalled without a source are **UNVERIFIED** (no network). This
is model work; there has been no human review.

## 0. Verdict and main result

1. **`HomLatticeCorr` is not a published theorem in this form.** It is true and no stronger than
   the literature, but it bundles four separate things:
   - two textbook facts:
     - **(a)** `A(ℂ)_σ ≅ ℂ^g/Λ` as complex Lie groups (Mumford §1 and §4);
     - **(b)** GAGA: holomorphic maps between proper `ℂ`-varieties are algebraic;
   - **(c)** "algebraic morphisms are holomorphic", which at the level of the project's
     definitions is a short scheme computation;
   - **(d)** the lifting argument of Birkenhake–Lange Prop. 1.2.1 (covering spaces plus
     holomorphy ⇒ `ℂ`-linear).

   It is also stated over leaf-push2's weak predicate `IsUniformization`. That predicate allows an
   arbitrary `Φ` (only a surjective analytic homomorphism with kernel `Λ`). Comparing such a `Φ`
   with the exponential map is glue, not literature.
   - (c) and (d) are proved here.
   - The comparison of a weak `Φ` with a strong uniformization is proved here.
   - Uniqueness was already proved by hom-unify.
2. **Main theorem (VERIFIED, compiled, standard axioms):**

   ```lean
   theorem ZInQ.HomLattice.homLatticeCorr_of_strong_gaga
       (HS : StrongUniformizationExists) (HG : GAGAMorphism) : HomLatticeCorr
   ```

   It therefore also gives `HomLinearLift`, which G10 needs over number fields, as well as
   `T11aHom` and `T11a_RiemannEnd`. The two hypotheses:
   - `StrongUniformizationExists` is AN3 at every field `K` and embedding `σ`. It is bp-analytic's
     leaf `UniformizationLeafAll` (in the build), copied field by field with `σ` added. It
     **implies** `UniformizationLeafAll` (`leafAll_of_strong`).
   - `GAGAMorphism` is GAGA for maps of complex abelian varieties.
3. **Over `ℂ` the only new input is GAGA (VERIFIED):**

   ```lean
   theorem t11a_riemannEnd_of_leaf_gaga (HL : UniformizationLeafAll) (HG : GAGAMorphism) :
       ZInQ.LeafPush2.T11a_RiemannEnd
   theorem t11aHom_of_leaf_gaga (HL : UniformizationLeafAll) (HG : GAGAMorphism) : T11aHom
   theorem homLinearLiftC_of_leaf (HL : UniformizationLeafAll) … -- HomLinearLift at K = ℂ, σ = id
   ```

   The lifting half of T11(a) (`∀ f, ∃ M`) needs **no new leaf**. It follows from the existing AN3
   leaf.
4. **Recommendation for the leaf list** (§5): replace two leaves by two others, so the count does
   not grow.
   - Replace bp-analytic's `UniformizationLeafAll` by `StrongUniformizationExists`, which implies
     it.
   - Replace leaf-push2's `T11a_RiemannEnd` (or hom-unify's proposed `HomLatticeCorr`) by
     `GAGAMorphism`.

## 1. Is it a published theorem? (literature check)

What the literature states (all STANDARD; every theorem number UNVERIFIED, recalled without
network access):

| statement | source | form in the source |
|---|---|---|
| a holomorphic homomorphism of complex tori `V/Λ → V'/Λ'` is induced by a unique `ℂ`-linear `F` with `F(Λ) ⊆ Λ'`, and every such `F` induces one | Birkenhake–Lange, *Complex Abelian Varieties* (2nd ed. 2004), §1.2, Prop. 1.2.1 and the definition of the analytic/rational representations following it; Mumford, *Abelian Varieties*, §1 | **analytic** tori; "homomorphism" means a holomorphic group homomorphism |
| a compact connected complex Lie group is a complex torus `ℂ^g/Λ` | Mumford §1 | analytic |
| for an abelian variety `A/ℂ`, `A(ℂ)` with its analytic structure is a compact connected complex Lie group | Mumford §4 (application); compactness and connectedness: SGA 1 XII 3.2, 2.4 (with 3.1) | algebraic → analytic |
| `X ↦ X^an` is fully faithful on proper `ℂ`-schemes: `Hom(X, Y) → Hom(X^an, Y^an)` is bijective for `X` proper (`Y` separated, of finite type) | Serre, GAGA, Ann. Inst. Fourier 6 (1956); SGA 1 XII Thm. 4.4 / Cor. 4.5; Mumford §3 (abelian varieties over `ℂ` = polarizable complex tori, fully faithfully) | algebraic ↔ analytic |
| a morphism of abelian varieties sending `0` to `0` is a homomorphism | Mumford §4, Cor. 1 (rigidity) | algebraic; **proved in Lean** by mul-rigidity |

Birkenhake–Lange's "abelian variety" is a complex torus that admits a positive line bundle (an
analytic object). Their Hom is analytic. Algebraicity comes from Chow's theorem or GAGA, cited in
their Ch. 4 (UNVERIFIED location).

**So `HomLatticeCorr` is not any one of these.**
- **Clause 1 (lifting, any `K`, `σ`)** composes three steps:
  - (c) `f : A → B` over `K` gives a holomorphic map on `(·)_σ(ℂ)`;
  - (a) both sides are tori;
  - (d) Prop. 1.2.1, the existence half.
- **Clause 2 (realization, over `ℂ`)** composes four steps:
  - Prop. 1.2.1, the trivial half: `M` induces a holomorphic homomorphism of the tori;
  - (a);
  - GAGA;
  - rigidity.
- **Both clauses** use leaf-push2's weak `IsUniformization`. That predicate does not say that
  `Φ` is the exponential map, or even that `Λ` is discrete. "Every weak `Φ` with `g = dim A` is
  `exp ∘ D` with `D` a linear isomorphism" is a further argument, which no source states for this
  predicate.

It is a correct consequence of the sources, and not stronger (hom-unify §3). But it is a
packaging, and two of its four pieces are provable glue.

## 2. The decomposition

| piece | content | status |
|---|---|---|
| `IsAnalyticHom σ ψ` | the hom/open/holomorphic clauses of `IsUniformization` (no kernel or surjectivity clause); `isUniformization_iff` | definition; proved equivalence |
| (c) algebraic ⇒ analytic | `isAnalyticHom_comp`: `Φ ≫ f` is analytic for `f` with `IsMonHom f` (`cEvalAt_comp`: evaluating `s` at `p ≫ f` = evaluating `f^*s` at `p`) | **proved** |
| lattice map ⇒ analytic | `isAnalyticHom_lin`: `Φ ∘ M` is analytic | **proved** |
| (d) lifting | `continuous_symm_comp_strong` (`φ⁻¹ ∘ ψ` is continuous, by clause (iii) of the strong uniformization); `exists_realLinear_of_continuous` (covering lift `ℂ^n → ℂ^{g'}`, then additive by connectedness); `exists_complexLinear_of_analytic_strong` (`ℂ`-linear: local coordinates (ii) and the inverse function theorem); adapted from bp-analytic's `continuous_comparison`, `exists_realLinear_lift`, `exists_complexLinear` | **proved** |
| weak `Φ` versus strong `φ` | `Φ = φ ∘ proj ∘ D` with `D` `ℂ`-linear and **onto** (`surjective_of_proj_comp_surjective`: `Λ'` discrete ⇒ countable, `ℂ` uncountable, so a proper subspace plus `Λ'` cannot cover); no dimension theory needed | **proved** |
| lifting half | `analyticHomLift_of_strong`: every analytic homomorphism `ψ : ℂ^g → B(ℂ)_σ` is `Φ_B ∘ M` (`M = S ∘ D_ψ`, `S` a right inverse of `D_Φ`); `homLinearLift_of_strong` | **proved** from `StrongUniformizationExists` |
| uniqueness in realization | hom-unify's `induces_unique` (`A` reduced, `ℂ`-points dense) | proved (hom-unify) |
| rigidity | `MulRigidity.isMonHom_of_geometricallyIntegral` (copied verbatim from scratch/alg-frob-red; mul-rigidity proved it from Mathlib); `eta_comp_of_one_comp` | **proved** |
| weak-source GAGA from strong-source GAGA | `analyticMapAlgebraic_of_gaga'`: `ψ` factors through `D` because `ker D ⊆ Λ_A` | **proved** |
| realization half | `homRealize_of_analyticHomAlgebraic`, `analyticHomAlgebraic_of_map` | **proved** from `GAGAMorphism` |
| (a) AN3 at every `σ` | `StrongUniformizationExists` | **leaf** (§3.1) |
| (b) GAGA | `GAGAMorphism` | **leaf** (§3.2) |

## 3. The two leaves

### 3.1 `StrongUniformizationExists` (AN3 at every embedding)

```lean
structure IsStrongUnif {K : Type} [Field K] (A : AbVar K) (σ : K →+* ℂ) {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (φ : Torus Λ ≃+ Additive (CPts A σ)) : Prop where
  holo : ∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
    IsOpen {v | ⊤ ≤ (Additive.toMul (φ (proj Λ v))).left ⁻¹ᵁ U} ∧
    AnalyticOnNhd ℂ (fun v => cEvalAt (Additive.toMul (φ (proj Λ v))) U f)
      {v | ⊤ ≤ (Additive.toMul (φ (proj Λ v))).left ⁻¹ᵁ U}
  coords : ∀ v₀, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U)) (e : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)),
    ⊤ ≤ (Additive.toMul (φ (proj Λ v₀))).left ⁻¹ᵁ U ∧
    HasFDerivAt (fun v i => cEvalAt (Additive.toMul (φ (proj Λ v))) U (f i)) (e : _ →L[ℂ] _) v₀
  open_map : ∀ v₀, ∀ N ∈ 𝓝 (proj Λ v₀), ∃ (U : A.X.left.Opens) (k : ℕ) (f : Fin k → Γ(A.X.left, U))
    (ε : ℝ), 0 < ε ∧ ⊤ ≤ (Additive.toMul (φ (proj Λ v₀))).left ⁻¹ᵁ U ∧
    ∀ P : CPts A σ, ⊤ ≤ P.left ⁻¹ᵁ U →
      (∀ i, ‖cEvalAt P U (f i) - cEvalAt (Additive.toMul (φ (proj Λ v₀))) U (f i)‖ < ε) →
      ∃ q ∈ N, Additive.toMul (φ q) = P

def StrongUniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (σ : K →+* ℂ),
    ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (φ : Torus Λ ≃+ Additive (CPts A σ)), IsStrongUnif A σ Λ φ
```

- **Definitions.** Every notion comes from the build: `PkgI3.AbVar`, leaf-push2's `CPts`,
  `cEvalAt`, bp-analytic's `Torus` and `proj`, and Mathlib's analysis. Nothing new is invented.
  `IsStrongUnif` is bp-analytic's `IsUniformization` field for field, with `CPts A σ`/`cEvalAt`
  in place of `A.Pt ℂ`/`evalAt`. At `σ = id` the two predicates are equivalent
  (`isStrongUnif_of_bp`, `bp_of_isStrongUnif`, VERIFIED). bp-analytic §4 reviewed that predicate
  (one model read-through: true for every `AbVar ℂ`, not vacuous).
- **Why it is true for general `σ`** (STANDARD argument; SPECULATIVE in the details). Let
  `A_σ = A ×_{K,σ} ℂ`. Then `A(ℂ)_σ = A_σ(ℂ)`, and (a) gives `A_σ^an ≅ ℂ^g/Λ`. The clauses only
  use regular functions on Zariski opens of `A` over `K`, which suffices for three reasons:
  - the coordinate ring of `U_σ` is `O(U) ⊗_{K,σ} ℂ`, generated by `O(U)`. So on `U_σ(ℂ) ⊂ ℂ^N`
    (coordinates from `K`-generators) the analytic topology and the holomorphic functions are
    detected by `O(U)`. This gives clauses (i) and (iii);
  - `Ω_{A_σ/ℂ}` is the pullback of `Ω_{A/K}`, and `Ω_{O(U)/K}` is generated by the `df` with
    `f ∈ O(U)`. So at every `P ∈ A_σ(ℂ)` some `g` functions `f_i ∈ O(U)` have independent
    differentials, and they are local coordinates by the inverse function theorem. This gives
    clause (ii). It holds even when `P` lies over a non-closed point of `A`, for example a
    transcendental point;
  - Mumford §1, §4; Serre GAGA §2; SGA 1 XII §1 (UNVERIFIED locators), as in bp-analytic.
- **Not stronger** than "AN3 for `A_σ`" (`A_σ^an` is a complex torus): every clause is a property
  of that torus structure, read through `K`-functions.
- **Implies the existing leaf:** `leafAll_of_strong` (VERIFIED). It also gives leaf-push2's weak
  uniformizations through `UnifBridge`'s argument. The identification `g = dim A` needed for
  leaf-push2's T35 `UniformizationExists` is not done here.

### 3.2 `GAGAMorphism` (GAGA for maps of complex abelian varieties)

```lean
def GAGAMorphism : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (φ : Torus Λ ≃+ Additive (CPts A (RingHom.id ℂ))), IsStrongUnif A (RingHom.id ℂ) Λ φ →
    ∀ ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ), IsAnalyticHom (RingHom.id ℂ) ψ →
      (∀ z ∈ Λ, ψ z = 1) →
      ∃ f : A.X ⟶ B.X, ∀ z, ψ z = Additive.toMul (φ (proj Λ z)) ≫ f
```

- **Meaning.** `φ` presents `A^an` as `ℂ^g/Λ`: clauses (i)-(iii) make `φ` a biholomorphism. A
  `ψ` that kills `Λ` is a holomorphic homomorphism `A^an → B^an`. The conclusion says it is
  algebraic. The conclusion asks only for a **morphism**: that `f` is a homomorphism is rigidity,
  which is proved.
- **Source.** GAGA: `Hom(A, B) → Hom(A^an, B^an)` is onto for `A` proper (Serre 1956; SGA 1 XII
  4.4; UNVERIFIED numbers). This is the narrow statement the task asked for ("every holomorphic
  homomorphism of complex tori that are abelian varieties is algebraic"), restricted further to
  homomorphisms. It is a consequence of the source and is no stronger.
  - No dimension hypothesis is needed.
  - The weak-source form `AnalyticMapAlgebraic` (over leaf-push2's `IsUniformization`, with
    `g = dim A`) is **derived** (`analyticMapAlgebraic_of_gaga'`).
- **Not vacuous.** Strong uniformizations exist by the AN3 leaf.
- Equivalent forms, all proved equivalent or implied:
  - `AnalyticMapAlgebraic ↔ AnalyticHomAlgebraic` (`analyticMapAlgebraic_iff`, by rigidity);
  - `AnalyticHomAlgebraic → HomRealize`;
  - `HomRealize → AnalyticHomAlgebraic`, given analytic lifting, T35 and finiteness of `dim`
    (`analyticHomAlgebraic_of_homRealize`).

  So the build's `ZInQ.HomUnify.HomRealize` (the realization half, existence only) has the same
  content. It could serve as the GAGA leaf in lattice form instead.

### 3.3 An alternative one-variety form of the lifting input (kept, superseded)

`UnifLocalInverse` says that a weak uniformization with `g = dim A` has a holomorphic local
inverse at `0` whose image is a neighbourhood of the identity. Since `A(ℂ)` has no topology in
Lean, the statement tests this on analytic homomorphisms. `analyticHomLift_of_unifLocalInverse`
derives the lifting half from it by pure analysis:
- `eq_fderiv_of_locally_additive`: a map `ℂ^g → ℂ^h` that is additive on a ball and
  `ℂ`-differentiable at `0` equals its derivative on the ball;
- `Λ ∩ W = 0` and the homomorphism property.

It is superseded by §3.1, whose predicate is already reviewed and in the build, and whose
test-map-free form is more natural.

## 4. Lean results (VERIFIED)

`lake env lean scratch/homlattice/HomLattice.lean` exits 0 in about 10 s. There are 45
`#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`. No `sorry` or `sorryAx`
appears (`out_HomLattice.txt`). The `MulRigidity` block (scratch/alg-frob-red/src_Rigidity.lean
lines 18-183) is verbatim (`verbatim_check.py`: OK).

Declarations, by role:

```lean
-- definitions
def IsAnalyticHom … ; structure IsStrongUnif … ; def StrongUniformizationExists
def GAGAMorphism ; def AnalyticMapAlgebraic ; def AnalyticHomAlgebraic ; def AnalyticHomLift
def AnalyticHomLiftC ; def UnifLocalInverse
-- glue
theorem isUniformization_iff ; theorem cEvalAt_comp ; theorem isAnalyticHom_comp
theorem isAnalyticHom_lin ; theorem eq_fderiv_of_locally_additive
theorem continuous_symm_comp ; theorem continuous_symm_comp_strong
theorem exists_realLinear_of_continuous
theorem exists_complexLinear_of_analytic ; theorem exists_complexLinear_of_analytic_strong
theorem surjective_of_proj_comp_surjective ; theorem eta_comp_of_one_comp
theorem isStrongUnif_of_bp ; theorem bp_of_isStrongUnif ; theorem strong_id_of_leaf
-- reductions
theorem homLinearLift_of_analyticHomLift ; theorem homRealize_of_analyticHomAlgebraic
theorem analyticHomLift_of_strong ; theorem homLinearLift_of_strong
theorem analyticHomLift_of_unifLocalInverse ; theorem analyticHomLiftC_of_leaf
theorem homLinearLiftC_of_leaf ; theorem analyticHomAlgebraic_of_map
theorem analyticMapAlgebraic_iff ; theorem analyticMapAlgebraic_of_gaga'
theorem analyticMapAlgebraic_of_gaga ; theorem analyticHomAlgebraic_of_homRealize
-- main
theorem homLatticeCorr_of_strong_gaga (HS : StrongUniformizationExists) (HG : GAGAMorphism) :
    HomLatticeCorr
theorem t11a_riemannEnd_of_strong_gaga ; theorem t11aHom_of_strong_gaga
theorem t11a_riemannEnd_of_leaf_gaga (HL : UniformizationLeafAll) (HG : GAGAMorphism) :
    ZInQ.LeafPush2.T11a_RiemannEnd
theorem t11aHom_of_leaf_gaga ; theorem leafAll_of_strong
-- older intermediate forms, also compiled
theorem homLatticeCorr_of_analytic ; homLatticeCorr_of_local ; homLatticeCorr_of_local_map
theorem homLatticeCorr_of_local_realize ; homLatticeCorr_of_strong_map
theorem t11a_riemannEnd_of_analytic ; t11a_riemannEnd_of_local ; t11a_riemannEnd_of_local_map
theorem t11a_riemannEnd_of_leaf_map ; t11aHom_of_analytic
```

## 5. Recommendation

- **Leaf list.**
  - (i) Replace bp-analytic's AN3 leaf `UniformizationLeafAll` by `StrongUniformizationExists`.
    The new leaf implies the old one, and it covers number fields, which G10's `HomLinearLift`
    needs.
  - (ii) Replace `T11a_RiemannEnd` (or hom-unify's `HomLatticeCorr`) by `GAGAMorphism`.
  - The number of leaves stays the same. `HomLatticeCorr`, `HomLinearLift`, `T11aHom` and
    `T11a_RiemannEnd` all become glue, proved above.
- **If only `ℂ` matters**, keep `UniformizationLeafAll` and add `GAGAMorphism`. This covers T11(a)
  and `T11aHom` (`t11a_riemannEnd_of_leaf_gaga`, `t11aHom_of_leaf_gaga`).
- **For the crowdsourcing announcement**, the two statements are:
  - `StrongUniformizationExists`: Mumford §1 plus analytification of a smooth proper variety. It
    needs `A^an` as a complex manifold, which Mathlib does not have.
  - `GAGAMorphism`: GAGA/Chow for morphisms. It needs analytification and Chow's theorem or GAGA,
    also absent from Mathlib (prereq-survey A9: "GAGA and Riemann's theorem not found").

## 6. What remains (unchecked or not done)

- All theorem numbers in §1 and §3 are UNVERIFIED (no network). This includes Birkenhake–Lange
  Prop. 1.2.1, Mumford §1/§3/§4 and §4 Cor. 1, SGA 1 XII 2.4/3.1/3.2/4.4/4.5, and Serre GAGA §2.
- The argument that `K`-regular functions suffice in clauses (ii) and (iii) for general `σ`
  (§3.1) is a model argument. One independent model read-through has checked it, with no human
  review. That read-through, run read-only on `StrongUniformizationExists`, `IsStrongUnif` and
  `GAGAMorphism`, found no problem:
  - both statements are true for every `K`, `A`, `σ`, including points over non-closed points of
    `A`;
  - the junk value of `cEvalAt` is never seen;
  - neither statement is vacuous;
  - no clause is stronger than the literature;
  - `GAGAMorphism` is weaker than GAGA plus rigidity.

  Its one wording remark: not every open of `A_σ` is a base change, but the base-changed affine
  cover suffices. The docstring was adjusted accordingly.
- The assembly was not rebuilt. hom-unify's `GluePieces3Hom` takes `homLinearLift : HomLinearLift`,
  and `homLinearLift_of_strong` supplies it, but this was not composed over the flat assembly.
  The step is a one-line composition.
- `StrongUniformizationExists → ZInQ.LeafPush2.UniformizationExists` (T35, which pins
  `g = dim A`) is not proved here. It needs dimension theory: the analytic dimension `g` equals
  the Krull dimension.
