# g4-weilres: glue step G4 (Weil restriction and the Hom field)

## Main result

**G4 is proved in Lean from three named inputs, plus the outputs of G2 and G3 and one missing
Mathlib fact (dimension of a base change).** File: `scratch/g4-weilres/G4.lean`, 1447 lines, no
`sorry`. All 19 printed theorems depend only on `propext`, `Classical.choice`, `Quot.sound`
(VERIFIED by `#print axioms`).

The headline is `G4WeilRes.homField_of_model_leaves`.

Inputs (`def … : Prop`):

- `PkgI3.HomFreeFinite`: an existing leaf, Mumford, *Abelian varieties*, §19 Thm 3.
- `MorphismsDescend`: EGA IV₃ 8.8.2(i) for `ℚ̄ = colim L`. A leaf candidate stated in EGA's own
  form.
- `InertiaFixesHoms`: Serre–Tate 1968 Thm 1 with Mumford §19 Thm 3. The equivariance step of
  its derivation is glue that is not formalized; see §3.

Hypotheses from other glue steps:

- `hK`: `K` unramified outside `T`, in the Galois form. This is G2's output.
- `hgood`: the model `A/K` has good reduction at every place over every `p ∉ T`. This is G3's
  output.
- `hdim`: the conjugates are surfaces, i.e. `dim(A ×_{K,e} ℚ̄) = 2`. STANDARD, missing from
  Mathlib.

Setting: `K ⊆ ℚ̄` finite Galois with `[K:ℚ] ≤ F₀ = 324!`, and `A : PkgI3.AbVar K`.

Conclusion: there is `L ⊇ K` such that:

- `L` is finite Galois;
- `[L:ℚ] ≤ D = ZInQ.heightD`;
- `G_L` fixes every homomorphism between conjugates of `A` over `ℚ̄`. Precisely,
  `conjAction K A σ = 1` for `σ ∈ G_L`, where `conjAction` is the conjugation action, constructed
  below;
- `L` is unramified outside `T`, in both the Galois form and glue-descent's `UnramifiedAt`. The
  latter is the form G7's `GlueDescent.B3Q.b3_degree_le_QM` takes.

`b3_of_homField` feeds the output into G7's consumer, and `cm_degree_of_homField` into the CM
branch's `d ≤ D`.

**The Weil-restriction step is constructed, not assumed.**

- The conjugates `A_e = A ×_{K,e} ℚ̄` are constructed, one per embedding `e : K → ℚ̄`, with their
  pullback squares over `Spec σ` (`conjData`).
- The action `conjAction K A : G_ℚ →* Aut_ℤ(⊕_{e,e'} Hom(A_e, A_{e'}))` is constructed and is a
  group homomorphism (`conjActionExists`). This lattice with its action is `End(Res_{K/ℚ}A ⊗ ℚ̄)`,
  N5 L545-547, which is all the manuscript uses of the Weil restriction. Mathlib has no Weil
  restriction of schemes, and none is needed.
- The key generic lemma is that the conjugate of a homomorphism of base-changed group objects is
  a homomorphism: `G4Conj.conj_isMonHom`, through `cmp_mul`, `cmp_one`, from Mathlib's monoidal
  `Over.pullback`.
- The action is the unique conjugation action (`isConjAction_unique`).

## 1. What G4 must deliver (VERIFIED by reading the consumers)

The manuscript's step is N5 L544-563, VERIFIED by reading `diophantine_zq.tex` L544-563.

- **G7, B3**: `GlueDescent.B3Q.b3_degree_le_QM` (`ZInQKernel/HDecomp/Descent/B3Assembly.lean`)
  takes:
  - `L : IntermediateField ℚ (AlgebraicClosure ℚ)` with `[FiniteDimensional ℚ L] [IsGalois ℚ L]`;
  - `finrank ℚ L ≤ heightD`;
  - `∀ p : Nat.Primes, p ∉ ramSet S u → UnramifiedAt L p`;
  - `ε` with `InflatedFrom L ε`. This last input is G7's instantiation: the descent data `μ_σ`
    lie in the lattice, and `G_L` fixes the lattice. It stays the hypothesis `hdesc` of
    `b3_of_homField`.
- **The CM branch**: `GlueAssembly.CMOutput` takes a real `d` with `1 ≤ d ≤ heightD`.

## 2. What compiles (`scratch/g4-weilres/G4.lean`)

### 2.1 Generic: conjugating homomorphisms of base-changed monoid objects (namespace `G4Conj`)

This works in any category with pullbacks. For `X` over `S` and base changes along
`f₁, f₂ : T → S` with `f₂ = s ≫ f₁`:

| Declaration | Content |
| --- | --- |
| `mul_left_fst`, `one_left_fst` | the multiplication and unit of `X ×_{S,f} T`, then the projection to `X` (Mathlib's `Over.μ_pullback_left_*`, `ε_pullback_left`) |
| `cmp`, `cmp_isPullback` | the comparison `X ×_{f₂} T → X ×_{f₁} T` over `s`, and its square, a pullback |
| `cmp_mul`, `cmp_one` | the comparison respects multiplication and unit |
| `conj`, `conj_cmp`, `conj_unique` | the conjugate `σφ` of `φ : X_{f₁} → Y_{g₁}`, characterized by `σφ ∘ cmp = cmp ∘ φ` |
| `conj_isMonHom` | **the conjugate of a monoid homomorphism is a monoid homomorphism** |
| `conj_mul`, `conj_one` | conjugation is multiplicative for the group law on `Hom` |
| `conj_congr`, `conj_self`, `conj_comp` | conjugation is functorial in `s` |

### 2.2 The Hom field (namespace `G4WeilRes`)

| Declaration | Content |
| --- | --- |
| `exists_liesOver`, `exists_inertia_restrict` | places over `p`; lifting a residually trivial automorphism of a finite Galois `L` into some `I_w` |
| `unramifiedAt_of_inertia_le`, `galUnramifiedOutside_iff` | **bridge**: `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` for finite Galois `L`. New; usable also for G7's `L'` and G11 |
| `toGL`, `toGL_injective`, `homField_core` | **core**: a continuous action of `G_ℚ` on a free `ℤ`-module of rank `r`, trivial on inertia outside `T`, has a Hom field `L ⊇ K` with `[L:ℚ] ≤ [K:ℚ]·3^{r²}`, unramified outside `T` (Minkowski + infinite Galois theory + bridge) |
| `homField_le_heightD` | with `[K:ℚ] ≤ F₀` and `r ≤ 16F₀²`: `[L:ℚ] ≤ D` |
| `pi_rank_le`, `HomLattice`, `homLattice_free` | the lattice is free of rank `≤ 16n²` for surfaces (`HomFreeFinite`) |
| `tateHom_injective`, `tateLattice_injective`, `trivial_of_faithful`, `inertia_of_tate` | the `ℓ`-adic realization of the lattice is faithful; an equivariant realization with trivial inertia gives `hinert` |
| `homField_of_conjugates` | G4 for any finite family of surfaces over `ℚ̄` with an action |
| `ConjData`, `IsConjAction`, `isConjAction_unique`, `ConjActionExists` | conjugation data and the unique conjugation action |
| `bcAlong`, `embAct`, `specEmb_act`, `specEmb_symm`, `conjData`, `card_conjugates` | **the `[K:ℚ]` conjugates of a model `A/K`**, constructed |
| `conjHom`, `conjAct`, `conjAct_one`, `conjAct_mul`, `conjAction`, `conjActionExists` | **the conjugation action, constructed** |
| `homField_of_model` | G4 for `A/K` with continuity and inertia as hypotheses |
| `HomDescends`, `stabSub`, `embAct_symm_of_mem`, `conjAction_continuous` | continuity from "every morphism is fixed by an open subgroup" |
| `specIncl`, `specEmb_factor`, `cmpL`, `MorphismsDescend`, `specGal_specIncl`, `homDescends_of_morphismsDescend` | **continuity from EGA IV₃ 8.8.2**: the descent bookkeeping is proved |
| `homField_of_model'`, `homField_of_model_final` | intermediate forms |
| `InertiaFixesHoms`, `conjAction_inertia` | **the inertia hypothesis from good reduction** (with `hK` and `hgood`) |
| `homField_of_model_leaves` | **G4, headline form** |
| `b3_of_homField`, `cm_degree_of_homField` | the consumers |

Proof sketches.

- **Core.**
  1. `ker ρ` is open, as a finite intersection of the stabilizers of a basis.
  2. `E = fixedField(ker ρ)` is finite Galois (`InfiniteGalois.*`).
  3. `[E:ℚ] = |ρ(G_ℚ)| ≤ 3^{r²}` (Minkowski, `GlueRepo.TorsionFree.card_le_three_pow`).
  4. Take `L = E ⊔ K`. Inertia lies in `G_E ∩ G_K = G_L`.
- **Bridge.**
  1. Lift `g ∈ I(P|p)` to `σ ∈ G_ℚ`.
  2. Correct it into some `I_w`, using Mathlib's profinite transitivity and
     `stabilizerHom_surjective_of_profinite` over the algebraic integers fixed by `G_L`
     (following glue-b3b, glue-conj).
  3. The hypothesis then gives `g = 1`, so `e = |I(P|p)| = 1`.
- **Group law.** It follows from `conj_comp` and `conj_self`. The index identities
  `(στ)⁻¹∘e = τ⁻¹∘σ⁻¹∘e` and `1⁻¹∘e = e` hold by `rfl` (VERIFIED).
- **Continuity.**
  - `MorphismsDescend` gives `ψ` over a number field `L` with `φ ∘ cmpL = cmpL ∘ ψ`.
  - For `σ ∈ G_L` one has `Spec σ ≫ (Spec ℚ̄ → Spec L) = (Spec ℚ̄ → Spec L)`, so
    `cmp_σ ∘ cmpL = cmpL`. Then `conj_unique` gives `conj_σ φ = φ`.
  - Indices are transported along `σ⁻¹∘e = e` for `σ ∈ G_K` by `subst`.
- **Inertia.**
  - `s ∈ I_w` with `p ∉ T` lies in `G_K` by `hK`. So `s` fixes the embeddings.
  - Then apply `InertiaFixesHoms` to each component, with good reduction at `w ∩ e(K)` from
    `hgood`.

Compile:

1. `lake build ZInQKernel.HDecomp.B3Unram.B3b ZInQKernel.HDecomp.Repo.TorsionFree
   ZInQKernel.HDecomp.Repo.Numerics ZInQKernel.HDecomp.Descent.B3Assembly ZInQKernel.HDecomp.Objects`
2. `lake env lean scratch/g4-weilres/G4.lean`

The file takes about 40 s to check, VERIFIED.

## 3. What remains

1. **`MorphismsDescend`**. This is a leaf candidate: EGA IV₃ 8.8.2(i), the surjectivity part, for
   the filtered colimit `ℚ̄ = colim L` over the number fields `L ⊆ ℚ̄` (locator UNVERIFIED).
   - The hypotheses hold for abelian varieties: the source is qcqs (proper) and the target is
     locally of finite presentation (smooth).
   - The Lean form says that `φ` is the base change of some `ψ` over `L`, expressed through the
     cartesian squares `cmpL`. This is the published statement's content, not a strengthening.
2. **`InertiaFixesHoms`**. Fix a place `w` where `A` (at `w ∩ e₁(K)`) and `B` (at `w ∩ e₂(K)`)
   have good reduction. The input says that inertia at `w` fixes every `A_{e₁} → B_{e₂}` under
   conjugation.
   - It is a consequence of Néron–Ogg–Shafarevich (Serre–Tate 1968 Thm 1, the leaf
     `PkgI2.NeronOggShafarevich`), which makes inertia trivial on `T_ℓ` for `ℓ ≠ p`, and of the
     faithfulness of `T_ℓ` (`tateHom_injective`, proved from `HomFreeFinite`).
   - What links the two is the equivariance of the `ℓ`-adic realization under conjugation. That
     link is glue, **not formalized**. It needs the action of `G_ℚ` on the points of the
     conjugates; the `cmp` squares give it by lifting `Spec ℚ̄`-points, and `cmp_mul` gives
     additivity.
   - The Tate modules of `PkgI3.AbVar.T` for a variety over `ℚ̄` are taken over
     `AlgebraicClosure (AlgebraicClosure ℚ)`, which complicates the comparison with
     `NeronOggShafarevich` for the model over `K`.
   - The input is not a published statement verbatim. Treat it as a glue target with published
     ingredients, not as a leaf. Estimated 0.5-1k lines (SPECULATIVE).
3. **`hdim`**: `dim(A ×_{K,e} ℚ̄) = dim A`. Dimension is invariant under field extension: STANDARD,
   not in Mathlib. leaf-qm-fp's `IsBaseChangeOf` notes the same gap.
4. **`hK`** (G2's output, open there) and **`hgood`** (G3's output: leaf-qm-fp's
   `LeafQM.AV.QML3.goodReduction` gives it on its objects, and the instantiation on the actual
   `A` is open).
5. On G7's side, outside G4: `hdesc` in `b3_of_homField`.

## 4. Suggested update of h-decomposition §3, row G4 (for the integrator)

> G4: **proved** from `HomFreeFinite`, `MorphismsDescend` (EGA IV₃ 8.8.2) and `InertiaFixesHoms`
> (NOS + Mumford + equivariance glue, not formalized), with G2's `hK`, G3's `hgood`, and `hdim`
> (missing from Mathlib): `G4WeilRes.homField_of_model_leaves`.
>
> - The conjugates of `A/K` and the conjugation action of `G_ℚ` on their Hom lattice (the
>   endomorphism lattice of `Res_{K/ℚ}A`) are constructed: `conjData`, `conjAction`, with
>   `G4Conj.conj_isMonHom`. No Weil restriction of schemes is needed.
> - The Hom field: `homField_core` (Minkowski + infinite Galois theory).
> - New bridge: `galUnramifiedOutside_iff`.
> - The output feeds `b3_degree_le_QM` (`b3_of_homField`) and `CMOutput`
>   (`cm_degree_of_homField`) (g4-weilres).

## 5. Labels

- VERIFIED (compiled): every declaration in §2, and their axiom lists.
- VERIFIED (read): N5 L544-563, and the consumers' signatures (`B3Assembly.lean`,
  `B2Glue.lean`, `GlueAssembly` in `scratch/h-decomposition/Leaves.lean`).
- STANDARD, not formalized: §3 items 2 (equivariance) and 3.
- UNVERIFIED locators: Mumford §19 Thm 3; Serre–Tate 1968 Thm 1; EGA IV₃ 8.8.2.
