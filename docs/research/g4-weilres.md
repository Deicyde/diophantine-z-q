# g4-weilres: glue step G4 (Weil restriction and the Hom field)

## Main result

**G4 is proved in Lean, down to three named analytic or geometric inputs and G2's output**
(`scratch/g4-weilres/G4.lean`, 1184 lines, no `sorry`; every main theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`, VERIFIED by `#print axioms`). The one leaf used is the
existing `PkgI3.HomFreeFinite` (Mumford, *Abelian varieties*, §19 Thm 3; locator UNVERIFIED).

What is proved:

- **The Weil-restriction step, as the argument uses it, is constructed.** For a model
  `A : PkgI3.AbVar K` over a finite Galois `K ⊆ ℚ̄`:
  - the `[K:ℚ]` conjugates `A_e = A ×_{K,e} ℚ̄` (one per embedding `e : K → ℚ̄`);
  - their pullback squares over `Spec σ`;
  - an honest group action `conjAction K A : G_ℚ →* Aut_ℤ(⊕_{e,e'} Hom(A_e, A_{e'}))`. This is
    the conjugation of homomorphisms, the `G_ℚ`-module `End(Res_{K/ℚ}A ⊗ ℚ̄)` of N5 L545-547.
  - Its key lemma, that the conjugate of a homomorphism is a homomorphism, is proved from
    Mathlib's monoidal structure on `Over.pullback`. The action is the unique one with the
    conjugation property (`isConjAction_unique`).
  - No Weil restriction of schemes is needed (Mathlib has none). The manuscript uses `W₀` only
    through this lattice.
- **The Hom field.** If this action is continuous and inertia outside `T` acts trivially, then
  there is `L ⊇ K` such that:
  - `L` is finite Galois;
  - `[L:ℚ] ≤ D = ZInQ.heightD`;
  - every geometric homomorphism among the conjugates is fixed by `G_L`;
  - `L` is unramified outside `T`, in both the Galois form and glue-descent's `UnramifiedAt` form.

  This is `homField_of_model`. Its proof uses Minkowski, Mathlib's infinite Galois theory, and a
  new bridge between the two forms of unramifiedness.
- **The consumers.** G4's output plugs into `GlueDescent.B3Q.b3_degree_le_QM`, which is what G7
  calls (`b3_of_homField`), and into `GlueAssembly.CMOutput`'s `d` (`cm_degree_of_homField`).

What remains (§3):

- **`hcont`**: continuity of the action. It follows from the limit theorem EGA IV₃ 8.8.2; leaf
  candidate, and the derivation is glue.
- **`hinert`**: trivial inertia on the lattice outside `T`. Its algebraic half
  (`inertia_of_tate`, `tateLattice_injective`, from `HomFreeFinite`) is proved. What is missing is
  the Galois action on the Tate modules of the conjugates and its equivariance; the input there is
  Néron–Ogg–Shafarevich.
- **`hdim`**: the dimension of a base change.
- **`hK`**: `K` unramified outside `T`. This is G2's output.

## 1. What G4 must deliver (VERIFIED by reading the consumers)

The manuscript's step is N5 L544-563, VERIFIED by reading `diophantine_zq.tex` L544-563. Its output
goes to two places.

- **G7, B3**: `GlueDescent.B3Q.b3_degree_le_QM` (`ZInQKernel/HDecomp/Descent/B3Assembly.lean`)
  takes:
  - `L : IntermediateField ℚ (AlgebraicClosure ℚ)` with `[FiniteDimensional ℚ L] [IsGalois ℚ L]`;
  - `finrank ℚ L ≤ heightD`;
  - `∀ p : Nat.Primes, p ∉ ramSet S u → UnramifiedAt L p`;
  - `ε` with `InflatedFrom L ε`. This last input is G7's instantiation: the descent data `μ_σ`
    lie in the lattice, so a field that defines the lattice defines `ε`. It stays a hypothesis
    of `b3_of_homField`.
- **The CM branch**: `GlueAssembly.CMOutput` takes a real `d` with `1 ≤ d ≤ heightD`.

## 2. What compiles (`scratch/g4-weilres/G4.lean`)

### 2.1 Generic: conjugating homomorphisms of base-changed monoid objects (namespace `G4Conj`)

This works in any category with pullbacks. For a monoid object `X` over `S` and base changes
along `f₁, f₂ : T → S` with `f₂ = s ≫ f₁`:

| Declaration | Content |
| --- | --- |
| `mul_left_fst`, `one_left_fst` | the multiplication and unit of a base change `X ×_{S,f} T`, followed by the projection to `X` (from Mathlib's `Over.μ_pullback_left_*`, `ε_pullback_left`) |
| `cmp`, `cmp_isPullback` | the comparison `X ×_{f₂} T → X ×_{f₁} T` over `s`, and the fact that its square is a pullback |
| `cmp_mul`, `cmp_one` | **the comparison respects multiplication and unit** |
| `conj`, `conj_cmp`, `conj_unique` | the conjugate `σφ : X_{f₂} → Y_{g₂}` of `φ : X_{f₁} → Y_{g₁}`, characterized by `σφ ∘ cmp = cmp ∘ φ` |
| `conj_isMonHom` | **the conjugate of a monoid homomorphism is a monoid homomorphism** |
| `conj_mul`, `conj_one` | conjugation is multiplicative for the pointwise group law on `Hom` |
| `conj_congr`, `conj_self`, `conj_comp` | conjugation is functorial in `s` |

### 2.2 The Hom field (namespace `G4WeilRes`)

| Declaration | Content |
| --- | --- |
| `exists_liesOver` | there is a place of `ℚ̄` over every prime |
| `exists_inertia_restrict` | an automorphism that is trivial modulo `w` on the integers of a finite Galois `L` agrees on `L` with an element of `I_w` |
| `unramifiedAt_of_inertia_le`, `galUnramifiedOutside_iff` | **bridge**: `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` for finite Galois `L` |
| `toGL`, `toGL_injective` | `Aut_ℤ(M) ↪ GL_r(ℤ)` |
| `homField_core` | **core**: an action of `G_ℚ` on a free `ℤ`-module of rank `r` that is continuous and trivial on inertia outside `T` has a Hom field `L ⊇ K` with `[L:ℚ] ≤ [K:ℚ]·3^{r²}`, unramified outside `T` |
| `homField_le_heightD` | with `[K:ℚ] ≤ F₀` and `r ≤ 16F₀²`: `[L:ℚ] ≤ D` |
| `pi_rank_le`, `HomLattice`, `homLattice_free` | `⊕ Hom(A_i, A_j)` is free of rank `≤ 16·n²` for surfaces (leaf `HomFreeFinite`) |
| `tateHom_injective`, `tateLattice`, `tateLattice_injective` | the `ℓ`-adic realization of the lattice is injective (from `HomFreeFinite` and flatness) |
| `trivial_of_faithful`, `inertia_of_tate` | inertia acting trivially on the realization ⇒ `hinert` (given an equivariant action on the realization) |
| `homField_of_conjugates` | G4 for any finite family of surfaces over `ℚ̄` with an action on its lattice |
| `specGal_mul`, `specGal_one` | `Spec` of Galois elements composes |
| `ConjData`, `IsConjAction`, `isConjAction_unique` | conjugation data (pullback squares `A_i → A_{σ⁻¹i}` over `Spec σ`) and the unique conjugation action |
| `bcAlong`, `embAct`, `specEmb_act`, `specEmb_symm`, `conjData` | **the conjugates of a model `A/K`**, constructed |
| `card_conjugates` | there are `[K:ℚ]` of them |
| `conjHom`, `conjAct`, `conjAct_one`, `conjAct_mul`, `conjAct_isConjAction` | conjugation on each Hom group and on the lattice; the group law |
| `conjAction`, `conjActionExists` | **the conjugation action `G_ℚ →* Aut_ℤ(lattice)` exists** |
| `homField_of_model` | **G4 for a model `A/K`**, with `ρ = conjAction K A` |
| `b3_of_homField` | G4's `L` with `T = ramSet S u` fed into `b3_degree_le_QM` |
| `cm_degree_of_homField` | `1 ≤ [L:ℚ] ≤ D` as reals |

**Proof of the core.**

1. `ker ρ` is open, as a finite intersection of the stabilizers of a basis.
2. `E = fixedField(ker ρ)` is finite Galois (`InfiniteGalois.fixingSubgroup_fixedField`,
   `isOpen_iff_finite`, `normal_iff_isGalois`).
3. `[E:ℚ] = |G_ℚ/ker ρ| = |ρ(G_ℚ)| ≤ 3^{r²}`. The last step is Minkowski,
   `GlueRepo.TorsionFree.card_le_three_pow`, through `toGL`.
4. Take `L = E ⊔ K`, with `[L:ℚ] ≤ [E:ℚ][K:ℚ]`.
5. Inertia at `p ∉ T` lies in `G_E ∩ G_K = G_L`, and the bridge turns this into `UnramifiedAt`.

**Proof of the bridge.**

1. Lift `g ∈ I(P|p) ≤ Gal(L/ℚ)` to `σ ∈ G_ℚ`.
2. Make `σ` an element of `I_w` that agrees with it on `L`. This uses Mathlib's profinite
   transitivity and `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, over the algebraic
   integers fixed by `G_L`, following glue-b3b's `exists_inertia_neg` and glue-conj's
   `mem_inertia_of_center`.
3. The hypothesis forces `g = 1`.
4. Hence `e = |I(P|p)| = 1` (Mathlib's `card_inertia_eq_ramificationIdxIn`).

**Proof of the group law.** It follows from `conj_comp` and `conj_self`. The index identities
`(στ)⁻¹∘e = τ⁻¹∘(σ⁻¹∘e)` and `1⁻¹∘e = e` hold definitionally (VERIFIED by `rfl`), so no
transport along index equalities is needed.

Compile:

1. `lake build ZInQKernel.HDecomp.B3Unram.B3b ZInQKernel.HDecomp.Repo.TorsionFree
   ZInQKernel.HDecomp.Repo.Numerics ZInQKernel.HDecomp.Descent.B3Assembly ZInQKernel.HDecomp.Objects`
2. `lake env lean scratch/g4-weilres/G4.lean`

The file takes 15-40 s to check, VERIFIED.

## 3. What remains (the hypotheses of `homField_of_model`)

1. **`hcont`**: every element of the lattice has an open stabilizer under `conjAction K A`.
   - Input: every homomorphism `A_e → A_{e'}` over `ℚ̄` is the base change of one over a number
     field. This is the limit theorem for morphisms of finitely presented schemes, EGA IV₃ 8.8.2
     (locator UNVERIFIED), a leaf candidate.
   - Glue: conjugation by `σ ∈ G_L` fixes a morphism defined over `L`. This is `conj_unique`
     applied to the pasted squares `ℚ̄ → L → K`, plus transport of the index along `σ∘e = e`
     for `σ ∈ G_K`.
   - Not formalized. Estimated 200-400 lines (SPECULATIVE).
2. **`hinert`**: for `p ∉ T` and `s ∈ I_w`, `conjAction K A s = 1`. The route:
   - `s ∈ G_K`, since `K` is unramified outside `T`. So `s` fixes the embeddings.
   - `s` acts trivially on `T_ℓ` of every conjugate, by Néron–Ogg–Shafarevich. This is the leaf
     `PkgI2.NeronOggShafarevich` with `PkgI2.inertiaTrivial_of_goodReduction`, applied to the good
     reduction of the conjugates at primes over `p`, which is G3's output.
   - `inertia_of_tate` (proved) carries this to the lattice. It needs the conjugation action on
     the Tate modules of the conjugates and the equivariance of `tateLattice`; neither is
     formalized. The action on points comes from the same `cmp` squares, through lifts of
     `Spec ℚ̄`-points, and its additivity follows from `cmp_mul`. The Tate modules in
     `PkgI3.AbVar.T` are taken over `AlgebraicClosure (AlgebraicClosure ℚ)` for a variety over
     `ℚ̄`, which complicates the comparison with `A/K`.
3. **`hdim`**: `dim(A ×_{K,e} ℚ̄) = 2` when `dim A = 2`. This is invariance of dimension under
   field extension: STANDARD and missing from Mathlib. leaf-qm-fp's `IsBaseChangeOf` notes the
   same gap.
4. **`hK`**: `K` unramified outside `T`. This is G2's output, already open there. Either form
   works, by `galUnramifiedOutside_iff`.
5. On G7's side, outside G4: `hdesc` in `b3_of_homField`, which says that `ε` is inflated from
   any field that defines the lattice. This is G7's instantiation.

## 4. Suggested update of h-decomposition §3, row G4 (for the integrator)

> G4: **proved** modulo continuity, inertia and the dimension of base change.
>
> - The conjugates of `A/K` and the conjugation action of `G_ℚ` on their Hom lattice (the
>   endomorphism lattice of `Res_{K/ℚ}A`) are constructed (`G4WeilRes.conjData`, `conjAction`;
>   generic lemmas `G4Conj.conj_isMonHom`, `cmp_mul`). No Weil restriction of schemes is needed.
> - The Hom field: `homField_core` (Minkowski + infinite Galois theory) and `homField_of_model`,
>   with leaf `HomFreeFinite`.
> - The output feeds `b3_degree_le_QM` (`b3_of_homField`) and `CMOutput`
>   (`cm_degree_of_homField`).
> - New bridge: `galUnramifiedOutside_iff`.
> - Open: `hcont` (EGA IV 8.8.2 + glue), `hinert` (NOS + the action on Tate modules; the
>   algebraic half `inertia_of_tate` is proved), `hdim`, and G2's `hK` (g4-weilres).

## 5. Labels

- VERIFIED (compiled): every declaration in §2, and their axiom lists.
- VERIFIED (read): N5 L544-563, and the consumers' signatures (`B3Assembly.lean`,
  `B2Glue.lean`, `GlueAssembly` in `scratch/h-decomposition/Leaves.lean`).
- STANDARD, not formalized: items 1-3 of §3.
- UNVERIFIED locators: Mumford §19 Thm 3; Serre–Tate 1968 Thm 1; EGA IV₃ 8.8.2.
