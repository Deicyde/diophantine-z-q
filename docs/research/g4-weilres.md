# g4-weilres: glue step G4 (Weil restriction and the Hom field)

## Main result

**G4's arithmetic and Galois-theoretic content is proved in Lean** (`scratch/g4-weilres/G4.lean`,
760 lines, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` for every main theorem,
VERIFIED by `#print axioms`). In particular, the Hom field reaches the consumer that G7 actually
calls, `GlueDescent.B3Q.b3_degree_le_QM`, in exactly the form that consumer requires. The one
leaf used is the existing `PkgI3.HomFreeFinite` (Mumford, *Abelian varieties*, §19 Thm 3,
locator UNVERIFIED).

What remains open is one construction on the abelian-variety layer, the Weil-restriction
structure itself. It is the existence of the conjugation action of `G_ℚ` on the Hom lattice of the
conjugates (`ConjActionExists (conjData K A)`), together with two properties of that action:
continuity, and trivial inertia outside `T`. Plus `dim(A_e) = 2` for base changes. The
conjugates themselves are constructed (`conjData`), and the conjugation action, if it exists, is
unique (`isConjAction_unique`). So the open hypothesis pins down a specific object: it cannot be
met by an arbitrary action.

Statement of the main theorem (`G4WeilRes.homField_of_model`). The hypotheses are:

- `K ⊆ ℚ̄` is finite Galois, with `[K:ℚ] ≤ F₀ = 324!`.
- `K` is unramified outside `T`, in the Galois form `GlueB3Unram.GalUnramifiedOutside`. This is G2's output.
- `A : PkgI3.AbVar K` is a variety whose `[K:ℚ]` conjugates `A_e = A ×_{K,e} ℚ̄` are surfaces.
- `ρ : G_ℚ →* Aut_ℤ(⊕_{e,e'} Hom(A_e, A_{e'}))` is the conjugation action. It is continuous, and
  every inertia group over every `p ∉ T` acts trivially.

The conclusion: there is `L ⊇ K`, finite Galois over `ℚ`, such that:

- `G_L` fixes every geometric homomorphism among the conjugates;
- `[L:ℚ] ≤ D = ZInQ.heightD`;
- `L` is unramified outside `T`, both in the Galois form and in glue-descent's ideal-theoretic
  form `UnramifiedAt L p`, which is the form `b3_degree_le_QM` takes.

## 1. What G4 must deliver (VERIFIED by reading the consumers)

The manuscript's step is N5 L544-563, VERIFIED by reading `diophantine_zq.tex` L544-563. Its output
goes to two places.

- **G7, B3**: `GlueDescent.B3Q.b3_degree_le_QM` (`ZInQKernel/HDecomp/Descent/B3Assembly.lean`)
  takes:
  - `L : IntermediateField ℚ (AlgebraicClosure ℚ)` with `[FiniteDimensional ℚ L] [IsGalois ℚ L]`;
  - `finrank ℚ L ≤ heightD`;
  - `∀ p : Nat.Primes, p ∉ ramSet S u → UnramifiedAt L p`;
  - a sign cocycle `ε` with `InflatedFrom L ε`. This last input is G7's instantiation: the descent
    data `μ_σ` are elements of the lattice, so a field that defines the lattice defines `ε`.
- **The CM branch**: `GlueAssembly.CMOutput` takes only a real `d` with `1 ≤ d ≤ heightD`.

`GlueAssembly.GlueOutputs` itself never mentions `L`. It reaches the assembly only through
these two consumers.

## 2. What compiles (`scratch/g4-weilres/G4.lean`, namespace `G4WeilRes`)

| Declaration | Content | Status |
| --- | --- | --- |
| `exists_liesOver` | there is a valuation subring of `ℚ̄` over every prime `p` (Mathlib's `Ideal.image_subset_nonunits_valuationSubring`) | compiled |
| `exists_inertia_restrict` | `L` finite Galois, `σ` trivial modulo `w` on the integers of `L` ⇒ some `s ∈ I_w` agrees with `σ` on `L` | compiled |
| `unramifiedAt_of_inertia_le` | **the bridge**: if every `I_w` over `p` fixes `L`, then `UnramifiedAt L p` | compiled |
| `galUnramifiedOutside_iff` | `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` for finite Galois `L` (the converse direction is glue-b3-unram's `inertia_le_of_unramifiedAt`) | compiled |
| `toGL`, `toGL_injective` | `Aut_ℤ(M) ↪ GL_r(ℤ)` from a basis | compiled |
| `homField_core` | **the core** (see below) | compiled |
| `homField_le_heightD` | the core with `[K:ℚ] ≤ F₀`, `r ≤ 16F₀²` ⇒ `[L:ℚ] ≤ D` (`GlueRepo.Numerics.a8_degree`, `heightD_eq`) | compiled |
| `pi_rank_le` | `∏_{(i,j)}` of free modules of rank `≤ c` has rank `≤ c·n²` | compiled |
| `trivial_of_faithful`, `conj_trivial` | an equivariant injective realization transfers trivial actions (N5 L559-561's "and therefore on its endomorphism lattice") | compiled |
| `HomLattice A` | `∀ ij : Idx × Idx, PkgI3.AbVar.Hom (A ij.1) (A ij.2)` | definition |
| `homLattice_free` | from the leaf `HomFreeFinite`: for surfaces, `HomLattice` is free and finite of rank `≤ 16·#Idx²` | compiled |
| `homField_of_conjugates` | G4 for any finite family of surfaces over `ℚ̄` with `#Idx ≤ F₀` | compiled |
| `ConjData`, `IsConjAction` | conjugation data (pullback squares over `Spec σ`) and the characterization `σf ∘ g_{σ,i} = g_{σ,j} ∘ f` | definitions |
| `isConjAction_unique` | at most one conjugation action for given data (`IsPullback.hom_ext`) | compiled |
| `bcAlong`, `embAct`, `conjMap`, `conjMap_isPullback`, `conjData` | **the conjugates of a model `A/K`**: base change along each embedding `e : K → ℚ̄`, the permutation action `σ·e = σ∘e`, and the pullback squares `A_{σ∘e} → A_e` over `Spec σ` (pasting, `IsPullback.of_right'`) | compiled, no hypotheses |
| `card_conjugates` | `#(K →ₐ[ℚ] ℚ̄) = [K:ℚ]` (`AlgHom.card`) | compiled |
| `homField_of_model` | G4 for a model `A/K` (statement above) | compiled |
| `ConjActionExists` | the open glue target (a `Prop`) | definition |
| `b3_of_homField` | G4's `L` with `T = ramSet S u` fed into `b3_degree_le_QM`. The output is `χ`, `β` and `L' ⊇ L ⊇ K` Galois with `[L':ℚ] ≤ Q_R·M_S(u)` | compiled |
| `cm_degree_of_homField` | `1 ≤ [L:ℚ] ≤ D` as reals (`CMOutput`'s `d`) | compiled |

**The core, `homField_core`** (proved, no leaf). Let `K ⊆ ℚ̄` be finite Galois and unramified
outside `T` (Galois form). Let `M` be a `ℤ`-module with a basis indexed by `Fin r`, and
`ρ : G_ℚ →* (M ≃ₗ[ℤ] M)` an action in which every `m` has an open stabilizer and every `I_w` over
every `p ∉ T` acts trivially. Then there is `L ⊇ K`, finite Galois, such that:

- `G_L` acts trivially on `M`;
- `[L:ℚ] ≤ [K:ℚ]·3^{r²}`;
- `L` is unramified outside `T`, in both forms.

Proof:

1. `ker ρ` is open, as a finite intersection of the stabilizers of the basis vectors.
2. `E = fixedField(ker ρ)` is finite Galois, by Mathlib's infinite Galois theory:
   `InfiniteGalois.fixingSubgroup_fixedField`, `isOpen_iff_finite`, `normal_iff_isGalois`.
3. `[E:ℚ] = |Gal(E/ℚ)| = |G_ℚ/ker ρ| = |ρ(G_ℚ)| ≤ 3^{r²}`. The last step is Minkowski,
   `GlueRepo.TorsionFree.card_le_three_pow`, through `toGL`.
4. Take `L = E ⊔ K`. Then `[L:ℚ] ≤ [E:ℚ][K:ℚ]`.
5. The inertia `I_w` at `p ∉ T` lies in `G_E ∩ G_K = G_L`, by Mathlib's `fixingSubgroup_sup`.
   The bridge then turns this into `UnramifiedAt`.

**The bridge, `unramifiedAt_of_inertia_le`** (proved, no leaf) is new, and is useful beyond G4: it
converts any Galois-form unramifiedness, such as glue-b3-unram's for `L'`, into the ideal-theoretic
form. Proof:

1. Choose a place `w` over `p`, and let `P₀` be its center on `𝓞_L`.
2. Lift `g ∈ I(P₀|p) ≤ Gal(L/ℚ)` to some `σ ∈ G_ℚ`.
3. Turn `σ` into an element of `I_w` that agrees with `σ` on `L`. This uses Mathlib's profinite
   transitivity and `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, over the ring of
   algebraic integers fixed by `G_L`. It follows glue-b3b's `exists_inertia_neg`, and uses
   glue-conj's center lemma through `mem_inertia_of_center`.
4. The hypothesis kills that element, so `g = 1`.
5. Hence `e(P₀) = |I(P₀)| = 1`, by Mathlib's `card_inertia_eq_ramificationIdxIn`. Every prime of
   `𝓞_L` over `p` has the same `e`, by `ramificationIdxIn_eq_ramificationIdx`.

Compile: `lake build ZInQKernel.HDecomp.B3Unram.B3b ZInQKernel.HDecomp.Repo.TorsionFree
ZInQKernel.HDecomp.Repo.Numerics ZInQKernel.HDecomp.Descent.B3Assembly ZInQKernel.HDecomp.Objects`,
then `lake env lean scratch/g4-weilres/G4.lean`. About 15-35 s once those oleans exist, VERIFIED.

## 3. What remains

These are the open hypotheses of `homField_of_model`, in decreasing order of size.

1. **`ConjActionExists (conjData K A)`**. This is the Weil-restriction step proper. It is glue,
   STANDARD and not formalized. It asks for a `ℤ`-linear group action
   `ρ : G_ℚ →* Aut_ℤ(⊕ Hom(A_e, A_{e'}))` satisfying `IsConjAction`.
   - The underlying morphism `σf` exists and is unique by the pullback property. `conjMap` gives
     the squares.
   - The crux is that `σf` is a *homomorphism* and that `σ ↦ (f ↦ σf)` is additive. Both need the
     squares `conjMap` to respect the group laws: `g ∘ μ_{A_{σe}} = μ_{A_e} ∘ (g ×_{Spec σ} g)`.
     That in turn needs the monoidal structure of Mathlib's `Over.pullback` (used through
     `Functor.grpObjObj`) to commute with pullback pasting.
   - The group law `ρ(στ) = ρ(σ)ρ(τ)` then follows from the uniqueness argument of
     `isConjAction_unique`, applied to the pasted squares. The squares compose, because
     `conjMap`'s are lifts into one pullback; this is not yet proved in Lean.
   - Estimated size: medium (0.5-1k lines, SPECULATIVE).
2. **Continuity** (`hcont`: every geometric homomorphism has an open stabilizer). It is a
   consequence of: every homomorphism `A_ℚ̄ → B_ℚ̄` is the base change of one over a number
   field. That is the limit theorem for morphisms of finitely presented schemes, EGA IV₃ 8.8.2
   (locator UNVERIFIED), a leaf candidate stated with `bcAlong`. Deriving `hcont` from it also
   needs the compatibility of `ρ` with base change. That is glue, after item 1.
3. **Inertia** (`hinert`). Fix `p ∉ T` and `s ∈ I_w`.
   - `s ∈ G_K`, since `K` is unramified outside `T`. So `s` fixes every embedding `e`, because
     `K/ℚ` is Galois.
   - `s` acts trivially on `T_ℓ(A_e)` (`ℓ ≠ p`) by Néron–Ogg–Shafarevich. This is the leaf
     `PkgI2.NeronOggShafarevich`, through `PkgI2.inertiaTrivial_of_goodReduction`. The good
     reduction of every conjugate at primes over `p` is G3's output.
   - `trivial_of_faithful` (proved) carries this to the lattice. It needs two things:
     - injectivity of `Hom → Hom_{ℤ_ℓ}(T_ℓ, T_ℓ)`. This is `HomFreeFinite`'s last clause on
       `ℤ_ℓ ⊗ Hom`, plus flatness of `ℤ → ℤ_ℓ` on the free module `Hom`;
     - equivariance of the realization. This needs the action on points, which has the same
       group-law issue as item 1.
4. **`hdim`**: `dim(A ×_{K,e} ℚ̄) = 2` when `dim A = 2`. Dimension is invariant under field
   extension. It is STANDARD and missing from Mathlib; leaf-qm-fp's `IsBaseChangeOf` notes the
   same gap.
5. **`hK`**: `K` unramified outside `T`. This is G2's output, already open there. Either form
   works now, by `galUnramifiedOutside_iff`.
6. On G7's side, outside G4: `hdesc` in `b3_of_homField` says that the cocycle `ε` of the
   descent data is inflated from any field that defines the lattice. That is G7's
   instantiation.

The manuscript's own formulation is more than what is consumed. It forms
`W₀ = Res_{K/ℚ} A` as a scheme, and Mathlib has no Weil restriction of schemes. But the argument
uses only `End(W₀_ℚ̄) = ⊕_{σ,τ} Hom(σA, τA)` with its `G_ℚ`-action, which is what `HomLattice`
with `ConjData` formalizes. So **no Weil restriction of schemes is needed for G4**. The weakest
form that is consumed is `homField_le_heightD`, taken on the lattice of the conjugates.

## 4. Suggested update of h-decomposition §3, row G4 (for the integrator)

> G4: the Hom field **proved** from the lattice: `G4WeilRes.homField_core` (Minkowski + infinite
> Galois theory) and `homField_of_model` on `conjData K A` (the conjugates of `A/K`,
> constructed), with leaf `HomFreeFinite`. The output feeds `b3_degree_le_QM` (`b3_of_homField`)
> and `CMOutput` (`cm_degree_of_homField`). There is a new bridge
> `GalUnramifiedOutside ↔ UnramifiedAt` (`galUnramifiedOutside_iff`). Open: `ConjActionExists`
> (the conjugation action respects group laws), continuity (EGA IV 8.8.2), the inertia hypothesis
> on the lattice (NOS + realization equivariance), and `dim` of base change (g4-weilres).

## 5. Labels

- VERIFIED (compiled): every declaration in §2, and their axiom lists.
- VERIFIED (read): N5 L544-563, and the consumers' signatures in `B3Assembly.lean`, `B2Glue.lean`
  and `Leaves.lean` (`GlueAssembly`).
- STANDARD, not formalized: items 1-4 of §3.
- UNVERIFIED locators: Mumford §19 Thm 3; Serre–Tate 1968 Thm 1; EGA IV₃ 8.8.2.
