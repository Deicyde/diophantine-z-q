# g4-weilres (fleet summary)

**Result: G4 (Weil restriction and the Hom field) is proved in Lean from three named inputs,
plus the outputs of G2 and G3 and the dimension of a base change.**
File: `scratch/g4-weilres/G4.lean`, 1447 lines, no `sorry`. All 19 printed theorems depend only
on `propext`, `Classical.choice`, `Quot.sound` (VERIFIED). Report: `docs/research/g4-weilres.md`.

## Headline: `G4WeilRes.homField_of_model_leaves`

- **Inputs** (`def … : Prop`):
  - `PkgI3.HomFreeFinite` (Mumford §19 Thm 3);
  - `MorphismsDescend` (EGA IV₃ 8.8.2: a morphism between base changes to `ℚ̄` comes from a number
    field);
  - `InertiaFixesHoms` (NOS + Mumford + equivariance; that last glue step is not formalized).
- **Hypotheses from other steps**: `hK` (G2: `K` unramified outside `T`), `hgood` (G3: good
  reduction of `A/K` above `p ∉ T`), `hdim` (`dim A_e = 2`, missing from Mathlib).
- **Conclusion**: for `A/K` with `K ⊆ ℚ̄` finite Galois and `[K:ℚ] ≤ F₀`, there is a Hom field
  `L ⊇ K` such that:
  - `L` is finite Galois, with `[L:ℚ] ≤ D`;
  - `G_L` fixes every homomorphism between conjugates;
  - `L` is unramified outside `T`, both as `GalUnramifiedOutside` and as `UnramifiedAt`.

## What compiles

- **Weil-restriction step, constructed.**
  - The conjugates `A_e = A ×_{K,e} ℚ̄` (`conjData`).
  - The conjugation action `conjAction K A : G_ℚ →* Aut_ℤ(⊕ Hom(A_e, A_{e'}))`, a group
    homomorphism (`conjActionExists`). This is `End(Res_{K/ℚ}A ⊗ ℚ̄)` as N5 uses it; no Weil
    restriction of schemes is needed.
  - Generic `G4Conj.conj_isMonHom`: the conjugate of a homomorphism is a homomorphism, via
    Mathlib's monoidal `Over.pullback`.
  - Uniqueness: `isConjAction_unique`.
- **Hom field core** (`homField_core`): Minkowski + infinite Galois theory. `[L:ℚ] ≤ [K:ℚ]·3^{r²}`,
  hence `≤ D`.
- **Bridge** (`galUnramifiedOutside_iff`): the Galois and ideal-theoretic forms of unramifiedness
  agree on finite Galois fields. New, and reusable for G7's `L'` and for G11.
- **Continuity**: `homDescends_of_morphismsDescend` and `conjAction_continuous` (the descent
  bookkeeping, proved).
- **Inertia**: `conjAction_inertia` (from `hK`, `hgood`, `InertiaFixesHoms`), and the
  `ℓ`-adic faithfulness `tateHom_injective` (from `HomFreeFinite`).
- **Consumers**: `b3_of_homField` feeds G7's `b3_degree_le_QM`; `cm_degree_of_homField` gives
  the CM branch's `d ≤ D`.

## What remains

1. The equivariance glue inside `InertiaFixesHoms`: the `G_ℚ`-action on the points and Tate
   modules of the conjugates, compatible with `conj`.
2. `hdim`: invariance of dimension under field extension (Mathlib).
3. `hK` and `hgood`, the outputs of G2 and G3, and their instantiation on the actual `A`.
4. G7's own `hdesc` (`ε` inflated from `L`), outside G4.
