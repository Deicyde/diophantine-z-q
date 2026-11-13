# g0-mod-galois (fleet note)

**Result.** The glue range G8-G12 of `ModularConstituent` is proved in Lean, with no `sorry`, from
these inputs:
- the leaf bundles (R9a, R9b, R10, R11+R12 = Pan∘Berger, R13, R14, R15, T6, T9, T11, T12, T17,
  T18, T19, T23, T26);
- glue-ssbc's proved `SemisimpleBaseChange`;
- the outputs of the earlier steps, `G2Out`, `G3Out`, `G6Out`, `G7Out` (the ℓ-adic scalar-descent
  data and the matrix units of `B ⊗ ℚ̄_ℓ`);
- five named glue Props: `G8Matrix` (linear algebra), `G9Glue` (N5's de Rham descent lemma),
  `G10Glue` (oddness), `G12Weight` (Hodge–Tate weight comparison), `G12Det` (the determinant
  identities).

The conclusion is a continuous `r₅ : G_ℚ → GL₂(ℚ̄₅)` with five properties:
- `ℚ̄₅ ⊗ V₅(A) ≅ r₅ ⊕ r₅`, which on `G_ℚ` is the descended `ρ` and on `G_{L'}` the Tate action;
- absolutely irreducible on `G_{L'}`;
- de Rham at 5 with weights `{0, −1}`;
- odd;
- unramified outside `T ∪ {5}` and attached, up to a finite-image twist, to a weight-2
  eigenform (`G0Galois.g8_g12_of_leaves`).

`r₃` comes from `g8_g11` at `ℓ = 3`. Proved outright:
- G11, with no named glue;
- the Pan application;
- `k = 2` (`weight_match`);
- finiteness of the twist (`twist_finite`);
- C2's application;
- the descended representation and its splitting.

**Feeds the next range exactly.** `G0Galois.newformG12Out_of_galois` proves g0-mod-newform's input
`G12Out A` (its definitions are copied verbatim as `G0Galois.NF.*`). It needs one more named Prop,
`FiniteCharDirichlet` (Kronecker–Weber step). `commonConstituent_of_sides` gives `ModularConstituent`'s
`CommonConstituent` directly from G8's splitting and a `J`-side embedding.

**Compiles.** `lake env lean scratch/g0-mod-galois/ModGalois.lean` (g0-split's `Split.lean` + the
two parts, assembled by `build.sh`): 0 errors, no `sorry`. The axioms are [propext, Classical.choice,
Quot.sound] for all eight main theorems (VERIFIED, run7).

**Finding.** R14 as stated (`HSyn.EigenformRepExists`, consequence form) omits the published
determinant `det ρ_g = ε_g χ^{k−1}`, which the determinant argument (`G12Det`) needs.
Recommendation: add that clause to R14.

**Remains.**
- The five named Props, plus `FiniteCharDirichlet`; sizes and arguments are in
  docs/research/g0-mod-galois.md §3.
- The ℓ-adic realization `G7Realize` of g0-mod-field's points-level `G7Data` (prose only; §4.3).
- Local versus global inertia for g0-mod-newform's G15Ram (§4.1).
- One common environment: the partners build over `ZInQKernel/HDecomp/`, while this file builds on
  `Split.lean`, where the leaf statements live.
