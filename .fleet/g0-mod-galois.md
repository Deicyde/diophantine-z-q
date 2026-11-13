# g0-mod-galois (fleet note)

**Result.** The glue range G8-G12 of `ModularConstituent` is proved in Lean, with no `sorry`, from
these inputs:
- the leaf bundles (R9a, R9b, R10, R11+R12 = Pan∘Berger, R13, R14, R15, T6, T9, T11, T12, T17,
  T18, T19, T23, T26);
- two leaves outside the bundles: Burnside (`BurnsideAbsIrred`, textbook) and R14 with its
  published determinant clause (`R14Det`);
- glue-ssbc's proved `SemisimpleBaseChange`;
- the outputs of the earlier steps, `G2Out`, `G3Out`, `G6Out`, `G7Out` (the ℓ-adic scalar-descent
  data and the matrix units of `B ⊗ ℚ̄_ℓ`);
- five named glue Props: `G9Glue` (N5's de Rham descent lemma), `G10Glue` (oddness),
  `G12Weight` (Hodge–Tate weight comparison), `DetTate` (`det V_ℓ(A) = χ_ℓ^{dim A}`, from T9),
  `ResQFiniteIndex` (`[G_ℚ:G_K] < ∞`).

The first-draft pieces `G8Matrix` and `G12Det` are proved (`g8Matrix_of_burnside`,
`g12Det_of`).

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
- finiteness of the twist (`g12Det_of`: traces agree via Chebotarev, the `2×2` determinant
  identity, `det(r⊕r)` through the splitting; then `twist_finite`);
- C2's application;
- the descended representation and its splitting.

**The three ranges interlock.** A token comparison (VERIFIED, 02:55) found every definition that
the partners copied from this file identical to the current one:
- g0-mod-field's `GaloisCopy` (`resQ`, `Vb`, `tate`, `G2Out`, `G7Out`). It proves `G2Out` from its
  `G7Data`, and states `TateBridge` (`G7Data` → `G7Out`).
- g0-mod-newform's copies (`resQ`, `Vb`, `tate`, `Intertwines`, `G8Out`, `G12Out`). Its proved
  `g12Spec_of_galois` turns `G8Out` at 3 and 5 plus `G12Out` into its input `G12Spec`, and its
  `G15RamG` clause (iii) is `G11Out`.

`resQ` is Mathlib's `Field.absoluteGaloisGroup.map`, with `resQ_spec` proved for the embedding
that `map` chooses. A redefinition during the run was reverted to keep this match.

**Feeds the next range exactly.** `G0Galois.newformG12Out_of_galois` proves g0-mod-newform's input
`G12Out A` (its definitions are copied verbatim as `G0Galois.NF.*`). It needs one more named Prop,
`FiniteCharDirichlet` (Kronecker–Weber step). `commonConstituent_of_sides` gives `ModularConstituent`'s
`CommonConstituent` directly from G8's splitting and a `J`-side embedding.

**Compiles.** `lake env lean scratch/g0-mod-galois/ModGalois.lean` (g0-split's `Split.lean` + the
four parts, assembled by `build.sh`): 0 errors, no `sorry`. The axioms are [propext, Classical.choice,
Quot.sound] for all eleven main theorems (VERIFIED, run12, 2m30s).

**Finding.** R14 as stated (`HSyn.EigenformRepExists`, consequence form) omits the published
determinant `det ρ_g = ε_g χ^{k−1}`, which the determinant argument needs. It is added here as
the leaf `R14Det`. Recommendation: replace the bundle's R14 by it.

**Remains.**
- The five named glue Props, plus `FiniteCharDirichlet`; sizes and arguments are in
  docs/research/g0-mod-galois.md §3.
- g0-mod-field's `TateBridge` (the ℓ-adic realization of its `G7Data`).
- g0-mod-newform's `G14TraceCompat` and `G15RamG` (i)-(ii). Both need `G8Out`'s descent link on
  all of `G_ℚ` (report §4.2).
- One common environment: the partners build over `ZInQKernel/HDecomp/`, while this file builds on
  `Split.lean`, where the leaf statements live.
