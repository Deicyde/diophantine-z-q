# g0-mod-galois (fleet note)

**Result.** The glue range G8-G12 of `ModularConstituent` is proved in Lean, with no `sorry`
(`G0Galois.g8_g12_of_leaves`). Its inputs are:
- the leaf bundles;
- two further leaves: Burnside's theorem (`BurnsideAbsIrred`) and R14 with its published
  determinant clause (`R14Det`);
- the outputs of the earlier steps: `G2Out`, `G3Out`, `G6Out`, and `G7Out` (ℓ-adic descent data
  with the matrix units of `B ⊗ ℚ̄_ℓ`);
- five named glue Props: `G9Glue` (de Rham descent lemma), `G10Glue` (oddness), `G12Weight`
  (Hodge–Tate comparison), `DetTate` (`det V_ℓ(A) = χ_ℓ^{dim A}`, from T9) and
  `ResQFiniteIndex`.

The output is a continuous `r₅ : G_ℚ → GL₂(ℚ̄₅)` with these properties:
- `ℚ̄₅ ⊗ V₅(A) ≅ r₅ ⊕ r₅`, through the descended `ρ` on `G_ℚ`;
- absolutely irreducible on `G_{L'}`;
- de Rham at 5 with weights `{0, −1}`;
- odd;
- unramified outside `T ∪ {5}`;
- attached, up to a finite-image twist, to a weight-2 eigenform.

`g8_g11` gives the same G8-G11 properties for `r₃`.

What is proved outright:
- G11;
- Pan's application;
- `k = 2`;
- finiteness of the twist (`g12Det_of`, by Chebotarev and the 2×2 determinant identity);
- C2;
- the linear algebra of G8 (`g8Matrix_of_burnside`);
- the link to `CommonConstituent`.

**Interlock (VERIFIED, token comparison).** g0-mod-field and g0-mod-newform copied this file's
`resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, `Intertwines`, `G8Out` and `G12Out`. All copies are
identical to the current definitions.
- g0-mod-field proves `G2Out` from its `G7Data` and states `TateBridge` (`G7Data` → `G7Out`).
- g0-mod-newform proves that `G8Out` at 3 and 5 plus `G12Out` give its input `G12Spec`, and its
  G15 clause (iii) is `G11Out`.

This file also proves that bridge itself (`newformG12Out_of_galois`, with `FiniteCharDirichlet`).

**Compiles.** `lake env lean scratch/g0-mod-galois/ModGalois.lean` (`Split.lean` + four parts,
`build.sh`) gives 0 errors and no `sorry`. The axioms are standard for all ten main theorems
(run13). One model review (read-only) judged all nine named Props and four inputs true; it found
one docstring defect (`Tm σ = μ_σ∘σ`, without `a_σ`), now fixed.

**Finding.** The bundle's R14 omits the published `det ρ_g = ε χ^{k−1}`, which the determinant
argument needs. This file states it as `R14Det`. Recommendation: replace the bundle's R14 by it.

**Remains.**
- The five named Props and `FiniteCharDirichlet` (docs/research/g0-mod-galois.md §3).
- g0-mod-field's `TateBridge`.
- g0-mod-newform's `G14TraceCompat` and G15 (i)-(ii). Both need `G8Out`'s descent link.
- One common environment: the partners use `ZInQKernel/HDecomp/`; this file uses `Split.lean`.
