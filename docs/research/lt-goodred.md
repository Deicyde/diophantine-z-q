# lt-goodred: `GoodRedTorsion` and `QMEndRank` are proved

Task lt-goodred, 2026-11-13. Lean: `scratch/lt-goodred/` (results log `log.md`).

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. **UNVERIFIED** = theorem number recalled without a source (no
network). Model work only; no human review.

## 0. Main result

**Both glue Props are proved, with no statement changed and no new leaf.** Both are copied
verbatim from linked-tate (`scratch/linked-tate/parts/98_g3tate.lean`, `parts/95_linked.lean`).

```lean
theorem LTGoodRed.goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion
theorem LTGoodRed.QM.qmEndRank_of_leaves (hM1 : PkgI3.HomFreeFinite)
    (hT27 : PkgI3.QMDichotomyYu) : HSyn.LinkedTate.QMEndRank
```

- **`GoodRedTorsion`** needs no hypothesis. The leaf NOS (R7a,
  `PkgI2.NeronOggShafarevich`) is the antecedent of the Prop itself. The proof transports places,
  inertia, `resQ` and points; it uses Mathlib, unram-tate's `bcPt`/`trPt` and neron-lg's
  classification of the valuation rings of a number field.
- **`QMEndRank`** follows from two leaves that are already in `TextbookLeaves`:
  - I3.M1 (`t6`, Mumford §19 Thm 3);
  - T27 (`t27`, Yu 2013 Thm 1.1).

  Albert's classification, which linked-tate's docstring names, is **not** needed. Over `Ω = \bar{L'}`,
  T27 has two cases:
  - `End⁰(A'_Ω) ≅ B`: this gives `rank ≤ 4`;
  - `End⁰(A'_Ω) ≅ M₂(ℚ(√d))`: this case is excluded by `EndDivision` and a dimension count.

  T27's own hypotheses are proved here:
  - `B = (2,−3)` is a division algebra;
  - `B ↪ End⁰`;
  - `dim A'_Ω = 2`.
- **Integration** (`scratch/lt-goodred/integ/`). `HSyn.GluePieces4` is linked-tate's
  `GluePieces3` without the fields `goodRedTorsion` and `qmEndRank`, so it has 27 fields instead
  of 29. The composite is:

  ```lean
  theorem HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves) (t : TextbookLeaves)
      (gp4 : GluePieces4) : ZInQ.SixContactMin
  ```

  It compiles against linked-tate's committed files (VERIFIED, §5). The fields are filled by:
  - `goodRedTorsion := LTGoodRed.goodRedTorsion`;
  - `qmEndRank := LTGoodRed.QM.qmEndRank_of_leaves t.t6 t.t27`.

**VERIFIED** (Lean 4.35.0, Mathlib v4.35.0): see §5. Every axiom report is
`[propext, Classical.choice, Quot.sound]`.

## 1. The statements (copied, unchanged)

- **`GoodRedTorsion`.** Assume NOS. Let `K ≤ L ≤ L'` be subfields of `ℚ̄` with `L'/ℚ` finite,
  and let `A/K` have good reduction at every DVR of `K` in which `3` is a unit. Take:
  - a prime `ℓ`, and a prime `p ∉ {3, ℓ}`;
  - a place `v` of `ℚ̄` above `p`;
  - `σ' ∈ G_{L'}` such that `resQ σ'` lies in the inertia group of `v`.

  Then `σ'` fixes every `ℓⁿ`-torsion point of `A_{L,L'}(\bar{L'})`.
- **`QMEndRank`.** Let `PK` be a `QML3` object over `K`, let `K ≤ L ≤ L'` with `L'/ℚ` finite, and
  let `A' = (PK.A)_{L,L'}`. If `EndDivision A'`, then `finrank_ℤ End(A') = 4`.

## 2. `GoodRedTorsion` (`parts/20_goodred.lean`)

Let `Ω = \bar{L'}`.

1. **The embedding `g`.** `g = qEmbRing L' : ℚ̄ → Ω` is the embedding that
   `Field.absoluteGaloisGroup.map` uses. It is bijective, because `Ω/ℚ` is algebraic, and
   `g ∘ resQ σ' = σ' ∘ g` (`resQ_spec`).
2. **The isomorphisms `τ` and `ψ`.** `τ : Ω ≃ₐ[K] \bar K` exists because `Ω` is an algebraic
   closure of `K` (`IsAlgClosure.equiv`). Set `ψ = g⁻¹ ∘ τ⁻¹ : \bar K ≃ ℚ̄`.
3. **The places `w` and `O`.** Let `w = ψ^*(v)`, a valuation ring of `\bar K`, and `O = w ∩ K`.
   - `p ∈ 𝔪_w`, so `p⁻¹ ∉ O` and `O ≠ K`. By neron-lg's `isDiscreteValuationRing_of_ne_top`,
     `O` is a DVR.
   - `3` and `ℓⁿ` are prime to `p`, hence units of `O` (`natCast_notMem_nonunits`: Bézout in the
     local ring `w`).
   - `O` need not be `v ∩ K` for the inclusion `K ⊆ ℚ̄`, because `resQ`'s embedding is arbitrary.
     This does not matter, since the hypothesis covers every DVR of `K` with `3` a unit.
4. **The inertia element.** `σ_K = τ σ' τ⁻¹` satisfies `ψ ∘ σ_K = resQ σ' ∘ ψ`. Mathlib's inertia
   subgroup is equivalent to "preserves the ring and acts trivially modulo the maximal ideal"
   (`of_mem_inertia`, `isInertia_of`). Hence `σ_K` is in the inertia group of `w`
   (PkgI2's `IsInertia`).
5. **NOS.** NOS (a) ⇒ (b) at `(O, w)`, applied with `m = ℓⁿ`, makes `σ_K` fix `A(\bar K)[ℓⁿ]`.
6. **The points.** `E = trPt τ ∘ bcPt ∘ bcPt : A_{L,L'}(Ω) ≃* A(\bar K)` is multiplicative and
   carries `σ'` to `σ_K` (`bcPt_galAct` twice, `trPt_galAct`). It is injective, so `σ'` fixes `x`.

Combined with linked-tate's `goodRedG3Bridge_of_torsion` and `qmModelG3_of`, this proves
`GoodRedG3Bridge` and `QMModelG3`, i.e. G3 on the model, from R6, R7a and T5 alone.

## 3. `QMEndRank` (`parts/40_qmrank.lean`, `parts/50_split.lean`)

Write `M = End(A')`, `A'' = A'_Ω` with `Ω = \bar{L'}`, and `ι : 𝒪 → End(PK.A)`.

1. **`rank M ≥ 4`** (`four_le_finrank`). `𝒪 ≅ ℤ⁴` (`ofIntHom`), and `endBC ∘ endBC ∘ ι : 𝒪 → M`
   is an injective ring map. `M` is finite over `ℤ` by I3.M1.
2. **`rank M ≤ rank End(A'')`** (`finrank_le_baseChange`). `endBC` is injective (flat descent).
   Moreover `rank_ℤ End = dim_ℚ End⁰`, because `End` is free by I3.M1 (`finrank_end0`).
3. **T27 at `A''`.** Its hypotheses are proved:
   - **`dim A'' = 2`.** `QML3.surface` with g0-dim's `pkgI3_dim_baseChange`, applied three times.
   - **`B = (2,−3)` is a division algebra** (`quatB6_isUnit`). We have `x x̄ = n(x)` with
     `n = x₀² − 2x₁² + 3x₂² − 6x₃²`. This form is anisotropic over `ℚ` by a 3-adic descent: mod 3,
     `x₀² + x₁² ≡ 0` forces `3 | x₀, x₁`, and then the same holds for `x₂, x₃` (`norm6_int`,
     `norm6_rat`).
   - **`B →ₐ[ℚ] End⁰(A'')`** (`quatEmbed`). Send `i ↦ 1 ⊗ φ(i)` and `j ↦ 1 ⊗ φ(2·(1+j)/2 − 1)`,
     using `QuaternionAlgebra.Basis.liftHom`. The relations hold in `𝒪`.
4. **Case `End⁰(A'') ≅ B`.** Then `rank M ≤ dim_ℚ B = 4`.
5. **Case `End⁰(A'') ≅ M₂(ℚ(√d))`** (`qmSplitCaseRank`). Suppose `rank M > 4`.
   - `End⁰(A') ↪ End⁰(A'') ≅ M₂(F)`, which has dimension 8. The embedding exists because `ℚ` is
     flat over `ℤ` (`IsLocalization.flat`).
   - `θ : B → End⁰(A')` exists, and `B` is a division algebra. So for `s ∉ θ(B)`, the map
     `(b, b') ↦ θb + θb'·s` is injective. This gives `dim ≥ 8` (`eight_le_finrank`).
   - Hence `End⁰(A') ≅ M₂(F)`. The preimage `x` of `E₁₂` satisfies `x ≠ 0` and `x² = 0`.
   - Clearing denominators gives `n·x = 1 ⊗ m` with `m ≠ 0` and `m² = 0` (`exists_smul_eq_tmul`,
     `one_tmul_injective`).
   - **`eq_zero_of_mul_self_eq_zero`.** If `m ≠ 0`, then `EndDivision` makes `m` surjective, so
     `m ∘ m = 0` is surjective too. The zero endomorphism is `toUnit ≫ η`, which factors through
     `Spec k`, a single point. So `A'` would be a point, with `dim ≤ 0 ≠ 2`.

## 4. Findings

- **Neither statement is false, vacuous or inert.** Both are proved over genuine definitions:
  - **`GoodRedTorsion`.** Its antecedents are the leaf NOS and a good-reduction hypothesis that
    `QML3.goodReduction` supplies.
  - **`QMEndRank`.** Its hypothesis `EndDivision` is used, in case 2 of T27.
- **`QMEndRank` needs no literature beyond I3.M1 and T27.** Linked-tate's docstring calls it
  "literature-backed (Mumford §19 Thm 3, Albert's classification)". Albert is replaced by T27
  (already a leaf) together with an elementary dimension count.
- **A by-product.** `eq_zero_of_mul_self_eq_zero` holds for every abelian variety of positive
  dimension: `EndDivision` excludes nonzero square-zero endomorphisms. It is proved from the
  definitions alone.
- **A heartbeat note.** `goodRedTorsion` needs `set_option maxHeartbeats 1000000 in`. The default
  200 000 times out at `whnf`, which a run without the option confirmed (VERIFIED).

## 5. What compiles

- **`scratch/lt-goodred/GoodRed.lean`** (16 417 lines, assembled by `assemble.sh`) contains:
  - lines 1-14993 of linked-tate's `Leaves.lean`, a byte-identical copy of the pin-applied
    h-decomposition file, followed by four closers;
  - the parts `05_dim` (g0-dim, verbatim), `10_copies` (the verbatim copies listed in `log.md`),
    `20_goodred`, `30_qmendrank` (verbatim `QMEndRank` and `endBC`), `40_qmrank` and `50_split`.

  `lake env lean scratch/lt-goodred/GoodRed.lean`: VERIFIED exit 0 in 160 s, with 0 errors and no
  `sorry`. All 9 axiom reports are standard: `goodRedTorsion`, `quatB6_isUnit`, `quatEmbed`,
  `four_le_finrank`, `qmEndRank_of`, `eq_zero_of_mul_self_eq_zero`, `eight_le_finrank`,
  `qmSplitCaseRank` and `qmEndRank_of_leaves`.
- **Iteration.** `olean/Tail.lean` is compiled against an olean of the same prefix
  (`build_prefix.sh`, 202 s; then `ctail.sh`).
- **Integration** (`integ/`). It reads linked-tate's committed `Leaves.lean`, `imports_extra.txt`
  and `parts/`, and edits none of them. `build.sh prefix|tail|integ` runs an olean chain:
  - `prefix`: 533 s;
  - `tail`: 241 s;
  - `integ`: 103 s. Its input is `99d_proofs.lean`, which `make_proofs.py` generates from `parts/`
    without the copies that linked-tate already has, followed by `99e_bundle4.lean`.

  Every step: VERIFIED exit 0, 0 errors.
- **The integration as one flat file** (46 150 lines, generated, not committed): VERIFIED exit 0
  in 686 s, with 0 errors and no `sorry`. All 233 axiom reports are standard, including
  `HSyn.gluePieces3_of_gluePieces4` and `HSyn.sixContactMin_of_leaves4`.

## 6. What remains

- Of linked-tate's four new glue Props, `LinkedFrob` and `LinkedRam` remain. So do the other
  fields of `GluePieces4`.
- G3 on the model now rests on R6, R7a and T5 alone, through linked-tate's
  `qmModelG3_of ∘ goodRedG3Bridge_of_torsion` and `LTGoodRed.goodRedTorsion`.
