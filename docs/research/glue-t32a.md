# glue-t32a: T32(a) is glue, and B3 (v) now rests on no leaf

Status: research note (task glue-t32a, 2026-11-12). Lean: `scratch/glue-t32a/T32a.lean`
(self-contained, `import Mathlib`, 2266 lines; lines 9-1816 are `scratch/glue-b3b/B3b.lean` L3-1810
verbatim, and the new material starts at the comment `# glue-t32a`). Log: `scratch/glue-t32a/log.md`.

## Verdict

1. **(VERIFIED, compiled.)** `GlueB3Unram.t32a : LeafPush.T32a_TameQuadratic` is proved in Lean.
   This is leaf **T32(a)** of the synthesis bundle (`TextbookLeaves.t32a`). Its statement and the
   definitions it uses (`GQ`, `IsAtPrime`, `inertiaQ`) are `diff`-identical to
   `scratch/h-decomposition/Leaves.lean` L11908-11932 (L11918-11941 at 01267822; integrated since as
   `ZInQKernel/HDecomp/B3Unram/T32a.lean`). In words: for an odd prime `p` and a
   valuation subring `w` of `ℚ̄` with `w ∩ ℚ = ℤ_(p)`, there are exactly two continuous
   homomorphisms `I_w → ℤˣ`, where `I_w` is Mathlib's `ValuationSubring.inertiaSubgroup` pushed into
   `G_ℚ` with the Krull topology.
2. **(VERIFIED, compiled.)** `GlueB3Unram.leafB3a : LeafB3a` (via glue-b3b's `leafB3a_of_t32a`),
   and `GlueB3Unram.unramified_outside_noLeaf`. The latter is B3 (v): the twisted kernel field `L'`
   of N5 L702-712 is unramified outside `T`. It has exactly the hypotheses and conclusion of
   glue-b3b's `unramified_outside_t32a`, minus the hypothesis `T32a_TameQuadratic`. **B3 (v) rests
   on no leaf.**
3. **(VERIFIED.)** Every `#print axioms` line in the file reads `[propext, Classical.choice,
   Quot.sound]`. There are 20 lines: the 14 inherited ones, plus `exists_kummer`,
   `val_pow_eq_zpow`, `char_eq_sgn_zpow`, `t32a`, `leafB3a` and `unramified_outside_noLeaf`. The
   file has no `sorry` and no `axiom`, and `lake env lean scratch/glue-t32a/T32a.lean` finishes in
   about 21 s with 0 errors.
4. Effect on the decomposition. Both parts of T32 are now glue: T32(b) by glue-b3b (`t32b`) and
   T32(a) here. Once the files are integrated, leaf T32 (two Props) can be dropped from
   `TextbookLeaves` (done: T32 is no longer a `TextbookLeaves` field; `HSyn.t32a_glue`).

## The proof (no ramification groups, no tame-inertia structure)

The route glue-b3b proposed went through the structure of tame inertia (`G₀/G₁ ↪ k^×`, `G₁` a
`p`-group) or through the value group of the inertia field. Neither is needed. The proof below uses
only quadratic Kummer theory, the fact that values are rational powers of `v(p)`, and glue-b3b's
`exists_inertia_neg`. Throughout, `v` is the valuation of `w`, `g ∈ ℚ̄` satisfies `g² = p`, and
`η_g(τ) = τ(g)/g ∈ {±1}`.

- **Inertia element negating `√p`.** `√p ∉ ℚ`, so glue-b3b's `exists_neg_of_sq` gives some
  `σ ∈ G_ℚ` with `σg = -g`. Then `exists_inertia_neg` (with `c = p`) gives `τ₀ ∈ I_w` with
  `τ₀g = -g`. So `η_g` is nontrivial on `I_w`. It is continuous because `Stab(g)` is open
  (`etaG_continuous`).
- **Sign lemma** (`not_inertia_neg`). Let `τ ∈ I_w` and `v(z) = 1`. Then `τz = -z` is impossible:
  inertia acts trivially on the residue field, so `v(τz - z) < 1`. But `τz - z = -2z` has valuation
  `1`, because `p` is odd.
- **Kummer generator** (`exists_kummer`). Let `χ : I_w → ℤˣ` be continuous.
  - `ker χ` is open, so it contains `I_w ∩ Fix(E)` for some finite extension `E`, by Mathlib's
    `krullTopology_mem_nhds_one_iff`.
  - Let `γ` be a primitive element of `E` (`Field.exists_primitive_element`). Then `χ(τ)` depends
    only on `τγ`, which is a root of `minpoly γ`. Define `c(τγ) = χ(τ)` on the orbit and `c = 0` on
    the other roots.
  - Some power sum `β = Σ_y c(y) y^j` over the roots is nonzero, by the Vandermonde determinant.
    It satisfies `τβ = χ(τ)β` for all `τ ∈ I_w`.
- **Values** (`val_pow_eq_zpow`). For `x ∈ ℚ̄^×` there are `n ≥ 1` and `m ∈ ℤ` with
  `v(x)^n = v(p)^m`. The reason is that two terms of `minpoly x` evaluated at `x` have the same
  valuation (`Valuation.map_sum_eq_of_lt`), and a nonzero rational has valuation `v(p)^m`.
- **Classification** (`char_eq_sgn_zpow`). Let `n` be least with `v(β)^n = v(g)^k` for some
  `k ∈ ℤ`; this exists because `v(p) = v(g)²`.
  - `n` is odd. Suppose `n = 2a`. If `k` is even, then `v(β)^a ∈ v(g)^ℤ` (value groups are
    torsion-free), which contradicts the minimality of `n`. If `k` is odd, then `z = β^n g^{-k}` is
    a unit and `τ₀z = -z`, which contradicts the sign lemma.
  - For every `τ ∈ I_w`, `z = β^n g^{-k}` is a unit with `τz = χ(τ)^n η_g(τ)^{-k} z`. By the sign
    lemma this factor is `1`. Since `n` is odd, `χ(τ) = η_g(τ)^k`.
- **Count** (`t32a`). Every continuous `χ` is `1` (`k` even) or `η_g` (`k` odd), and `η_g ≠ 1`.
  Hence `Nat.card {χ // Continuous χ} = 2` (`Nat.card_eq_two_iff`).

Wild inertia never appears. A Kummer generator whose valuation has a `p`-power denominator is
covered by the case "`n` odd". Mathlib inputs (VERIFIED by compilation):

- `krullTopology_mem_nhds_one_iff`, `stabilizer_isOpen_of_isIntegral`,
  `Field.exists_primitive_element`, `IntermediateField.lift_adjoin_simple`,
  `IntermediateField.le_iff_le`;
- `Polynomial.mem_aroots`, `Polynomial.aeval_algHom_apply`, `Matrix.det_vandermonde_ne_zero_iff`,
  `Matrix.eq_zero_of_mulVec_eq_zero`;
- `Valuation.map_sum_eq_of_lt`, `pow_left_injective` (from `HasUniqueRoots` for linearly ordered
  monoids with zero), `Nat.exists_eq_pow_mul_and_not_dvd`, `IsAlgClosed.exists_pow_nat_eq`,
  `Nat.card_eq_two_iff`.

From the project's earlier glue: `residue_inertia` (glue-b3-unram), `val_intCast_eq_one`,
`val_natCast_ne_zero`, `smul_sq_cases`,
`liesOver_of_isAtPrime`, `exists_neg_of_sq`, `not_isSquare_of_squarefree`, `exists_inertia_neg`,
`leafB3a_of_t32a` and `unramified_outside_t32a` (glue-b3b), `isLocallyConstant_of_openSubgroup`
(glue-descent).

## What remains

Nothing for T32 or B3 (v). (Integrated since: `ZInQKernel/HDecomp/B3Unram/T32a.lean`, and
`HSyn.t32a_glue` in `Leaves.lean`.) The original plan: for integration, `ZInQKernel/HDecomp/` would need the content of
`T32a.lean` as a module (it already contains glue-b3-unram, glue-conj and glue-b3b). The `LeafPush`
definitions would then be imported from the Leaves module instead of copied, and the field
`TextbookLeaves.t32a` (and `t32b`) would be filled by `GlueB3Unram.t32a` (`GlueB3Unram.t32b`). No
file under `ZInQKernel/` or `blueprint/` was edited.

The published source, now only as a cross-check: Serre, *Corps locaux* IV §2 (tame inertia is
`∏_{ℓ≠p} ℤ_ℓ(1)`, wild inertia is pro-`p`); locator UNVERIFIED.
