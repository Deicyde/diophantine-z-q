# glue-a6-alg: the A6 glue is finished in Lean

## Verdict

**A6 (Lemma PR(ii), Raynaud route) now follows in Lean from the three I2 leaves alone:**
`NeronOggShafarevich`, `RaynaudCriterion` and `TorsionStructure`. Both open glue items that
rv-a6-route left are proved:

1. `QuatUnipotentTrivial`, the pure-algebra statement, is now the theorem
   `GlueA6Alg.quatUnipotentTrivial`.
2. The existence of a valuation subring of `K̄` lying over a given valuation subring of `K` is
   `GlueA6Alg.Alg.exists_valuationSubring_comap_eq`. It holds for any field extension `L/K` and is
   derived from Mathlib's Chevalley extension theorem.

All of this is VERIFIED: it compiles with `lake env lean`, contains no `sorry`, and
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]`.

| Lean declaration | File | Hypotheses |
|---|---|---|
| `GlueA6Alg.core` | scratch/glue-a6-alg/Quat.lean | none (pure algebra over `(ℤ/3^{2k})⁴`) |
| `GlueA6Alg.quatUnipotentTrivial : QuatUnipotentTrivial` | Quat.lean, A6.lean | none |
| `GlueA6Alg.exists_valuationSubring_comap_eq` | Extend.lean (and in A6.lean, under `Alg`) | none |
| `GlueA6Alg.goodReduction_of_QM_rational3` | A6.lean | `hNOS hRay hTors` + rv-a6-route's data, including `w, hw` |
| `GlueA6Alg.goodReduction_of_QM_rational3'` | A6.lean | `hNOS hRay hTors`, with no `w` and no `hw` |

`scratch/glue-a6-alg/A6.lean` is `scratch/rv-a6-route/A6.lean` with these changes only (checked
with `diff`):

- the namespace `RvA6` is renamed `GlueA6Alg`;
- `import Mathlib` is added;
- rv's theorem that takes `hAlg` is renamed `goodReduction_of_QM_rational3_of_alg`;
- the new declarations listed above are added.

The leaf definitions (`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, …) and the
definition `QuatUnipotentTrivial` are copied unchanged. The conclusion is the same, `HasGoodReduction A O`.

## 1. Proof of `QuatUnipotentTrivial` (as formalized)

The proof follows rv-a6-route §3, but replaces steps 1–2 (the count `|T/JT| = 9`) with a shorter
argument that needs no cardinality of quotients.

Setting (`core`): `V = Fin 4 → ZMod q` with `q = 3^{2k}` and `k ≥ 1`. The maps `I, J, S` are
`ZMod q`-linear and satisfy:

- `I² = 2`, `J² = −3`, `JI = −IJ`;
- `SI = IS` and `SJ = JS`;
- `S² − 2S + 1 = 0`.

Conclusion: `S v = v` whenever `3^k v = 0`.

1. **A generator mod 3.**
   - Some `x` has `Jx ≢ 0 (mod 3)`.
   - Otherwise `J e₀ = 3u` and `J u = 3u'`, so `−3e₀ = J²e₀ = 9u'`. Reading coordinate 0 in
     `ZMod 9` gives `−3 = 0`, which is false (`decide`).
2. **Independence over 𝔽₃ (`f3_indep`).**
   - Let `Ī, J̄` be the reductions mod 3 (the matrices of `I, J` mapped by `ZMod.castHom`). They
     satisfy `Ī² = 2`, `J̄² = 0`, `J̄Ī = −ĪJ̄`.
   - Suppose `J̄x̄ ≠ 0` and `a x̄ + b Īx̄ + c J̄x̄ + d ĪJ̄x̄ = 0`.
   - Applying `J̄`, then `Ī`, gives `(a² − 2b²) J̄x̄ = 0`. Since `a² − 2b²` is anisotropic mod 3
     (`decide`), `a = b = 0`. In the same way, `c = d = 0`.
   - So these four vectors form a basis of `𝔽₃⁴` (`LinearIndependent.span_eq_top_of_card_eq_finrank`).
3. **Nakayama.**
   - By induction on `n`, every `u ∈ V` is `φ_x(a) + 3ⁿu'`, where
     `φ_x(a) = a₀x + a₁Ix + a₂Jx + a₃IJx`.
   - At `n = 2k` the term `3^{2k}u'` vanishes, so `φ_x : (ZMod q)⁴ → V` is surjective.
   - It is therefore injective (`Finite.injective_iff_surjective`). So `V` is free of rank one over
     `Λ/q` on `x`.
4. **`S − 1` is right multiplication.**
   - Write `Sx − x = φ_x(a)`. Because `S` commutes with `I` and `J`, `(S − 1)φ_y(α) = φ_{(S−1)y}(α)`.
   - Hence `0 = (S − 1)²x = φ_{φ_x(a)}(a) = φ_x(a₀² + 2a₁² − 3a₂² + 6a₃², 2a₀a₁, 2a₀a₂, 2a₀a₃)`.
     This is the square in `Λ`, expanded by `simp` with the relations and closed by `module`.
   - By injectivity, `q` divides each of these four coordinates.
5. **Valuation step.**
   - `RvA6.quat_sq_dvd`, copied verbatim from scratch/rv-a6-route/QuatVal.lean, gives `3^k ∣ aᵢ`.
     So `a = 3^k a'`.
6. **Conclusion.**
   - Let `v = φ_x(α)` with `3^k v = 0`. By injectivity, `3^k α = 0`.
   - Then `(S − 1)v = φ_{3^k φ_x(a')}(α) = φ_{φ_x(a')}(3^k α) = 0`.

**Transport (`quatUnipotentTrivial`).**

- Let `e : G[q] ≃ (ZMod q)⁴` be the additive bijection in the hypothesis. Extend `e` by `0` outside
  `G[q]`; call the result `E`. `E` is additive on `G[q]`, sends powers to multiples and inverses to
  negatives, and is injective on `G[q]`.
- Each group endomorphism `f` becomes the additive map `v ↦ E(f(e⁻¹v))`. This map is automatically
  `ZMod q`-linear (`AddMonoidHom.toZModLinearMap`).
- The multiplicative hypotheses then become the linear relations of `core`.
- `x^{3^k} = 1` implies `x ∈ G[q]` and `3^k E(x) = 0`.

## 2. Extension of valuation rings

`exists_valuationSubring_comap_eq`: for fields `K ⊂ L` (any `[Algebra K L]`) and any
`O : ValuationSubring K`, there is a `w : ValuationSubring L` with `w.comap (algebraMap K L) = O`.

- **Source.** Mathlib's `IsLocalRing.exists_factor_valuationRing`
  (Mathlib/RingTheory/Valuation/LocalSubring.lean) gives a valuation subring `B` of `L` that
  dominates the image of `O`. That theorem rests on `LocalSubring.exists_le_valuationSubring`,
  tagged `@[stacks 00IA]`, which uses Zorn's lemma. VERIFIED by reading.
- **`O ⊆ B ∩ K`.** This is the factorization.
- **`B ∩ K ⊆ O`.** Take `x ∈ B ∖ O`. Then `x⁻¹ ∈ O` is a nonunit of `O`. Its image is a unit of
  `B`, with inverse `x`. This contradicts `IsLocalHom`.

Consequence: in A6, the auxiliary `w` lying over `O`, which rv-a6-route listed as "not formalized",
is no longer a hypothesis (`goodReduction_of_QM_rational3'`).

## 3. What remains

Nothing remains open for A6 as stated by rv-a6-route. The leaves `NeronOggShafarevich`,
`RaynaudCriterion` and `TorsionStructure` are unchanged; their faithfulness was reviewed by
rv-a6-route and pkg-I2, not here. The integration into `ZInQKernel/` is left to the integrators,
as instructed.
