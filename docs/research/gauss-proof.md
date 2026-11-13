# gauss-proof: Gauss's point count, and `ZInQ.Contrib.functionalEquation5`

## Main result (VERIFIED: compiled, no `sorry`)

```lean
theorem ZInQ.Contrib.functionalEquation5 : ZInQ.Literature.FunctionalEquation5
```

in `ZInQKernel/Contrib/GaussFE/FunctionalEquation5.lean`. The type is exactly the hypothesis:
`example : ZInQ.Literature.FunctionalEquation5 := ZInQ.Contrib.functionalEquation5` elaborates.
The proof takes no hypotheses.

```
#print axioms ZInQ.Contrib.functionalEquation5
'ZInQ.Contrib.functionalEquation5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`scratch/gauss-proof/axioms.lean` → `scratch/gauss-proof/out_axioms.txt`.)

The proof is bp-hecke-fe's reduction `literature_hecke_fe_of_gaussPointCount : GaussPointCount →
HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5` together with a new Lean proof of its one
hypothesis:

```lean
theorem ZInQ.Contrib.GaussFE.gaussPointCount : GaussPointCount
-- GaussPointCount, verbatim from scratch/bp-hecke-fe/HeckeFE.lean:
--   ∀ p : ℕ, p.Prime → p % 4 = 1 →
--     (p : ℂ) - (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℂ) =
--       (1 / 4) * ∑ q ∈ normFiber p, unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) * gz 0 0 q
```

This is Gauss's theorem (1814) on `y² = x³ − x`. Textbook source: Ireland–Rosen, *A Classical
Introduction to Modern Number Theory*, Ch. 18 §4 for the count, Ch. 8 for Jacobi sums, and Ch. 9 §9 for
the congruence of quartic Jacobi sums (STANDARD; section numbers from memory, UNVERIFIED). The
Lean proof does not use these chapters as a black box. It proves the congruence directly; see the
Proof section below.

**Consequence (VERIFIED, compiled; standard axioms):** `ZInQKernel/Contrib/GaussFE/Headline.lean`
proves

```lean
theorem ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier
    (hH : ZInQ.SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA)
    (hG : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget
theorem ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzInputs_grossZagier
    (hH : ZInQ.SixContactMin) (hT : ZInQ.PropN.TYZInputs)
    (hG : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget
theorem ZInQ.Contrib.GaussFE.certifiedRankTYZClRk_of_readingA_grossZagier
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hG : ZInQ.Literature.GrossZagier) :
    ZInQ.RouteK.Rank.CertifiedRankTYZClRk
```

So Theorem 1.1 now needs only H = `SixContactMin`, `TYZThm35ReadingA` (or `PropN.TYZInputs`) and
`GrossZagier`. `HeckeContinuation` is not needed, because the headline only uses its case
`d ≡ 5 (mod 8)` squarefree, which bp-hecke-fe proves (`HeckeContinuation5`). The provider
`ZInQ.Contrib.heckeContinuation` itself is **not** closed: `Literature.HeckeContinuation` quantifies
over every `d ≠ 0`, and only odd squarefree `d ≡ 1 (mod 4)` is covered (`deuringCd_of_gaussPointCount`).

## Files (all new; nothing imports them)

| file | imports | content |
|---|---|---|
| `ZInQKernel/Contrib/GaussFE/HeckeFE.lean` | Mathlib, `ZInQKernel.RouteK.Rank.LFunctionCd`, `ZInQKernel.Hypotheses.CR3Literature` (both on the baseline list) | verbatim copy of `scratch/bp-hecke-fe/HeckeFE.lean`. The only change is the namespace, `BpHeckeFE` → `ZInQ.Contrib.GaussFE` (checked by `diff`) |
| `ZInQKernel/Contrib/GaussFE/Gauss.lean` | Mathlib only | Gauss's count via the quartic Jacobi sum (`gauss_jacobi`) |
| `ZInQKernel/Contrib/GaussFE/FunctionalEquation5.lean` | the two above | `gaussPointCount`, `literature_hecke_fe`, `ZInQ.Contrib.functionalEquation5` |
| `ZInQKernel/Contrib/GaussFE/Headline.lean` | `ZInQKernel.MainLiterature` (baseline), FunctionalEquation5 | the three theorems above |

Each file was checked with `lake env lean` and `lake build <module>`, with no errors. The check
files are `scratch/gauss-proof/axioms*.lean` and their outputs are `out_axioms*.txt`. No existing
file was edited: `git diff --stat 01267822` lists only new files.

## The proof (`Gauss.lean`, 408 lines)

Fix a prime `p ≡ 1 (mod 4)`.

1. **Quartic character** (`exists_quartic`). `χ : MulChar (ZMod p) ℤ[i]` of order 4, from Mathlib's
   `MulChar.exists_mulChar_orderOf`, since `i` is a primitive 4th root of unity in `ℤ[i]`
   (`isPrimitiveRoot_gI`). The values are `0` or units with `u⁴ = 1`, i.e. `±1, ±i`
   (`pow_four_eq_one_cases`).
2. **`χ²` is the quadratic character** (`quadraticChar_eq_chi_sq`). Both send a generator `g` of
   `(ZMod p)ˣ` to `−1`: for `χ²` because `χ² ≠ 1`, and for the quadratic character because
   `g^((p−1)/2) ≠ 1` (Mathlib's `quadraticChar_eq_pow_of_char_ne_two'`).
3. **Count to Jacobi sums.** First, `#{y² = x³ − x} = p + Σ_x (x³ − x / p)` (`card_cubic_eq`). Next,
   `χ(x³ − x)² = χ(x²) χ(1 − x²)²`, and the substitution `t = x²` has fibres of size `1 + χ(t)²`
   (`sum_sq_comp`). Together these give `Σ_x χ(x³ − x)² = J(χ, χ²) + J(χ³, χ²)` (`sum_chi_sq_cubic`).
   Finally, `J(χ³, χ²) = conj J(χ, χ²)` (`jacobi_conj`). So with `J = J(χ, χ²) = A + Bi`, the count
   is `p + 2A`.
4. **Norm** (`jacobi_mul_star`). `J · J̄ = p`. Proof: map along `ℤ[i] ↪ ℂ` and apply Mathlib's
   `jacobiSum_mul_jacobiSum_inv`, using `χ⁻¹ = χ³` and `(χ²)⁻¹ = χ²`. Hence `A² + B² = p`.
5. **Congruence** (`two_add_two_i_dvd_jacobi_add_one`). `(2 + 2i) ∣ J + 1`. Write
   `J = Σ_t f(t)` with `f(t) = χ(t) χ(1 − t)²`.
   - `f(t⁻¹) = f(t)`, using `1 − t⁻¹ = −(1 − t) t⁻¹`, `χ(t⁻¹) = χ(t)³` and `χ(−1)² = 1`.
   - `f(0) = f(1) = 0`.
   - `f(−1) = χ(−1)χ(2)² = 1` (`chi_neg_one_mul_chi_two_sq`): with `r² = −1` in `𝔽_p`,
     `χ(−1)χ(2)² = χ(2r)² = χ((1 + r)²)² = 1`.
   - On `X = 𝔽_p ∖ {0, ±1}` the involution `t ↦ t⁻¹` has no fixed points, each `f(t)` is a unit,
     and `2(u − 1) ∈ (2 + 2i)` for each unit `u`. So `Finset.sum_involution` in
     `ℤ[i]/(2 + 2i)` gives `Σ_X (f − 1) ≡ 0`.
   - Hence `J + 1 = (p − 1) + Σ_X (f − 1) ≡ 0`, because `4 ∣ p − 1` and `(2 + 2i) ∣ 4`.

   In coordinates: `A` is odd and `B ≡ A + 1 (mod 4)`, so `−J` is primary.
6. **Result** (`gauss_jacobi`).
   `∃ A B : ℤ, A² + B² = p ∧ (A+1) % 2 = 0 ∧ (B−A−1) % 4 = 0 ∧ #{y² = x³ − x} = p + 2A`.

`FunctionalEquation5.lean` turns this into `GaussPointCount`.
- `sum_normFiber_prime` (bp-hecke-fe) with `a = |A|`, `b = |B|` gives
  `RHS = ψ₁(π₀) + ψ₁(π̄₀)` (`psiPair`).
- `psiPair` is invariant under `z ↦ −z` and `z ↦ z̄` (`psiPair_neg`, `psiPair_conj`), and
  `π₀ ∈ {±π₁, ±π̄₁}` for the primary `π₁ = −A − Bi`.
- `psiPair π₁ = −2A` (`unitOf_primary`, `psiPair_primary`).
- The left side is `p − (p + 2A) = −2A`.

This route differs from bp-hecke-fe's plan only in step 5. The plan proposed Ireland–Rosen's
`J(χ,χ)` argument, or a count modulo 8. The pairing `t ↦ t⁻¹` acts directly on `J(χ, χ²)` and
needs neither.

## What remains

Nothing remains for this task. Every piece compiled.

Points for the integrator:
- `HeckeFE.lean` (2724 lines) is a copy of bp-hecke-fe's scratch file under a new namespace. If
  bp-hecke-fe is folded in separately, one of the two copies should be dropped.
- `Literature.HeckeContinuation` (all `d ≠ 0`) is still open as a provider. It is not needed for the
  headline (see `Headline.lean`).
- The statements of `ZInQ.Literature.FunctionalEquation5` and `GaussPointCount` are upstream's and
  bp-hecke-fe's. They were not re-audited here beyond the type check above.
