# Removing CAT: an effective Dirichlet theorem

Status: done (2026-11-08). `ZInQ.catalogueBound8 : CatalogueBound8` is proved in
`ZInQKernel/Progressions/`, and the main theorem no longer takes CAT. The plan below is kept as
written; the delivered constants are in the blueprint chapter `progressions/`. When the plan was
written, the main theorem
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of` took four hypotheses. Three of
them (H, PC, 22P) rest on Shimura curves and modularity, the Gross–Zagier–Kolyvagin package
with BCDT, and Green–Tao–Ziegler; none of that is within reach of Mathlib. The fourth, CAT, is a
statement about primes in arithmetic progressions, and the proof uses it with so much room to
spare that a textbook effective Dirichlet theorem suffices. This note plans its replacement by a
theorem.

## What the proof needs from CAT

`CatalogueBound` (`ZInQKernel/Hypotheses/PrimePattern.lean`) says that every unit class modulo
`W = 4·324#` contains at least 22 primes in `(324, 2^(W³))`. The manuscript gets it from the
Bennett–Martin–O'Bryant–Rechnitzer estimate. In Lean it is used only through the cutoff
`X = 2^(W³)`, in four files:

| File | Use |
| --- | --- |
| `Size/Constants/Catalogue.lean` | `cataloguePrime_bounds`, `Hcat_bounds` (`H_cat ≤ X^(22W)`), `Ns_bounds` (`N_s < 2^(2^2054)`), `ell_lt` (`ℓ < 2^(2^2063)`) |
| `Size/Constants/FormalMultiple.lean` | `cstar_lt` (`c_* < 2^(2^2059)`) |
| `Size/Constants/T.lean` | `Hmax_lt_D`, `cstar_lt_D`, `R_eq_D` |
| `Size/Majorants/Cutoff.lean` | `admissible_cutoff` (`c_*` and `ℓ` below `T`) |

Everything downstream sees CAT only through `R = D` and the bounds on `c_*` and `ℓ` below `T`.
`D.lean` proves `2^(2^k) < D` for `k ≤ 8008`, and `T > D`. With a cutoff `X' = 2^(2^K)` and
`W < 2^512`, `P_s < 2^433`:

- `H_cat ≤ X'^(22W) = 2^(22·W·2^K) < 2^(2^(K+517))`;
- `N_s < 2^(2^(K+518))`, `c_* ≤ 4·N_s^10 < 2^(2^(K+523))`, `ℓ < 2^(2^(K+528))`.

So every downstream statement survives, with new numerals, for any `K ≤ 7485`. The plan uses
the cutoff `X₈ = 2^(W^8)`, i.e. `K = 4096`:

- `H_max < 2^(W^8) < 2^(2^4096)`;
- `H_cat ≤ 2^(22·W^9)`, `N_s < 2^(2^4613)`, `c_* < 2^(2^4617)`, `ℓ < 2^(2^4623)`.

**The new hypothesis, then theorem** (`CatalogueBound8`):
every `r < W` coprime to `W` has `22 ≤ #{p ∈ (324, 2^(W^8)) : p prime, p ≡ r (mod W)}`.
`CatalogueBound → CatalogueBound8` is immediate, so the size chain can be rewired to
`CatalogueBound8` before the analytic work lands.

## The theorem to prove

**Effective Dirichlet.** There is an explicit `q₀ ≤ 2^64` such that for every `q ≥ q₀` and every
`a` coprime to `q`, at least 22 primes `p ≡ a (mod q)` satisfy `q² < p < 2^(q^8)`.

The proof below gives `p ≤ exp(C·q^(7/2))` with a modest explicit `C`, so the exponent 8 leaves
room for crude constants. Instantiated at `q = W` (where `W² > 324`), it proves
`CatalogueBound8`.

## Route

Notation: `χ` a Dirichlet character mod `q`, `χ₀` the principal one, `M = log q + 3`,
`S_χ(x) = Σ_{n≤x} χ(n)Λ(n)/n`.

1. **Character sums and L-series bounds (Abel summation).** For `χ ≠ χ₀`:
   `|Σ_{n≤x} χ(n)| ≤ q`; for real `σ ≥ 1` and `N ≥ 3`,
   `|Σ_{n>N} χ(n) n^(-σ)| ≤ 2q/N` and `|Σ_{n>N} χ(n) log n · n^(-σ)| ≤ 2q log N / N`. Hence for
   `σ ∈ [1, 2]`: `|L(σ,χ)| ≤ M`, `|L'(σ,χ)| ≤ M²`, `|L(σ,χ) − L(1,χ)| ≤ (σ−1)M²`, and
   `|Σ_{n≤x} χ(n)/n − L(1,χ)| ≤ 2q/x`. Here `L` is Mathlib's `DirichletCharacter.LFunction`
   (entire for `χ ≠ 1`, equal to the L-series for `re s > 1` by `LFunction_eq_LSeries`); the
   value at 1 is reached as a limit `σ → 1⁺`, never through conditional convergence.
2. **Complex characters** (`χ² ≠ χ₀`): `|L(1,χ)| ≥ 1/(256 M⁷)`. From Mathlib's
   `DirichletCharacter.norm_LSeries_product_ge_one` at `s = 1 + x` (real): `ζ(1+x) ≤ 1 + 1/x`,
   `|L(1+x,χ²)| ≤ M`, `|L(1+x,χ)| ≤ |L(1,χ)| + xM²`. If `|L(1,χ)| ≤ xM²` then
   `1 ≤ 128·x·M⁹`; take `x = 1/(256 M⁹)`.
3. **Real characters** (`χ² = χ₀`, `χ ≠ χ₀`): `L(1,χ) ≥ c·q^(-3/2)` with explicit `c`
   (about `1/40`). Through the Dirichlet class number formula in Mathlib
   (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `NumberField.dedekindZeta_residue`):
   1. *Classification.* There is a squarefree `d ≠ 1` with `|d| ≤ q` (every odd prime factor of
      `d` divides `q`) such that `χ(p) = (d/p)` (Legendre) for every prime `p ∤ 2q`. Proof:
      decompose `χ` over the prime powers of `q`; a real character of `(ℤ/p^k)^×`, `p` odd, is
      trivial or the Legendre symbol; of `(ℤ/2^k)^×`, one of `1, χ₄, χ₈, χ₄χ₈`; then Jacobi
      reciprocity turns the product of Legendre symbols into `(d/·)`.
   2. *The quadratic field* `K = ℚ(√d)` (Mathlib's `QuadraticAlgebra` / `IsQuadraticExtension`):
      a number field of degree 2, `|disc K| ≤ 4|d|` (via the order `ℤ[√d]`), `torsionOrder ≤ 6`,
      regulator `= 1` if `d < 0` and `≥ log((1+√5)/2)` if `d > 1` (a unit `ε > 1` is
      `(a + b√d)/2` with `a, b ≥ 1`).
   3. *Ideal counts.* Let `a_K(n)` be the number of ideals of norm `n`. It is multiplicative. For
      every prime `p` there is `ε_p ∈ {−1, 0, 1}` with `a_K(p^k) = Σ_{j≤k} ε_p^j` (from
      `Σ e_i f_i = 2`), and `ε_p = (d/p)` for odd `p ∤ d` (Kummer–Dedekind for `X² − d`).
   4. *Factorization.* For real `s > 1`:
      `ζ_K(s) = ζ(s) L(s,χ) Π_{p | 2q} (1 − χ(p) p^(-s)) (1 − ε_p p^(-s))^(-1)`
      (`χ(p) = 0` for `p | q`, so only `p = 2 ∤ q` has a nontrivial numerator).
   5. *Lower bound.* Multiply by `s − 1` and let `s → 1⁺`:
      `L(1,χ) = res_K · Π_{p|2q}(1 − ε_p/p)/(1 − χ(p)/p) ≥ res_K/(3q)`, and
      `res_K ≥ log((1+√5)/2)/(6√q)` from `h ≥ 1`, `w ≤ 6` and `|disc K| ≤ 4q`.
4. **Mertens and the residue-class count.**
   1. Mertens' first theorem: `|Σ_{n≤x} Λ(n)/n − log x| ≤ C₀` for `x ≥ 1`, from
      `log ⌊x⌋! = Σ_{d≤x} Λ(d)⌊x/d⌋` and Chebyshev (`Chebyshev.psi_le`).
   2. For `χ ≠ χ₀`: with `T(x) = Σ_{n≤x} χ(n) log n / n` and `log n = Σ_{d|n} Λ(d)`,
      `L(1,χ) S_χ(x) = T(x) + Σ_{d≤x} χ(d)Λ(d)/d · R(x/d)` with `|R(y)| ≤ 2q/y`, so
      `|S_χ(x)| ≤ (M² + 2q·ψ(x)/x)/|L(1,χ)|`, which is at most `C₁ q^(5/2)` by steps 2 and 3.
   3. Orthogonality (`DirichletCharacter.sum_char_inv_mul_char_eq`): for
      `S_a(x) = Σ_{n≤x, n≡a} Λ(n)/n`,
      `S_a(x) − S_a(y) ≥ (log(x/y) − 2C₀ − 2 log q)/φ(q) − 2C₁q^(5/2)`.
   4. Prime powers `p^k` (`k ≥ 2`) above `y` contribute `O(log y/√y)`, and each prime above `y`
      contributes at most `log y / y`. With `y = q^8` and `log(x/y) ≥ 5C₁ q^(7/2)`, at least 22
      primes `≡ a` lie in `(y, x]`.
5. **Instance and rewiring.** Instantiate at `q = W`; restate the four size files against
   `CatalogueBound8` with the numerals above; remove `hCAT` from `Pstar_spec`, `assembly` and
   the main theorems. The main theorem then takes H, PC and 22P.

## Mathlib (v4.35.0) inventory

Available:
- Dirichlet characters, orthogonality, `LFunction` (entire for `χ ≠ 1`), `LFunction_eq_LSeries`,
  `LFunction_apply_one_ne_zero`, `norm_LSeries_product_ge_one`;
- Dirichlet's theorem without a bound (`Nat.forall_exists_prime_gt_and_eq_mod`);
- `vonMangoldt`, `vonMangoldt_sum`, Chebyshev `θ` and `ψ` bounds;
- Abel summation (`NumberTheory/AbelSummation.lean`);
- `NumberField.dedekindZeta`, the class number formula, `regulator`, `classNumber`,
  `torsionOrder`, Kummer–Dedekind;
- `QuadraticAlgebra` (discriminant, `IsQuadraticExtension`), `Int.IsFundamentalDiscr`;
- Legendre and Jacobi symbols with reciprocity, `χ₄`, `χ₈`.

Missing, to be written:
- Mertens' first theorem;
- explicit L-series bounds near `s = 1`;
- quantitative non-vanishing;
- ideal counts in quadratic fields;
- the real quadratic regulator bound;
- the classification of real characters.

## Organization

- **Lean:** a new directory `ZInQKernel/Progressions/`, importing only Mathlib (and, for the
  final instance, `Hypotheses/PrimePattern`), so its builds stay short.
- **Blueprint:** a new chapter `blueprint/roadmap/progressions/`, with `origin: background`
  articles citing the textbook sources (Apostol, *Introduction to Analytic Number Theory*,
  ch. 6–7; Davenport, *Multiplicative Number Theory*; Marcus, *Number Fields*, ch. 7, which
  Mathlib's class number formula follows).
- **Agents:** independent strands are 1, 3.1, 3.2, 3.3, 4.1 and 5 (the rewiring against
  `CatalogueBound8`). Then 2 after 1, 3.4–3.5 after 3.1–3.3, and 4.2–4.4 after 2 and 3.

## Risks

- **Quadratic fields (3.2–3.4)** are the largest strand: Mathlib has the class number formula
  but no ideal counts for quadratic fields. If the ring-of-integers route stalls, an
  alternative is to work in the order `ℤ[√d]` only where an upper bound on `|disc K|` is needed.
- **The classification (3.1)** for `p = 2` has four cases. It needs to hold only for primes
  `p ∤ 2q`, which keeps the 2-adic splitting law out of 3.3.
- **Constants.** Every constant must be explicit. The exponent 8 leaves room for losses up to
  roughly `exp(q^7)`.
