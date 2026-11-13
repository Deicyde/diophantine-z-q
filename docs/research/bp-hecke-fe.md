# bp-hecke-fe: blueprint for `HeckeContinuation` and `FunctionalEquation5`

Status: task bp-hecke-fe, 2026-11-12, base fork main `27875ecf`. Lean: `scratch/bp-hecke-fe/HeckeFE.lean`
(compiled with `lake env lean`, no `sorry`, `#print axioms` = `propext, Classical.choice, Quot.sound`).
Log: `scratch/bp-hecke-fe/log.md`. Marks: VERIFIED (compiled, computed or read here), STANDARD
(published, reference given), SPECULATIVE; theorem numbers quoted from memory are UNVERIFIED.

## 0. Main result

**Both literature Props are proved in Lean from one classical theorem, Gauss's point count on
`y² = x³ − x`** (VERIFIED: compiled, no `sorry`, `#print axioms` = `propext, Classical.choice,
Quot.sound`):

```lean
theorem BpHeckeFE.literature_hecke_fe_of_gaussPointCount (h1 : GaussPointCount) :
    HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5

def BpHeckeFE.GaussPointCount : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 →
    (p : ℂ) - (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℂ) =
      (1 / 4) * ∑ q ∈ normFiber p, unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) * gz 0 0 q
```

`ZInQ.Literature.FunctionalEquation5` is the project's Prop itself: conductor `32d²`, root number
`−1`, on the strip `0 < Re s < 2`. `HeckeContinuation5` is `Literature.HeckeContinuation`
restricted to squarefree `d ≡ 5 (mod 8)`. That restriction is all the headline uses:
`tyzRow5b_of_readingA_five : TYZThm35ReadingA → HeckeContinuation5 → TYZRow5b` is proved. CR₃ follows
from TYZ reading A, Gross–Zagier and `GaussPointCount` (`certifiedRankTYZClRk_of_gaussPointCount`).

**The leaf.** `GaussPointCount` says: for every prime `p ≡ 1 (mod 4)`,
`p − #{(x, y) ∈ 𝔽_p² : y² = x³ − x} = π + π̄`. Here `p = ππ̄` in `ℤ[i]` and `π ≡ 1 (mod 2 + 2i)` is
primary. The right-hand side is written as `¼ Σ_{a² + b² = p} u(a + bi)(a + bi)`, where `u` is the
16-entry table `unitOf` (8 unit entries on `(ℤ/4)²`, 0 elsewhere). This is Gauss's theorem (1814). In textbook form it is Ireland–Rosen,
*A Classical Introduction to Modern Number Theory*, Ch. 18 §4, the point count of
`y² = x³ − Dx` with `D = 1` (STANDARD; theorem number UNVERIFIED). It is refereed and classical,
and it mentions only `𝔽_p`, `ℤ²` and a finite table: no elliptic-curve library, no L-function.
Numerically VERIFIED at the 29 primes `p ≡ 1 (mod 4)` below 300 (`remaining_check.py`).

Proof plan for a Lean proof (tier M; the steps are numerically VERIFIED for 10 primes in
`gauss_jacobi_check.py`). Let `χ₄` be a quartic character of `𝔽_p^×` with values in `ℤ[i]`
(Mathlib: `MulChar.exists_mulChar_orderOf`), and let `χ₂ = χ₄²`.
1. `Σ_{x² = u} χ₂(x) = χ₄(u) + χ̄₄(u)` and `χ₂(−1) = 1`. Hence
   `S := Σ_x χ₂(x³ − x) = J(χ₄, χ₂) + J(χ̄₄, χ₂) = 2 Re J`, where `J = J(χ₄, χ₂)` is the Jacobi sum.
   The point count is then `N = p + S` (`card_cd_affine_eq` with `d = 1`).
2. `N(J) = p` (Mathlib `jacobiSum_mul_jacobiSum_inv`), so `J ∈ U·π ∪ U·π̄`. This description of the
   elements of norm `p` is proved inside `sum_normFiber_prime`.
3. `−J` is primary, `J ≡ −1 (mod 2 + 2i)`. Mathlib's `exists_jacobiSum_eq_neg_one_add` gives
   `J ≡ −1 (mod (i − 1)²) = (mod 2)`; one more factor of `(1 + i)` is needed (Ireland–Rosen Ch. 9 §9,
   the congruence for quartic Jacobi sums; UNVERIFIED locator). Then `S = −(π + π̄)` for the primary
   `π = −J`, which is `GaussPointCount` once `heckeCoeff 1 p = π + π̄` (from `sum_normFiber_prime` and
   `psi_gmul_unit`). An alternative for the sign (SPECULATIVE, checked by hand only): steps 1–2 give
   `S = ±2a`. The sign follows from `#E(𝔽_p) = N + 1 ≡ 0 (mod 8)`, because `p ≡ 1 + b² (mod 8)`. For the
   count, the maps `σ(x, y) = (−x, iy)` and `τ(x, y) = (−1/x, y/x²)` commute and generate a group of
   order 8 acting on the points with `y ≠ 0`. `σ` acts freely, and only `σ²τ` has fixed points: the four
   points with `x = ±i`, `y² = ∓2i`, which exist because `2i = (1 + i)²`. So `N − 3 ≡ 4 (mod 8)`.

Or the team can take it as a leaf.

Everything else is proved, including the `ℤ[i]` arithmetic: `heckeMult` (multiplicativity, by gcd
and Bezout; the fibres of `(α, β) ↦ αβ` have four elements) and `heckePrimePowSplit` (the Hecke
relation at split primes, from `A_p = U·π ⊔ U·π̄`).

Intermediate forms are also proved: `literature_hecke_fe_of_split_gaussPointCount`,
`literature_hecke_fe_of_mult_split_gaussPointCount`
(with `HeckeMult` as a hypothesis), `literature_hecke_fe_of_heckeEuler_gaussPointCount` (`HeckeEuler`
instead of `HeckeMult ∧ HeckePrimePowSplit`), and `literature_hecke_fe_of_heckeEuler_gaussSplit`
(`GaussSplit 1`, phrased through `cdCoeff 1 p`).

Two consequences are worth naming: `heckeEuler_of_odd` (the Euler product of `L(ψ_d, s)` for odd
squarefree `d`, proved outright) and `deuringCd_of_gaussPointCount` (Deuring's identity
`L(C_d, s) = L(ψ_d, s)`, coefficientwise, for squarefree `d ≡ 1 (mod 4)`, from `GaussPointCount`).
The Hecke coefficients are defined explicitly (`normFiber n` is the finset of `(a, b) ∈ ℤ²` with
`a² + b² = n`, `gz 0 0 (a, b) = a + bi`, `unitOf` is the table of §2.1):

```lean
noncomputable def heckeCoeff (d n : ℕ) : ℂ :=
  (1 / 4) * ∑ p ∈ normFiber n,
    (jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) * unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) * gz 0 0 p

def DeuringCd (d : ℕ) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ((ZInQ.Literature.cdCoeff d n : ℤ) : ℂ) = heckeCoeff d n
```


**How the Props reduce** (all proved in `scratch/bp-hecke-fe/HeckeFE.lean`):

1. **Analysis: no Hecke characters, adeles or Poisson summation on `ℝ²`.** The weight-two theta
   series of a shifted copy of `ℤ[i]` factors through Mathlib's one-variable Hurwitz kernels:
   `Σ_{(m,n)∈ℤ²} ((m+a) + i(n+b)) e^{−π((m+a)²+(n+b)²)x} = oddKernel a · evenKernel b + i · evenKernel a · oddKernel b`.
   So the transformation law (weight 2), the Mellin transform, the entireness and the functional
   equation all come from `Mathlib.NumberTheory.LSeries.{HurwitzZetaEven, HurwitzZetaOdd,
   AbstractFuncEq, MellinEqDirichlet}`. Lean: `twistedL_continuation` (for every
   `c : (ℤ/M)² → ℂ`, `Σ_α c(α) α N(α)^{−s}` is entire) and `lambdaC_two_sub` (its functional
   equation whenever the finite Fourier transform of `c` satisfies a relation `FourierRel`).
2. **Deuring's identity** `DeuringCd d`: `cdCoeff d n = heckeCoeff d n`. Here `cdCoeff` is the
   project's `LFunctionCd.lean` coefficient sequence of Mathlib's `L(C_d, s)`, so the identity says
   `L(C_d, s) = L(ψ_d, s)`. It gives `HeckeContinuation5` (`heckeContinuation5_of_deuring`). It follows
   from the Euler product `HeckeEuler d` (proved: `heckeEuler_of_odd`, from `heckeMult` and the
   prime-power recursion) plus agreement at the primes (`deuringCd_of_heckeEuler`). The primes
   `p ≡ 3 (mod 4)`, `p ∣ d` and `p = 2` are proved by point counts. The split primes reduce to `d = 1`
   by a quadratic twist and reciprocity (`gaussSplit_of_one`), and then to `GaussPointCount`.
3. **The functional equation**: `CdFourier d` (the finite Fourier transform of the character data
   on `(ℤ/4d)²`) gives `FunctionalEquation5` with `DeuringCd`. The constants were checked in Lean
   (`const_identity`), and the root number is `(2/d) = −1`. `CdFourier d` is **proved**. It factors by
   CRT into a 2-part, proved by `decide` (`g2G_table`), and the odd part `OddGauss d`. `OddGauss` is
   multiplicative (`oddGauss_mul`); at an odd prime it is the two-dimensional quadratic Gauss sum
   `gauss2D`, proved from Mathlib's `gaussSum_sq` and `gaussSum_mulShift_eq` by completing the
   square.

**CR₃ without the two textbook Props** (VERIFIED, compiled): `certifiedRankTYZClRk_of_gaussPointCount :
TYZThm35ReadingA → GrossZagier → GaussPointCount → RouteK.Rank.CertifiedRankTYZClRk`. Composed with the existing
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk`
(`RouteK/RankVariants.lean`), this gives the headline with `HeckeContinuation` and
`FunctionalEquation5` replaced by `GaussPointCount`. That last composition is one line but was not
compiled here, because the `RankVariants` olean chain was out of date in this worktree.

**Suggested change on integration.** `Literature.HeckeContinuation` quantifies over every
`d ≠ 0`, but its only use (`tyzRow5b_of_readingA`) is at squarefree `d ≡ 5 (mod 8)`. Replacing it
by `HeckeContinuation5` loses nothing for the headline (`tyzRow5b_of_readingA_five`). It also
avoids even and non-squarefree `d`, where `LSeries_cd_eq` is not available: even `d` changes the
conductor and the character at 2.

## 1. What Mathlib v4.35 has (VERIFIED by reading `.lake/packages/mathlib`)

| Need | Mathlib | Notes |
| --- | --- | --- |
| Mellin functional-equation framework | `NumberTheory/LSeries/AbstractFuncEq.lean`: `WeakFEPair` (`f g k ε f₀ g₀`, `h_feq : f (1/x) = (ε x^k) • g x`, rapid decay), `IsStrongFEPair` (`f₀ = g₀ = 0`), `Λ`, `differentiable_Λ₀`, `functional_equation : Λ (k − s) = ε • symm.Λ s`, `IsStrongFEPair.Λ_eq : Λ = mellin f`, `IsStrongFEPair.differentiable_Λ`, residues | exactly what is needed; weight `k` arbitrary real |
| 1-D theta kernels | `HurwitzZetaEven.lean`: `evenKernel`, `cosKernel`, `evenKernel_functional_equation` (`evenKernel a x = x^{−1/2} cosKernel a (1/x)`), `hasSum_int_evenKernel`, `hasSum_int_cosKernel`, `isBigO_atTop_evenKernel_sub`, `isBigO_atTop_cosKernel_sub`. `HurwitzZetaOdd.lean`: `oddKernel`, `sinKernel`, `oddKernel_functional_equation` (`x^{−3/2}`), `hasSum_int_oddKernel`, `hasSum_int_sinKernel`, `isBigO_atTop_oddKernel` | the product of an odd and an even kernel has weight `3/2 + 1/2 = 2` |
| Mellin = Dirichlet series | `MellinEqDirichlet.lean`: `hasSum_mellin`, `hasSum_mellin_pi_mul` (any index type) | used with index `ℤ × ℤ` |
| Completed Riemann/Hurwitz/Dirichlet L-functions | `HurwitzZeta*.lean`, `ZMod.lean` (`ZMod.LFunction`, `completedLFunction`, `LFunction_one_sub`), `DirichletContinuation.lean` | templates; not used directly (they are 1-dimensional) |
| Jacobi theta | `ModularForms/JacobiTheta/TwoVariable.lean` (`jacobiTheta₂`, `jacobiTheta₂_functional_equation`) | underlies the kernels |
| Lattice sums | `Algebra/Module/ZLattice/Summable.lean`: `ZLattice.summable_norm_sub_rpow` (`Σ_{z∈L} ‖z − x‖^r`, `r < −rank`); `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`: `PeriodPair`, `lattice`, `latticeEquivProd` | gives absolute convergence for `Re s > 3/2` |
| Gaussian integers | `Zsqrtd/GaussianInt.lean`, `Zsqrtd/QuadraticReciprocity.lean` (`GaussianInt.prime_of_nat_prime_of_mod_four_eq_three`), `SumTwoSquares.lean` (`Nat.Prime.sq_add_sq`) | Euclidean domain; splitting of primes |
| Gauss and Jacobi sums | `GaussSum.lean` (`gaussSum_sq` for quadratic characters), `JacobiSum/Basic.lean` (`jacobiSum`, `jacobiSum_mul_jacobiSum_inv` = `#F`, `exists_jacobiSum_eq_neg_one_add`: `J(χ,ψ) = −1 + z(μ−1)²`) | ingredients of Gauss's point count; the congruence modulo `(1+i)³` (primary) is not there |
| Jacobi symbol | `LegendreSymbol/JacobiSymbol.lean` (`jacobiSym`, `mod_left'`, reciprocity) | `χ_d(n) = (n/d)` |
| L-series of an elliptic curve | `AlgebraicGeometry/EllipticCurve/LFunction.lean` (`WeierstrassCurve.LSeries`, `LFunction`, `localPolynomial`) | project: `ZInQKernel/RouteK/Rank/LFunctionCd.lean`, `LSeries_cd_eq` (odd squarefree `d`: `L(C_d,s) = LSeries (cdCoeff d) s`), `LFunction_cd_apply_prime_eq_sub_card` |
| Dedekind zeta | `NumberField/DedekindZeta.lean` (definition and residue; no continuation) | not needed |
| Absent | Hecke characters (Größencharaktere), their L-functions, Deuring's theorem, quartic residue symbol, theta series of number fields beyond `ℚ`, Poisson summation on `ℝ²` | all avoided by the route below |

## 2. The mathematics of the route

Notation: `M = 4d`, `d` odd squarefree, `d ≡ 1 (mod 4)` (this covers `d ≡ 5 (mod 8)`).
`N(α) = αᾱ` for `α ∈ ℤ[i] = ℤ²`, `χ_d(n) = (n/d)` (Jacobi), `e(x) = exp(2πix)`.

### 2.1 The Hecke character (Deuring)

For `α = a + bi` with `a + b` odd, let `u(α) ∈ {±1, ±i}` be the unit with `u(α)α ≡ 1 (mod 2+2i)`.
It depends only on `(a, b) mod 4`: `(1,0), (3,2) ↦ 1`; `(3,0), (1,2) ↦ −1`; `(0,3), (2,1) ↦ i`;
`(0,1), (2,3) ↦ −i`. Set `u(α) = 0` if `(1+i) ∣ α` (Lean: `unitOf`). Then
`ψ_d(α) = χ_d(N α) u(α) α` is a function of the ideal `(α)`. It is the Hecke character of
`ℚ(i)` of `∞`-type `z ↦ z` and conductor `(2+2i)d`, and Deuring's theorem for `C_d` reads

  `L(C_d, s) = L(ψ_d, s) = ¼ Σ_{α ∈ ℤ[i]} c_d(α) α N(α)^{−s}`,  with `c_d(α) = χ_d(Nα) u(α)`,

that is, coefficientwise, `a_n(C_d) = heckeCoeff d n` (Lean: `DeuringCd d`). At a prime:
- `p ≡ 3 (mod 4)`, `p ∤ d`: `a_p = 0` (the involution `x ↦ −x`), and `ψ_d(p) = −p` (`u(p) = −1`),
  so the Euler factor `(1 + p^{1−2s})^{−1}` matches.
- `p = ππ̄ ≡ 1 (mod 4)`, `π ≡ 1 (mod 2+2i)`, `p ∤ d`: `a_p = (d/p)(π + π̄) = ψ_d(π) + ψ_d(π̄)`. This is Gauss's
  theorem; for `D = d²` the quartic symbol `(D/π)₄` becomes `(d/p)` (STANDARD, Ireland–Rosen
  Ch. 18 §4). With reciprocity, `(d/p) = (p/d) = χ_d(N π)` because `d ≡ 1 (mod 4)`.
- `p ∣ 2d`: both sides are `0`.

### 2.2 Theta kernels (Lean: `gaussTheta`, `gaussThetaDual`)

For `a, b ∈ ℝ/ℤ`:
`gaussTheta a b x = oddKernel a x · evenKernel b x + i · evenKernel a x · oddKernel b x`,
`gaussThetaDual a b x = sinKernel a x · cosKernel b x + i · cosKernel a x · sinKernel b x`.
The 1-D functional equations give `gaussTheta a b (1/x) = x² · gaussThetaDual a b x`. Both are
`O(e^{−cx})` at `∞` (odd kernels decay, even kernels are bounded). So
`(gaussTheta a b, gaussThetaDual a b)` is a strong FE-pair with `k = 2`, `ε = 1`, its Mellin
transform `Λ_{a,b}` is entire, and `Λ_{a,b}(2 − s) = Λ^dual_{a,b}(s)`.

### 2.3 Mellin transform and continuation

`gaussTheta a b x = Σ_{p ∈ ℤ²} z_p e^{−π N_p x}` with `z_p = (p₁+a) + i(p₂+b)`, `N_p = |z_p|²`
(a product of absolutely convergent 1-D sums). `hasSum_mellin_pi_mul` with the lattice bound
`Σ |z_p|^{1−2σ} < ∞` (`σ > 3/2`) gives
`Λ_{a,b}(s) = π^{−s} Γ(s) Σ_p z_p N_p^{−s}`. So the shifted lattice series has the entire
continuation `π^s Γ(s)^{−1} Λ_{a,b}(s)` (`1/Γ` is entire). Splitting `ℤ² = ⊔_{j ∈ (ℤ/M)²} (j + Mℤ²)`:

  `T_c(s) := Σ_{α ∈ ℤ²} c(α mod M) α N(α)^{−s} = Σ_j c(j) · M · (M²)^{−s} · L_{j/M}(s)`,

so `T_c` is entire for every `c : (ℤ/M)² → ℂ`. Grouping by `N(α) = n` gives
`T_c(s) = Σ_n (Σ_{N α = n} c(α) α) n^{−s}`; with `c = c_d/4` and `DeuringCd` this is `L(C_d, s)`.

### 2.4 The functional equation (in Lean modulo `DeuringCd`)

Let `Θ(x) = Σ_j c_d(j) gaussTheta(j/M)(x)`, so `Θ(y) = M^{−1} Σ_α c_d(α) α e^{−πN(α)y/M²}`. The dual
kernel is `gaussThetaDual a b x = −i Σ_{ν ∈ ℤ²} ν e(aν₁ + bν₂) e^{−πN(ν)x}`, from `hasSum_int_sinKernel` and
`hasSum_int_cosKernel`. Hence

  `Σ_j c_d(j) gaussThetaDual(j/M)(x) = −i Σ_ν ĉ_d(ν) ν e^{−πN(ν)x}`,  with `ĉ_d(ν) = Σ_{j ∈ (ℤ/M)²} c_d(j) e((j·ν)/M)`.

**`CdFourier` (finite identity).** `ĉ_d(ν) = 0` unless `ν = (1+i)μ`, and then
`ĉ_d((1+i)μ) = 4d(1+i) · (2/d) · c_d(μ)`.

Proof (all in Lean): CRT parametrization `j = d a + 4 b` of `ℤ/4d`
(`sum_crt`), which needs no inverses because `d ≡ 1 (mod 4)` and `(16/d) = 1` (`fourierHat_cd_eq`).
- 2-part: `Σ_{j mod 4} u(j) e(j·ν/4) = 4(1+i) u(ν/(1+i))`, and `0` off `(1+i)ℤ[i]`. A 16 × 16 table, proved in
  Lean by `decide` in `ℤ[i]` (`g2G_table`, with `e(k/4) = i^k`, `cexp_two_pi_I_div_four`).
- odd part `OddGauss d`: multiplicative in `d` (Lean: `oddGauss_mul`, with the parametrization
  `b = n b₁ + m b₂` and the squares `(n²/m) = 1`). At an odd prime `p` (Lean: `gauss2D`),
  `Σ_{x,y ∈ 𝔽_p} χ(x²+y²) e((xν₁+yν₂)/p) = p χ(ν₁²+ν₂²)`, uniformly for `p ≡ 1` and `3 (mod 4)`. With
  `g = Σ_t χ(t)e(t/p)`, expand `χ(n) = g^{−1} Σ_t χ(t) e(tn/p)` for all `n` (`sum_chi_psi_mul`). Complete the
  square, `Σ_x e((tx² + νx)/p) = e(−ν²/(4t)/p) χ(t) g` (`sum_psi_complete_sq`, `sum_psi_sq`), and
  substitute `u = −(4t)^{−1}`. The result is `χ(−1) g² χ(Nν) = p χ(Nν)` (`gaussSum_sq`).
  (Also VERIFIED numerically for `d ∈ {5, 13, 21, 3, 7}`, all `ν`.)
- `χ_d(N((1+i)μ)) = χ_d(2) χ_d(Nμ)` and `(2/d) = −1` for `d ≡ 5 (mod 8)`.

Then, with `ν = (1+i)μ`: `Σ_j c_d(j) gaussThetaDual(j/M)(x) = 8d (2/d) M Θ(2M²x)`. With §2.2 this gives the
**theta self-duality** (the Lean proof works directly with the Mellin transforms: `dual_eq`,
`fourier_tsum_eq`, `lambdaC_two_sub`; the theta-level statement is not needed)

  `Θ(1/x) = −8dM · x² · Θ(2M²x)`  (`d ≡ 5 (mod 8)`),

so `(Θ, −8dM Θ(2M² ·))` is a strong FE-pair (`k = 2`, `ε = 1`). Using `mellin_comp_mul_left`,
`mellin Θ (2 − s) = −8dM (2M²)^{−s} mellin Θ (s)`. Moreover `mellin Θ (s) = M^{2s−1} π^{−s} Γ(s) T(s)` with
`T = 4L(C_d, ·)`. Checking the constants by hand:
`(32d²)^{1−s/2} · 2^{s−1} · d · (4d)^{2s−3} = (32d²)^{s/2}/4` (the powers of `d` agree, `d^s`, and so do the powers of 2,
`2^{5s/2−2}`). This gives `Λ(2 − s) = −Λ(s)` for `Λ(s) = (32d²)^{s/2}(2π)^{−s}Γ(s)L(C_d, s)`: conductor
`32d²`, root number `(2/d) = −1` (and `+1` for `d ≡ 1 (mod 8)`, which matches PARI's `ellrootno` for
`d = 1`). The identity holds for `Re s > 3/2` on the Dirichlet-series side and extends to `Re s > 0`
by the identity theorem: `Γ` is analytic and nonzero there, and the continuation `F` is entire. On
`0 < Re s < 2` both `s` and `2 − s` lie in `Re > 0`. That is exactly the strip of `FunctionalEquation5`.

## 3. Dependency graph

Tiers: **S** = days (under ~300 lines), **M** = weeks, **L** = months (estimates SPECULATIVE). "DONE" = in
`scratch/bp-hecke-fe/HeckeFE.lean`, compiled, no `sorry`.

```
Mathlib: Hurwitz kernels, FE-pairs, hasSum_mellin, ZLattice sums, Gauss/Jacobi sums, ℤ[i], jacobiSym
  │
  ├─ A1 gaussTheta FE-pair (k = 2)                                S  DONE
  ├─ A2 Mellin = shifted lattice series (Re s > 3/2)              S  DONE
  ├─ A3 periodic twists T_c entire (block decomposition)          S  DONE
  ├─ A4 grouping by the norm: LSeries a = T_c                     S  DONE
  ├─ A5 HeckeContinuation5 ⟸ ∀d DeuringCd d                        S  DONE  heckeContinuation5_of_deuring
  │
  ├─ B1 ψ_d completely multiplicative, unit-invariant              S  DONE  psi_mul, psi_units (decide)
  ├─ B2 HeckeEuler d ⟸ HeckeMult ∧ HeckePrimePow ∧ h(1) = 1        S  DONE  heckeEuler_of_mult_primePow, heckeEuler_of_odd
  ├─ B2a HeckeMult d (Bezout/gcd in ℤ[i], fibres of size 4)         S  DONE  heckeMult, card_mul_fiber
  ├─ B2b HeckePrimePow at inert / ramified / bad p                   S  DONE  heckeCoeff_inert, _two_pow, _pow_of_dvd
  ├─ B2c HeckePrimePowSplit d (p ≡ 1 (4), p ∤ d)                    S  DONE  heckePrimePowSplit
  ├─ B3 GaussPointCount (⟹ GaussSplit 1, proved): a_p(y² = x³ − x) = π + π̄   M  OPEN  (Gauss 1814; quartic Jacobi
  │       sum J(χ,χ) and its congruence mod (1+i)³; or a temporary leaf)
  ├─ B3' GaussSplit d ⟸ GaussSplit 1 (twist, reciprocity)          S  DONE  gaussSplit_of_one
  ├─ B4 DeuringCd at p ≡ 3 (4), p | d, p = 2 (point counts)        S  DONE
  ├─ B5 DeuringCd d ⟸ HeckeEuler d ∧ GaussSplit d                  S  DONE  deuringCd_of_heckeEuler_gaussSplit
  │
  ├─ C1 dual kernel as lattice sum, its Mellin transform           S  DONE
  ├─ C2 CdFourier d ⟸ OddGauss d (CRT; 2-part by decide)           S  DONE  cdFourier_of_oddGauss
  ├─ C2' OddGauss d ⟸ OddGauss p for p | d (multiplicativity)      S  DONE  oddGauss_mul, oddGauss_of_prime
  ├─ C2'' OddGauss p, p odd prime                                  S  DONE  gauss2D, oddGauss_prime
  ├─ C3 FE of Λ_c under FourierRel                                 S  DONE  lambdaC_two_sub
  └─ C4 constants, strip, identity theorem
          FunctionalEquation5 ⟸ ∀d DeuringCd d ∧ CdFourier d       S  DONE  functionalEquation5_of_deuring_fourier'

  Final: literature_hecke_fe_of_gaussPointCount :
           GaussPointCount → HeckeContinuation5 ∧ FunctionalEquation5                     DONE
```

Open node: B3 (`GaussPointCount`), a classical refereed theorem and a legitimate leaf. The
remaining work is weeks, not months (SPECULATIVE). The analytic part, which wk-cr3 §4.3 estimated at
"months or more", is done.

## 4. What is proved (Lean, `scratch/bp-hecke-fe/HeckeFE.lean`, namespace `BpHeckeFE`)

All VERIFIED: compiled with `lake env lean` against Mathlib v4.35 and the project's
`LFunctionCd` and `CR3Literature` modules, no `sorry`, standard axioms only.

| Lean name | Statement |
| --- | --- |
| `gaussTheta`, `gaussThetaDual` | the kernels of §2.2 |
| `gaussTheta_one_div` | `gaussTheta a b (1/x) = x² · gaussThetaDual a b x` for `x > 0` |
| `gaussFEPair`, `isStrong_gaussFEPair` | strong FE-pair, `k = 2`, `ε = 1` |
| `differentiable_gaussLambda`, `gaussLambda_two_sub` | `Λ_{a,b} = mellin gaussTheta` is entire; `Λ_{a,b}(2−s) = Λ^dual_{a,b}(s)` |
| `hasSum_gaussTheta` | `gaussTheta a b t = Σ_{p∈ℤ²} gz a b p · exp(−π gq a b p t)` |
| `gaussPeriodPair`, `summable_norm_gz_rpow` | `ℤ + ℤi` as a Mathlib `PeriodPair`; `Σ_p ‖gz a b p‖^r < ∞` for `r < −2` |
| `hasSum_gaussLambda` | `Re s > 3/2`: `Σ_p π^{−s}Γ(s) gz/gq^s = Λ_{a,b}(s)` |
| `gaussL_continuation` | `Σ_p ((p₁+a)+i(p₂+b))/((p₁+a)²+(p₂+b)²)^s` has an entire continuation from `Re s > 3/2` |
| `twistedL`, `summable_twisted`, `twistedL_eq`, `twistedL_continuation` | `T_c(s) = Σ'_p c(p mod M)(p₁+ip₂)/(p₁²+p₂²)^s` is absolutely convergent and decomposes into `M²` shifted series; it is entire for every `c : (ZMod M)² → ℂ` |
| `normFiber`, `LSeries_eq_twistedL` | if `a n = Σ_{N p = n} c(p) gz p` (`n ≠ 0`) then `LSeries a s = T_c(s)` for `Re s > 3/2` |
| `unitOf`, `cdChar`, `cdChar_intCast`, `heckeCoeff` | the Hecke character data of §2.1, concretely |
| `DeuringCd d : Prop` | `∀ n ≠ 0, (cdCoeff d n : ℂ) = heckeCoeff d n` |
| `isLContinuation_of_deuring` | odd squarefree `d`, `DeuringCd d` ⟹ `∃ F, Literature.IsLContinuation (shortCurve (−d²)) F` |
| `heckeContinuation5_of_deuring` | the same for all squarefree `d ≡ 5 (mod 8)` (the form `tyzRow5b_of_readingA` uses) |
| `ech`, `hasSum_gaussThetaDual`, `hasSum_gaussLambdaDual` | dual kernel `= Σ_ν −i ν e(aν₁+bν₂) e^{−πN(ν)t}`; its Mellin transform as a Dirichlet series (`Re s > 3/2`) |
| `fourierHat`, `lambdaC`, `differentiable_lambdaC`, `lambdaC_eq`, `dual_eq` | `ĉ`, `Λ_c = Σ_j c(j)Λ_{j/M}` (entire), `π^{−s}Γ(s)T_c(s) = M(M²)^{−s}Λ_c(s)`, the dual side via `ĉ` |
| `FourierRel M c κ`, `fourierRel_const_mul`, `mulOneAddI_injective`, `fourier_tsum_eq` | the Fourier relation and the reindexing `ν = (1+i)μ` |
| `lambdaC_two_sub` | `FourierRel M c κ ⟹ Λ_c(2−s) = −iκ(1+i)·2^{−s}·M·(M²)^{−s}·Λ_c(s)` for all `s` |
| `CdFourier d : Prop`, `jacobiSym_two_of_mod_eight`, `const_identity` | `FourierRel (4d) (cdChar d) (4d(1+i)(2/d))`; `(2/d) = −1`; the conductor bookkeeping |
| `functionalEquation5_of_deuring_fourier`, `functionalEquation5_of_deuring_fourier'` | `DeuringCd d ∧ CdFourier d ⟹` the functional equation for `d` (the first also assumes `d ≡ 5 (mod 8)` and `d` squarefree); the Literature Prop `FunctionalEquation5` from both for all `d` |
| `sum_quadraticChar_cd_eq_zero`, `card_cd_affine_of_mod_four_eq_three`, `cdCoeff_prime_of_mod_four_eq_three` | `p ≡ 3 (mod 4)`: `Σ_x ((x³−d²x)/p) = 0`, `#{y² = x³ − d²x} = p`, `a_p = 0` |
| `deuring_prime_of_mod_four_eq_three`, `deuring_prime_of_dvd`, `deuring_two` | `DeuringCd` at `n = p` for `p ≡ 3 (mod 4)`, `p ∣ d`, `p = 2` |
| `heckeEulerPoly`, `HeckeEuler d : Prop`, `map_invOfUnit_one`, `cdCoeff_prime_eq`, `deuringCd_of_heckeEuler` | the Euler product of `heckeCoeff`; with agreement at all primes it gives `DeuringCd d` |
| `GaussSplit d : Prop`, `deuringCd_of_heckeEuler_gaussSplit` | agreement at split primes; `HeckeEuler d ∧ GaussSplit d ⟹ DeuringCd d` |
| `card_cd_affine_eq`, `sum_quadraticChar_twist`, `heckeCoeff_prime_twist`, `gaussSplit_of_one` | `#E_d^{aff}(𝔽_p) = p + Σ_x χ(x³−d²x)`; the quadratic twist `Σχ(x³−d²x) = χ(d)Σχ(x³−x)`; `GaussSplit 1 ⟹ GaussSplit d` |
| `unitG`, `unitG_mul` (decide), `gmul`, `psi`, `psi_mul`, `psi_units`, `psi_unit_mul` | `ψ_d(α) = (Nα/d) u(α) α` is completely multiplicative and `= 1` on units |
| `crt_injective`, `sum_crt`, `g2Sum`, `oddSum`, `fourierHat_cd_eq` | `ĉ_d = (2-part) · (odd part)` by the CRT parametrization `j = da + 4b` |
| `iPow`, `cexp_two_pi_I_div_four`, `g2G`, `g2Sum_eq`, `g2G_table` (decide) | the 2-part table |
| `OddGauss d : Prop`, `cdFourier_of_oddGauss` | `OddGauss d ⟹ CdFourier d` (`d ≡ 1 mod 4`) |
| `crt_injective2`, `sum_crt2`, `oddGauss_mul`, `oddGauss_one`, `oddGauss_of_prime` | `OddGauss` is multiplicative; reduces to odd primes |
| `HeckeContinuation5`, `tyzRow5b_of_readingA_five`, `heckeContinuation5_of_literature` | the restricted continuation Prop suffices for `TYZRow5b` |
| `literature_hecke_fe_final` | the reduction to `HeckeEuler`, `GaussSplit 1`, `OddGauss p` |
| `chiC`, `gP`, `sum_chi_psi_mul`, `sum_psi_sq`, `sum_psi_complete_sq`, `chiC_inv_eq`, `gP_sq`, `gP_ne_zero`, `gauss2D` | `Σ_{x,y∈𝔽_p} χ(x²+y²) e((xn₁+yn₂)/p) = p χ(n₁²+n₂²)` for odd primes `p` |
| `jacobiSym_eq_chiC`, `oddGauss_prime` | `OddGauss p` for every odd prime `p` |
| `literature_hecke_fe_of_heckeEuler_gaussSplit` | reduction to `HeckeEuler`, `GaussSplit 1` |
| `GaussPointCount`, `gaussSplit_one_of_pointCount`, `literature_hecke_fe_of_heckeEuler_gaussPointCount` | Gauss as a pure point count; reduction to `HeckeEuler`, `GaussPointCount` |
| `HeckeMult`, `HeckePrimePow`, `normFiber_one`, `heckeCoeff_one`, `coeff_inv_quadratic`, `heckeCoeff_prime_of_dvd`, `heckeEuler_of_mult_primePow` | `HeckeEuler` from multiplicativity and the prime-power recursion |
| `unitOf_eq_zero_of_even`, `heckeCoeff_two_pow`, `heckeCoeff_pow_of_dvd`, `dvd_of_dvd_sq_add_sq`, `normFiber_inert`, `heckeCoeff_inert`, `HeckePrimePowSplit`, `heckePrimePow_of_split` | the recursion at `p = 2`, `p ∣ d` and inert `p` |
| `literature_hecke_fe_of_mult_split_gaussPointCount` | the reduction with `HeckeMult` as a hypothesis |
| `certifiedRankTYZClRk_of_elementary`, `certifiedRankTYZClRk_of_gaussPointCount` | CR₃ from TYZ reading A, Gross–Zagier and the elementary statements, resp. `GaussPointCount` alone |
| `toG`, `norm_toG`, `toG_gmul`, `norm_eq_one_cases`, `norm_gcd_eq`, `unitsZ`, `conjZ`, `card_mul_fiber`, `gmul_mem_normFiber`, `heckeCoeff_zero`, `heckeMult` | `HeckeMult d` for every `d`: `N(gcd(γ, m)) = m` when `N γ = mn` with `m, n` coprime; the fibres of `(α, β) ↦ αβ` have 4 elements |
| `literature_hecke_fe_of_split_gaussPointCount` | reduction to `HeckePrimePowSplit`, `GaussPointCount` |
| `isUnit_of_norm_one`, `prime_of_norm_prime`, `psi_split_prime`, `sum_mul_bij`, `unit_mem_unitsZ`, `norm_unitsZ`, `psi_gmul_unit`, `split_ne`, `piZ`, `not_conj_dvd`, `prime_piZ`, `p_eq_mul`, `split_dvd`, `sum_normFiber_prime`, `card_unitsZ`, `heckePrimePowSplit` | `HeckePrimePowSplit d` for every `d`: Gaussian primes above split `p`, `A_p = U·π ⊔ U·π̄`, the Hecke relation |
| `literature_hecke_fe_of_gaussPointCount` | **the final reduction** (§0) |
| `heckeEuler_of_odd`, `deuringCd_of_gaussPointCount` | `HeckeEuler d` (odd squarefree `d`); `DeuringCd d` from `GaussPointCount` (`d ≡ 1 mod 4`) |

Faithfulness. `DeuringCd` is stated over the project's `cdCoeff` (proved equal to Mathlib's
`L(C_d,s)` coefficients by `LFunctionCd.lean`) and over explicit sums in `ℤ²`. It involves no
abstract structure and is a true classical theorem: for `d ≡ 1 (mod 4)` it is
Deuring's identity `L(C_d,s) = L(ψ_d,s)` written out. The PARI check (`deuring_check.py`,
`out_deuring_check.txt`) found 0 mismatches for `d ∈ {1,5,13,21,29,37,53,85}`, `n ≤ 400`.
For `d ≡ 3 (mod 4)` the Jacobi symbol `(n/d)` would have to be replaced by `(d/n)`;
`DeuringCd` is only claimed for `d ≡ 1 (mod 4)`.

## 5. Scripts (`scratch/bp-hecke-fe/`)

- `HeckeFE.lean`: the Lean file (§4).
- `deuring_check.py` → `out_deuring_check.txt`: `DeuringCd` numerically, with conductors and root
  numbers from PARI.
- `fourier_check.py` → `out_fourier_check.txt`: the 2-part, `OddGauss d` for `d ∈ {5, 13, 21, 3, 7}`,
  and the full `CdFourier d` for `d ∈ {5, 13, 21}`, numerically.
- `remaining_check.py` → `out_remaining_check.txt`: `GaussSplit 1` and `HeckeEuler d` numerically.
- `gauss_jacobi_check.py` → `out_gauss_jacobi_check.txt`: the Jacobi-sum plan for `GaussPointCount`
  (`S = 2 Re J`, `|J|² = p`, `−J` primary), at 10 primes.
- `log.md`: results log.

## 6. Not done / unchecked

- Open (checked numerically only): `GaussPointCount` (B3), Gauss's theorem. Everything else in §3 is
  proved in Lean.
- The scratch file imports `ZInQKernel.RouteK.Rank.LFunctionCd` and
  `ZInQKernel.Hypotheses.CR3Literature`; both were built with `lake build` in this worktree first.
- `HeckeContinuation` for all `d ≠ 0` (as currently stated in `CR3Literature.lean`) is not proved;
  only `HeckeContinuation5`. See §0 for why the restriction is enough.
- Literature locators: Gauss's point count is cited from Ireland–Rosen Ch. 18 §4 from memory
  (UNVERIFIED theorem number). The conductor `32d²` and root number `−1` are confirmed by PARI for
  the sampled `d` (VERIFIED) and, in Lean, follow from `CdFourier` and `DeuringCd`. So they no
  longer need a literature leaf.
