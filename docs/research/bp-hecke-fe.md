# bp-hecke-fe: blueprint for `HeckeContinuation` and `FunctionalEquation5`

Status: task bp-hecke-fe, 2026-11-12, base fork main `27875ecf`. Lean: `scratch/bp-hecke-fe/HeckeFE.lean`
(compiled with `lake env lean`, no `sorry`, `#print axioms` = `propext, Classical.choice, Quot.sound`).
Log: `scratch/bp-hecke-fe/log.md`. Marks: VERIFIED (compiled, computed or read here), STANDARD
(published, reference given), SPECULATIVE; theorem numbers quoted from memory are UNVERIFIED.

## 0. Main result

1. **No Hecke-character or adelic machinery is needed.** Both Props come from Mathlib's
   one-variable Hurwitz kernels. The weight-two theta series of a shifted copy of `ℤ[i]` factors
   as
   `Σ_{(m,n)∈ℤ²} ((m+a) + i(n+b)) e^{−π((m+a)²+(n+b)²)x} = oddKernel a · evenKernel b + i · evenKernel a · oddKernel b`,
   so the theta transformation law, the Mellin transform and the entireness all come from
   `Mathlib.NumberTheory.LSeries.{HurwitzZetaEven, HurwitzZetaOdd, AbstractFuncEq, MellinEqDirichlet}`.
2. **Proved in Lean (VERIFIED):** both literature Props are reduced to two concrete,
   elementary statements about explicit finite sums:

   `heckeContinuation5_of_deuring : (∀ d, d % 8 = 5 → Squarefree d → DeuringCd d) → ∀ d, d % 8 = 5 → Squarefree d → ∃ F, IsLContinuation (C_d) F`

   `functionalEquation5_of_deuring_fourier' : (∀ d ≡ 5 (8) squarefree, DeuringCd d) → (∀ such d, CdFourier d) → Literature.FunctionalEquation5`

   The second conclusion is the project's Prop `ZInQ.Literature.FunctionalEquation5` itself
   (conductor `32d²`, root number `−1`, strip `0 < Re s < 2`).
   - `DeuringCd d`: for `n ≠ 0`, the coefficient `cdCoeff d n` (the project's coefficients of
     Mathlib's `L(C_d, s)`, `LFunctionCd.lean`) equals
     `heckeCoeff d n = ¼ Σ_{α ∈ ℤ[i], N(α) = n} (N(α)/d) · u(α) · α`. Here `(N(α)/d)` is the Jacobi
     symbol and `u(α) ∈ {±1, ±i}` makes `u(α)α ≡ 1 (mod 2 + 2i)` (`unitOf`). This is Deuring's
     `L(C_d, s) = L(ψ_d, s)`.
   - `CdFourier d`: the finite Fourier transform of `c_d(α) = (N(α)/d) u(α)` on `(ℤ/4d)²`
     vanishes off `(1+i)ℤ[i]` and equals `4d(1+i)(2/d) c_d(μ)` at `(1+i)μ`.

   Both were checked numerically with PARI, with no failure (VERIFIED): `DeuringCd` for 8 values
   of `d` and all `n ≤ 400` (`deuring_check.py`), and `CdFourier` for `d ∈ {5, 13, 21}` and all `ν`
   (`fourier_check.py`). `DeuringCd` is also proved in Lean at every prime `n = p` except the split
   primes `p ≡ 1 (mod 4)`, `p ∤ d`: at `p ≡ 3 (mod 4)` (point count `#{y² = x³ − d²x} = p` by the
   involution `x ↦ −x`), at `p ∣ d` and at `p = 2`.
3. **Blueprint for the rest (§3).** `DeuringCd` is elementary classical number theory. What
   remains is Gauss's count of points on `y² = x³ − d²x` at split primes (quartic Jacobi sums) and the
   multiplicativity and prime-power recursion of `heckeCoeff` (unique factorization in `ℤ[i]`): tier M,
   weeks. `CdFourier` is quadratic Gauss sums over `𝔽_p` and `𝔽_{p²}` (or one composite Gauss-sum
   argument, §2.4), a 16-term table at 2 and the Chinese remainder theorem: tier M. The root number
   `−1` is the Jacobi symbol `(2/d) = −1` for `d ≡ 5 (mod 8)`; the conductor bookkeeping is a Lean
   lemma (`const_identity`).
4. **Suggested change on integration.** `Literature.HeckeContinuation` quantifies over every
   `d ≠ 0`, but its only use, `tyzRow5b_of_readingA`, applies it to squarefree `d ≡ 5 (mod 8)`.
   Restating it for that case (the conclusion of `heckeContinuation5_of_deuring`) loses nothing for the
   headline and avoids even `d` and non-squarefree `d`, where `LSeries_cd_eq` is not available
   (even `d` changes the conductor and the character at 2).
5. **No new leaves.** Every node below is glue over Mathlib definitions. If the team wants to
   parallelize, Gauss's point count (node B3) can be stated as a temporary leaf: the number of
   points on `y² = x³ − Dx` over `𝔽_p` (Ireland–Rosen, *A Classical Introduction to Modern Number
   Theory*, Ch. 18 §4, Theorem 5; theorem number UNVERIFIED). It is published, refereed and
   elementary.

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

### 2.4 The functional equation (in Lean modulo `CdFourier` and `DeuringCd`)

Let `Θ(x) = Σ_j c_d(j) gaussTheta(j/M)(x)`, so `Θ(y) = M^{−1} Σ_α c_d(α) α e^{−πN(α)y/M²}`. The dual
kernel is `gaussThetaDual a b x = −i Σ_{ν ∈ ℤ²} ν e(aν₁ + bν₂) e^{−πN(ν)x}`, from `hasSum_int_sinKernel` and
`hasSum_int_cosKernel`. Hence

  `Σ_j c_d(j) gaussThetaDual(j/M)(x) = −i Σ_ν ĉ_d(ν) ν e^{−πN(ν)x}`,  with `ĉ_d(ν) = Σ_{j ∈ (ℤ/M)²} c_d(j) e((j·ν)/M)`.

**`CdFourier` (finite identity).** `ĉ_d(ν) = 0` unless `ν = (1+i)μ`, and then
`ĉ_d((1+i)μ) = 4d(1+i) · (2/d) · c_d(μ)`.

Proof plan (not in Lean): CRT `ℤ/4d = ℤ/4 × ℤ/d` with `1/(4d) = u/4 + v/d`, `u ≡ d^{−1} ≡ 1 (mod 4)`.
- 2-part: `Σ_{j mod 4} u(j) e(j·ν/4) = 4(1+i) u(ν/(1+i))`. This is a 16 × 16 table (VERIFIED numerically;
  in Lean `decide`/`norm_num` over `ZMod 4`, with `e(k/4) ∈ {1, i, −1, −i}`).
- odd part, per prime `p ∣ d`: `Σ_{j ∈ 𝔽_p²} χ_p(Nj) e(j·ν/p) = p χ_p(Nν)`. For `p ≡ 1 (mod 4)`,
  `N(x+iy) = (x+iy)(x−iy)` splits into two independent coordinates, and the sum is
  `g(χ_p)² χ_p(Nν) = χ_p(−1) p χ_p(Nν)` (`gaussSum_sq`). For `p ≡ 3 (mod 4)`, it is the quadratic
  Gauss sum of `𝔽_{p²}`, equal to `−g(χ_p)² = p` (Davenport–Hasse for a quadratic extension, or a direct
  count of `#{x² + y² = t}`). The CRT cross factors are squares, and `χ_d(N(vν)) = χ_d(Nν)`.
  (VERIFIED numerically for `d ∈ {5, 13, 21, 3, 7}`, all `ν`.) A uniform alternative for odd
  squarefree `d ≡ 1 (mod 4)`: expand `χ_d(n) = τ(χ_d)^{−1} Σ_t χ_d(t) e(tn/d)` (`χ_d` is primitive), complete
  the square in each coordinate (`Σ_x e((tx² + νx)/d) = e(−\overline{4t}ν²/d) χ_d(t) G`), and use
  `G² = χ_d(−1)d`. The result is `d χ_d(Nν)`.
- `χ_d(N((1+i)μ)) = χ_d(2) χ_d(Nμ)` and `(2/d) = −1` for `d ≡ 5 (mod 8)`.

Then, with `ν = (1+i)μ`: `Σ_j c_d(j) gaussThetaDual(j/M)(x) = 8d (2/d) M Θ(2M²x)`. With §2.2 this gives the
**theta self-duality**

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

Tiers: **S** = days (under ~300 lines), **M** = weeks, **L** = months. "DONE" = in
`scratch/bp-hecke-fe/HeckeFE.lean`, compiled.

```
Mathlib: Hurwitz kernels, FE-pairs, hasSum_mellin, ZLattice sums, Jacobi/Gauss sums, ℤ[i], jacobiSym
  │
  ├─ A1 gaussTheta FE-pair (k=2)                              S  DONE
  ├─ A2 Mellin = shifted lattice series (Re s > 3/2)          S  DONE
  ├─ A3 periodic twists T_c entire (block decomposition)      S  DONE
  ├─ A4 grouping by the norm: LSeries a = T_c                 S  DONE
  │
  ├─ B1 ψ_d well defined on ideals, completely multiplicative   S
  │     (unitOf multiplicative on (ℤ[i]/4)^×: a decide; u(εα)εα = u(α)α for units ε)
  ├─ B2 heckeCoeff multiplicative; heckeCoeff(p^k) recursion    M
  │     (ℤ[i] is a UFD; count ideals of norm n; Euler factors at split/inert/ramified p)
  ├─ B3 Gauss: a_p = (d/p)(π+π̄), p ≡ 1 (4), π primary           M  (candidate temporary leaf)
  │     (#{y² = x³ − d²x} via the quartic Jacobi sum J(χ,χ); primary congruence mod (1+i)³)
  ├─ B4 a_p = 0 for p ≡ 3 (4) (involution x ↦ −x); p | 2d both 0  S  DONE (DeuringCd at these p)
  ├─ B5 DeuringCd d  (cdCoeff d n = heckeCoeff d n)            S  given B2–B4 and LFunctionCd
  │
  ├─ A5 HeckeContinuation (d ≡ 5 mod 8, squarefree) ⟸ B5        DONE (heckeContinuation5_of_deuring)
  │
  ├─ C1 dual kernel as lattice sum (sinKernel·cosKernel)       S  DONE
  ├─ C2 CdFourier: ĉ_d = 4d(1+i)(2/d) c_d(·/(1+i))             M
  │     C2a 2-part, 16×16 table (S); C2b p ≡ 1 (4) via gaussSum_sq (S);
  │     C2c p ≡ 3 (4), Gauss sum of 𝔽_{p²} (S–M); C2d CRT assembly (S)
  ├─ C3 FE of Λ_c under a Fourier relation (lambdaC_two_sub)  S  DONE (done on the Mellin side;
  │     the theta self-duality Θ(1/x) = −8dM x² Θ(2M²x) is not needed)
  └─ C4 constants + strip/identity theorem
        ⟹ FunctionalEquation5 ⟸ B5 ∧ C2                       S  DONE (functionalEquation5_of_deuring_fourier')
```

Cheapest faithful route: A1–A5, B4, C1, C3, C4 are done. What remains is B1–B3 and B5 (for both
Props) and C2 (for the functional equation). B3 is the largest single node. If parallelized, B (arithmetic) and C
(Fourier) are independent. The total is a few person-months at most (SPECULATIVE); the analytic
part, which wk-cr3 §4.3 estimated at "months or more", is done.

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
| `functionalEquation5_of_deuring_fourier`, `functionalEquation5_of_deuring_fourier'` | `DeuringCd d ∧ CdFourier d ⟹` the functional equation for `d`; the Literature Prop `FunctionalEquation5` from both for all `d` |
| `sum_quadraticChar_cd_eq_zero`, `card_cd_affine_of_mod_four_eq_three`, `cdCoeff_prime_of_mod_four_eq_three` | `p ≡ 3 (mod 4)`: `Σ_x ((x³−d²x)/p) = 0`, `#{y² = x³ − d²x} = p`, `a_p = 0` |
| `deuring_prime_of_mod_four_eq_three`, `deuring_prime_of_dvd`, `deuring_two` | `DeuringCd` at `n = p` for `p ≡ 3 (mod 4)`, `p ∣ d`, `p = 2` |

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
- `fourier_check.py` → `out_fourier_check.txt`: the two parts of `CdFourier` numerically.
- `log.md`: results log.

## 6. Not done / unchecked

- B1–B3, B5 (`DeuringCd` beyond the primes `p ≢ 1 (mod 4)`) and C2 (`CdFourier`) are not
  formalized. They are checked numerically only.
- Literature locators: Gauss's point count is cited from Ireland–Rosen Ch. 18 §4 from memory
  (UNVERIFIED theorem number). The conductor `32d²` and root number `−1` are confirmed by PARI for
  the sampled `d` (VERIFIED) and, in Lean, follow from `CdFourier` and `DeuringCd`. So they no
  longer need a literature leaf.
