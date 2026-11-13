# hecke-all: `HeckeContinuation` for every `d ≠ 0`, from Gauss's point count

Status: task hecke-all, 2026-11-12. Base `01267822` (origin/wip/integrate-w34b). Lean files:
`ZInQKernel/Contrib/HeckeAll/{HeckeFE,LocalCd,Iso,Continuation}.lean`. Log: `scratch/hecke-all/log.md`.
Marks: VERIFIED (compiled, computed or read here), STANDARD (published, reference given), SPECULATIVE.

## 0. Main result

**`ZInQ.Literature.HeckeContinuation` is proved in Lean from `GaussPointCount`, for every `d ≠ 0`**
(VERIFIED: `lake build ZInQKernel.Contrib.HeckeAll.Continuation` succeeds, no `sorry`, and
`#print axioms` gives `propext, Classical.choice, Quot.sound`):

```lean
theorem ZInQ.Contrib.heckeContinuation_of_gaussPointCount (h1 : HeckeAll.GaussPointCount) :
    ZInQ.Literature.HeckeContinuation
```

(`HeckeAll` here stands for the namespace `ZInQ.Contrib.HeckeAll`.) Together with bp-hecke-fe's functional
equation, which is copied here, both textbook CR₃ Props follow from the same hypothesis
(VERIFIED, compiled, standard axioms):
`ZInQ.Contrib.heckeContinuation_functionalEquation5_of_gaussPointCount : HeckeAll.GaussPointCount →
Literature.HeckeContinuation ∧ Literature.FunctionalEquation5`. `GaussPointCount` is copied verbatim
from `scratch/bp-hecke-fe/HeckeFE.lean`. It says that for primes `p ≡ 1 (mod 4)`,
`p − #{y² = x³ − x}(𝔽_p) = ¼ Σ_{a²+b²=p} u(a+bi)(a+bi)`. The statement is over local copies of
`normFiber`, `unitOf` and `gz`. A `GaussPointCount` stated over another verbatim copy of those
definitions (for example the gauss-proof task's `ZInQ.Contrib.GaussFE`) is accepted by
definitional unfolding (VERIFIED: `scratch/hecke-all/ComposeTest.lean` compiles). So when the
parallel task proves its copy, the provider is one line:
`theorem ZInQ.Contrib.heckeContinuation : ZInQ.Literature.HeckeContinuation :=
heckeContinuation_of_gaussPointCount <gauss-proof's theorem>`. That line is not written here,
because a Contrib module of this task may import only baseline files and its own files.

## 1. What is new compared with bp-hecke-fe

bp-hecke-fe proved the continuation for squarefree `d ≡ 5 (mod 8)` only (`HeckeContinuation5`).
Three gaps remained, and each is now closed in Lean.

### 1.1 Even squarefree `d`: Mathlib's L-function at `p = 2` (`LocalCd.lean`)

`LFunctionCd.lean` (baseline) computes Mathlib's `L(C_d, s)` only for odd squarefree `d`. It needs
the model `y² = x³ − d²x` to be minimal at every place, and it proves this from `v_p(Δ) < 12`.
For `d = 2e` (with `e` odd) we have `v₂(Δ) = v₂((2d)⁶) = 12`, so that criterion fails. The model
is still minimal, which PARI confirms: `u = 1`, `f₂ = 6`, type I₁*. The new proof uses `c₄`:

* `isMinimal_baseChange_of_c₄`: over any DVR, an integral `W` is minimal if `c₄(W) ≠ r⁴ c₄(W')`
  for every `r ∈ 𝔪` and every integral `W'`.
* `c₄_two_adic`: over `ℤ₂`, every integral model has either `16 ∣ c₄` (when `a₁ ∈ 𝔪`) or
  `c₄ ∉ 𝔪`, because `c₄ = (a₁² + 4a₂)² − 24(2a₄ + a₁a₃)`. So `v₂(c₄) ∉ {1, 2, 3}`.
* `isMinimal_cdLocal_two`: `c₄(C_{2e}) = 192e²` has `v₂ = 6`. A factorization `r⁴c₄'` with
  `v(r) ≥ 1` would need `v₂(c₄') = 2`, or `v(r) ≥ 2` with `c₄'` integral. Both are impossible.
* `isMinimal_cdLocal'`: minimality at every place, for every squarefree `d`.
  `localPolynomial_cdLocal_eq'`: the local polynomial is `cdEulerPoly d p`. `LSeries_cd_eq'`:
  `L(C_d, s) = Σ cdCoeff d n · n^{−s}` for every squarefree `d`. These are copies of the baseline
  proofs with the parity hypothesis removed.

### 1.2 Non-squarefree `d`: isomorphism invariance (`Iso.lean`)

Mathlib defines `L(E, s)` from a minimal model at each place, chosen by `Classical.choice`. For
`d = m²d'`, the model `y² = x³ − d²x` is not minimal at `p ∣ m`, and `C_9` even has good reduction
at 3. So the proof goes through `C_{m²d'} ≅ C_{d'}` instead:

* `not_hasMultiplicativeReduction_smul`: if `v(c₄)³ ≤ v(Δ)` (integral `j`), then no model
  `C • W` has multiplicative reduction.
* `localPolynomial_smul`: under that condition, Mathlib's `localPolynomial` does not change under a
  change of variables. Two minimal models differ by `v(u) = 1`, so the good and additive cases and
  `#W̃(κ)` agree (`vK_u_eq_one` and `exists_reduction_variableChange` from `LFunctionCd.lean`).
* `hj_cdLocal` (`c₄³ = 1728Δ`), `scaleChange_smul` (`u = m` maps `C_{m²d}` to `C_d`),
  `LFunction_cd_sq_mul` and `LSeries_cd_sq_mul`: `L(C_{m²d}, s) = L(C_d, s)`.

### 1.3 All residues of `d` mod 8: the quadratic twist (`Continuation.lean`)

The bp-hecke-fe route uses a separate Hecke character `ψ_d` for each `d`, and its proof of
Deuring's identity was written for `d ≡ 1 (mod 4)`. Here the twist is done on the coefficient
side instead, so only the Hecke character of `C_1` is needed:

* `cdCoeff_twist`: `cdCoeff d n = J(d | n) · cdCoeff 1 n` for every `d` and every `n ≠ 0`, with
  Mathlib's Jacobi symbol `jacobiSym d n`. At primes `p ∤ 2d` this is
  `a_p(C_d) = (d/p) a_p(C_1)`, from the substitution `x ↦ dx` in the point count
  (`sum_quadraticChar_twist`, `card_cd_affine_eq`). The prime powers follow from the recursion,
  since `(d/p)² = 1` (`coeff_twist_quadratic`). At `p ∣ d` both sides are `0`. At `p = 2` both
  sides are `0`, because `a_{2^k}(C_1) = 0`. The symbol `J(d | ·)` is completely multiplicative
  (`jacobiSym_factorization`).
* `DeuringCd 1`, that is `cdCoeff 1 n = ¼ Σ_{Nα=n} u(α)α`, comes from bp-hecke-fe's
  `deuringCd_of_gaussPointCount`. Hence `L(C_d, s) = Σ_α c(α mod 4d) α N(α)^{−s}` with
  `c = twChar d = ¼ J(d | N·) u(·)` on `(ℤ/4d)²`. The function is well defined because
  `Nα mod 4d` depends only on `α mod 4d`, and `J(d | ·)` has period `4d` on odd arguments
  (`jacobiSym.mod_right`). When `Nα` is even, `u(α) = 0`; this is `unitG_eq_zero_of_two_mul`,
  proved by `decide`. This step is `twChar_intCast`.
* `isLContinuation_of_squarefree`: `twistedL_continuation` from bp-hecke-fe (the weight-two theta
  series) gives the entire continuation. `heckeContinuation_of_gaussPointCount` then writes
  `d = b²a` with `a` squarefree (`exists_sq_mul_squarefree`) and applies `LSeries_cd_sq_mul`.

## 2. Checks

* VERIFIED (PARI via cypari2, `scratch/hecke-all/twist_check.py`, output
  `out_twist_check.txt`). Tested 26 values of `d`, covering every residue mod 8 and nine
  non-squarefree `d` up to 72. For all of them `a_n(C_d) = J(d'|n) a_n(C_1)` for `n ≤ 300`, where
  `d'` is the squarefree part of `d`: 0 mismatches. No curve has multiplicative reduction at any
  prime. For squarefree `d`, PARI's minimal model has `u = 1`. Conductor: `32d²` for odd
  squarefree `d`; for `d = 2e` with `e` odd, `f₂ = 6`, so `N = 64e²`.
* VERIFIED (compiled): the four modules build with `lake build`, and `#print axioms` gives the
  standard three. None of the modules contains `sorry`. Each imports only Mathlib, the baseline
  files `ZInQKernel/RouteK/Rank/LFunctionCd.lean` and `ZInQKernel/Hypotheses/CR3Literature.lean`,
  and this task's files.

## 3. What remains

* **`GaussPointCount`** is the only hypothesis left (Gauss 1814; Ireland–Rosen Ch. 18 §4, STANDARD,
  theorem number UNVERIFIED). The gauss-proof task is proving it. When checked (about 22:19) its branch had
  `gauss_jacobi`, which gives the count `p + 2A` with `A² + B² = p` and a primary normalization,
  but not yet the `GaussPointCount` form.
* `HeckeFE.lean` is a full copy of bp-hecke-fe's file (2724 lines, including the
  functional-equation part). The gauss-proof task has made a second copy. On integration a single
  shared copy should be kept, and `HeckeAll.GaussPointCount` and `GaussFE.GaussPointCount` should
  be identified. They are definitionally equal (`ComposeTest.lean`).
* By-products available for later use: Mathlib's `L(C_d, s)` in closed form for every squarefree
  `d` (`LFunction_cd_apply'`), and the invariance of Mathlib's L-function under change of variables
  for curves with integral `j` (`localPolynomial_smul`). The functional equation for `d ≢ 5 (mod 8)`
  was not attempted; the project does not need it.
