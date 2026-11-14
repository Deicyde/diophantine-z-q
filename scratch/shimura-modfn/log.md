# shimura-modfn results log

Task: `Shimura.ShimuraReciprocityModFn` (tyz-cm, `ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean`).

## 2026-11-13 23:10 start (fresh; no earlier run)

* Base 71dc3f1b. `lake build ZInQKernel.Contrib.TYZGenus.ShimuraMain` started (build1.log).
* No cypari2/mpmath on this host (and no network allowed): numerics in plain Python double
  precision.

## Numerics (VERIFIED computed, double precision)

* `jpair_check.py` → `jpair_check.out`: for `N = 32`, `Q = [32,10,1]` (`D = −28`):
  `j(τ_Q) = j(32τ_Q) = 16581375 = 255³` and `x(τ_Q) = −1 + 2.6457513111i = −1 + √−7`, `y = 4`.
  So the point `(j(τ_Q), j(32τ_Q))` of the plane model is rational while `x(τ_Q)` is not:
  no `A/B ∈ ℚ(X, Y)` with `x = A(j, j₃₂)/B(j, j₃₂)` has `B(255³, 255³) ≠ 0`.
  Similar: `[32,18,3]` (D=−60), `[32,4,1]` (D=−112), `[32,6,1]` (D=−92).
* `isolated_check.py` → `isolated_check.out`: multiplicity of `j(32τ)` among the 48 values
  `j((aτ+b)/d)` (`ad = 32`, `0 ≤ b < d`, `gcd(a,b,d) = 1`), compared via reduced points of the
  fundamental domain. SINGULAR (mult 2): the four above; TYZ class-7 forms `tyzForm7`/`tyzForm7'` for
  `n = 7, 15, 47` (exactly the `n` with `[𝔭₂]^{10} = 1`, cf. cm-bridge §1). ISOLATED (mult 1):
  `tyzForm`, `tyzForm'` for `n = 5, 13, 21, 29, 37, 53, 61`; class-7 for `n = 23, 31, 39, 55`.
  (31 forms checked.)

## 2026-11-13 23:35 ModFn.lean §0–§4 compiles

* `lake build ZInQKernel.Contrib.TYZGenus.ShimuraMain`: OK (10293 jobs).
* `lake env lean scratch/shimura-modfn/ModFn.lean`: 0 errors (VERIFIED; output
  `compile-ModFn.out`). Axioms of `shimuraReciprocityModFn_of_split`, `…_isolated`,
  `reciprocity_of_rep`, `jPair_reciprocity`, `isIsolated_one`, `shimuraReciprocityModFn_eq`:
  `[propext, Classical.choice, Quot.sound]`.
* Statements: `MainTheoremCMj` (leaf CM-J), `RatX0Rep` (non-CM leaf), `ShimuraReciprocityModFnSingular`
  (restriction of the leaf to non-isolated points); `shimuraReciprocityModFn_of_split`:
  `MainTheoremCMj → RatX0Rep → ShimuraReciprocityModFnSingular → ShimuraReciprocityModFn`.
* Pitfall: `MainTheoremCMj` needs `κ(O)`-stability of `⟨1, τ'⟩` (else `κ(𝔟)L' = cL` only fixes `O·L'`;
  `𝔟 = O`, `L = O`, `L' = ⟨1, 2τ⟩` would make it false).
* `set_option maxRecDepth 8000` needed to elaborate the copied statement.

## 2026-11-14 00:05 §5 q-expansion bookkeeping compiles

* `isRatModFn_jInv N : IsRatModFn N jInv` (`SL₂(ℤ)`-invariance from Mathlib's slash invariance of
  `E₄` and tyz-cm's `eta_pow_smul`; rational `q`-expansion `q·j = E₄(q)³/∏(1−qⁿ)²⁴` from Mathlib's
  `E_qExpansion_coeff` + tyz-cm's `IsRatAt` calculus; growth `|j| ≤ C e^{2π Im τ}` for `Im τ ≥ 1` by
  compactness).
* `isRatModFn_jN (hN : 0 < N) : IsRatModFn N (fun τ => jInv (scaleH N τ))` (`Γ₀(N)`-invariance via
  `γ' = [[a, Nb], [c/N, d]]`; growth at every cusp via tyz-cm's Hermite decomposition
  `exists_smul_decomp`; `q`-expansion reindexed by `Function.Injective.hasSum_iff`).
* `jPair_of_modFn : ShimuraReciprocityModFn → (j-part at Heegner pairs)` — consistency: on Heegner
  lattices `MainTheoremCMj` asks nothing beyond tyz-cm's leaf.
* Compile: 0 errors, no `sorryAx`; 9 `#print axioms` all `[propext, Classical.choice, Quot.sound]`
  (VERIFIED, `compile-ModFn.out`).

## 2026-11-14 00:40 class-7 singular set is finite

* Argument (STANDARD reasoning): for `tyzForm7 n` (`D = −n`, `O = 𝓞_K`, 2 split) the only `O`-stable
  cyclic 32-isogenies of `L` are `𝔭₂⁻⁵L`, `𝔭̄₂⁻⁵L`; non-`O`-stable ones have other orders, hence other
  `j`. So non-isolated ⟺ `[𝔭₂]^{10} = 1` ⟺ `𝔭₂^{10} = (α)`, `N(α) = (a² + nb²)/4 = 2^{10}`, `b ≠ 0`
  ⟹ `n ≤ 4096`.
* `class7_singular.py` → `class7_singular.out` (VERIFIED computed): 32 values
  `n = 7, 15, 47, 79, 103, 119, 127, 143, 159, 303, 319, 415, 455, 615, 1495, 1695, 1887, 2071, 2247,
  2415, 3007, 3135, 3255, 3367, 3471, 3567, 3655, 3927, 4015, 4047, 4071, 4087`.
* Cross-check against the direct multiplicity count (`class7_crosscheck.out`, 12 values of `n` in
  71…167): 12/12 agree.

## 2026-11-14 01:00 review

* Independent AI review (read-only): `MainTheoremCMj` TRUE, `RatX0Rep` TRUE, singular-point claim
  SOUND (needs only `x(τ_Q) ∉ ℝ`: `[32,−10,1]` is a different point with the same `(j, j₃₂)`),
  §1 derivation CORRECT. No blocking finding. Recorded in report §5.
