# tyz-cm: the CM leaf of the TYZ genus package

Task tyz-cm, 2026-11-13. Branch `wip/tyz-cm`. Files (all new, owned by tyz-cm):
`ZInQKernel/Contrib/TYZGenus/Shimura{Recip,Zn,Field,ModFn,QExp,Cusp,Main}.lean`.
Log: `scratch/tyz-cm/log.md`.

## 1. Main result

Target: cm-points' leaf `CM.CMFieldOfDefinition ringClassFieldD` (every Heegner point of
discriminant `D` on `X₀(32) = A`, through x0-32's `X0.phiC`, has coordinates in the ring class
field of discriminant `D`), and with it `Package.CMFieldOfDefinitionTYZ`.

**Status: reduced to ONE textbook leaf, `Shimura.CMValueRingClass`** (the field-of-definition
theorem for values of `ℚ(X₀(N))` at Heegner points: main theorem of CM plus the rational
structure of `X₀(N)`). Every `X₀(32)`-specific step is proved. That includes **x0-32's leaf
`X0.EtaModelInvariant` (`Γ₀(32)`-invariance of `x, y`), which is now a theorem**, via the eta
identity `x = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` and the `η²` multiplier in closed form.

```lean
-- ShimuraTheta.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_cmValueRingClass
    (hV : Shimura.CMValueRingClass) : CM.CMFieldOfDefinition RingClass.ringClassFieldD
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldTYZ_of_cmValueRingClass
    (hV : Shimura.CMValueRingClass) : Package.CMFieldOfDefinitionTYZ
theorem ZInQ.Contrib.TYZGenus.Shimura.tyzThm35ReadingA_of_cmValueRingClass
    (h11 : TYZDecomp.TYZThm11Integral) (h1 : TYZDecomp.TYZLcalOne)
    (h29 : TYZDecomp.TYZLemma29Mod2) (hV : Shimura.CMValueRingClass)
    (hs : Package.TYZSigmaFixesZn) (h318 : Package.Lemma318Literal RingClass.HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, TYZDecomp.IsTYZLcal ℓ → Package.GenusPointLeafCM ℓ) :
    ZInQ.Literature.TYZThm35ReadingA
theorem ZInQ.Contrib.TYZGenus.Shimura.etaModelInvariant : X0.EtaModelInvariant
theorem ZInQ.Contrib.TYZGenus.Shimura.xC_eq_even (τ : UpperHalfPlane) :
    X0.xC ↑τ = X0.etaD 16 ↑τ ^ 6 / (X0.etaD 8 ↑τ ^ 2 * X0.etaD 32 ↑τ ^ 4)
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_shimuraModFn
    (hS : Shimura.ShimuraReciprocityModFn) : CM.CMFieldOfDefinition RingClass.ringClassFieldD
theorem ZInQ.Contrib.TYZGenus.Shimura.shimuraReciprocityPic_of_shimuraModFn
    (hS : Shimura.ShimuraReciprocityModFn) : Shimura.ShimuraReciprocityPic
-- ShimuraEtaInv.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.etaSqExp_closed : ∀ (fuel : ℕ) (a b c d : ℤ),
    c.natAbs ≤ fuel → a * d - b * c = 1 →
      (d % 2 = 1 → 12 ∣ Shimura.XfR a b c d - ZInQ.GZTheta.etaSqExp fuel a b c d) ∧
      (c % 2 = 1 → 12 ∣ Shimura.YfR a b c d - ZInQ.GZTheta.etaSqExp fuel a b c d)
theorem ZInQ.Contrib.TYZGenus.Shimura.yC_gamma0 :
    ∀ γ ∈ CongruenceSubgroup.Gamma0 32, ∀ (τ : UpperHalfPlane), X0.yC ↑(γ • τ) = X0.yC ↑τ
theorem ZInQ.Contrib.TYZGenus.Shimura.xC_sub_two_sq_gamma0 :
    ∀ γ ∈ CongruenceSubgroup.Gamma0 32, ∀ (τ : UpperHalfPlane),
      (X0.xC ↑(γ • τ) - 2) ^ 2 = (X0.xC ↑τ - 2) ^ 2
theorem ZInQ.Contrib.TYZGenus.Shimura.etaModelInvariant_of_equation :
    X0.EtaModelEquation → X0.EtaModelInvariant
-- ShimuraMain.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_cmValue
    (hV : Shimura.CMValueRingClass) (hI : X0.EtaModelInvariant) :
    CM.CMFieldOfDefinition RingClass.ringClassFieldD
theorem ZInQ.Contrib.TYZGenus.Shimura.cmValueRingClass_of_modFn :
    Shimura.ShimuraReciprocityModFn → Shimura.CMValueRingClass
theorem ZInQ.Contrib.TYZGenus.Shimura.shimuraReciprocityPic_of_modFn :
    Shimura.ShimuraReciprocityModFn → X0.EtaModelInvariant → Shimura.ShimuraReciprocityPic
-- ShimuraCusp.lean, ShimuraQExp.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.etaCuspGrowth : Shimura.EtaCuspGrowth
theorem ZInQ.Contrib.TYZGenus.Shimura.xQExpRational : Shimura.XQExpRational
theorem ZInQ.Contrib.TYZGenus.Shimura.yQExpRational : Shimura.YQExpRational
-- ShimuraField.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of
    (hS : Shimura.ShimuraReciprocityPic) : CM.CMFieldOfDefinition RingClass.ringClassFieldD
-- ShimuraZn.lean (earlier run; target since passed to cm-numeric)
theorem ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of
    (hS : Shimura.ShimuraReciprocityPic) (hF : X0.EtaModelFricke) : Package.TYZSigmaFixesZn
```

`#print axioms` (VERIFIED, `scratch/tyz-cm/ax5.lean`, `ax6.lean`, `ax7.lean`; Lean 4.35.0): every
declaration above depends on axioms `[propext, Classical.choice, Quot.sound]`. Built with
`lake build ZInQKernel.Contrib.TYZGenus.ShimuraTheta` (VERIFIED, 2026-11-13 11:21), after
`git merge origin/main` (b7cdba8e, clean).

`python3 ~/dzq-runs/tc/diffcheck2.py`: MOD-UNNOTED 0, NOTE-ONLY 0 (nothing vendored by this task;
the gz-theta files `GZTheta/Eta.lean`, `TripleProduct.lean`, `JacobiGauss.lean` are imported,
not modified).

## 2. The leaves (what remains)

Dependency graph:

```
CM.CMFieldOfDefinition ringClassFieldD ⇐ CMValueRingClass        (cmFieldOfDefinition_of_cmValueRingClass)
CMValueRingClass ⇐ ShimuraReciprocityModFn                        (cmValueRingClass_of_modFn)
ShimuraReciprocityPic ⇐ ShimuraReciprocityModFn                    (shimuraReciprocityPic_of_shimuraModFn)
Package.TYZSigmaFixesZn ⇐ ShimuraReciprocityPic ∧ X0.EtaModelFricke (ShimuraZn, earlier run)
X0.EtaModelInvariant: proved (etaModelInvariant)
```

| Leaf | File | Statement (informal) | Source | Refereed |
|---|---|---|---|---|
| `Shimura.CMValueRingClass` | ShimuraMain | for every `g ∈ ℚ(X₀(N))` regular on `ℍ` (`IsRatModFn N g`) and every Heegner form `Q` of level `N`, discriminant `D`: `g(τ_Q) = ιC(a)` with `a ∈ ringClassFieldD D` | main theorem of CM + rational structure of `X₀(N)`: Shimura 1971, Thm. 5.7, Prop. 6.9 / Thm. 6.23, §6.8; Gross 1984 §1–§3; Cox, *Primes of the form x²+ny²*, Thm. 11.1 (all numbers UNVERIFIED, from memory) | yes (textbooks) |
| `Shimura.ShimuraReciprocityModFn` (optional, stronger) | ShimuraModFn | Gross's form: if `ρ` acts on `H_O` as `Art([J∩O])` and `κ(J∩O)·(L', L'_N) = c·(L, L_N)` then `ρ(g(τ_Q)) = g(τ_{Q'})` | Shimura 1971 Thm. 5.4; Silverman GTM 151 Thm. II.8.2; Gross 1984 §3 (UNVERIFIED numbers) | yes |

`IsRatModFn N g` (ShimuraModFn, a definition, not a leaf): `g` is `Γ₀(N)`-invariant, for every
`γ ∈ SL₂(ℤ)` `g(γτ) = O(e^{2πk Im τ})` as `Im τ → ∞`, and `q^k g(τ) = Σ_{n≥0} a_n qⁿ` on `ℍ` with
`a_n ∈ ℚ`. These are exactly the functions of `ℚ(X₀(N))` with no poles on `ℍ` (q-expansion
principle; Shimura Prop. 6.9, Diamond–Shurman §7.5–7.7, UNVERIFIED numbers). Neither CM leaf
mentions x0-32's eta model, so their truth does not depend on x0-32's analytic leaves.
For x0-32's `x, y` all three conditions are proved (`isRatModFn_xC_of etaModelInvariant
etaCuspGrowth xQExpRational`, same for `y`).

For the target only `CMValueRingClass` is needed (the trivial class); it is the classical
statement "Heegner points of `X₀(N)` of discriminant `D` are defined over the ring class field",
for all forms, with no Heegner condition `(f, N) = 1` or `gcd(A/N, B, NC) = 1` (the lattice
`⟨1/N, τ⟩` has an order `O' ⊇ O_D` and `H_{O'} ⊆ H_D`). It does not depend on the direction
convention of the Artin map. `ShimuraReciprocityModFn` is used only by `ShimuraZn`.

## 3. What is proved (X₀(32)-specific and general glue)

* **Order/lattice computation** (ShimuraField): `κ(O) ⊆ ℤ + ℤ·Aτ_Q` for `O = ℤ + f𝓞_K` of
  discriminant `D` (`kappa_order`, parity of the half-integral coordinates of `𝓞_K`, both
  `m ≡ 3` and `m ≢ 3 (mod 4)`), hence `κ(O)·⟨1, τ_Q⟩ = ⟨1, τ_Q⟩` and
  `κ(O)·⟨1/N, τ_Q⟩ = ⟨1/N, τ_Q⟩` for every Heegner form (`kappa_mul_mem_lat`,
  `kappa_mul_mem_latN_gen`, `idealLat_top_mul`); `D = discOf (sqfPart |D|) (condD D)`; a normalized
  embedding `Kˢ → ℚ̄` exists for every `m` (`exists_normalized_embed_any`); infinite Galois theory
  (`InfiniteGalois.fixedField_fixingSubgroup`).
* **Rational q-expansions** (ShimuraQExp): `q²x(τ)` and `q³y(τ)` are power series in `q` with
  rational coefficients on all of `ℍ`. Method: functions with rational iterated derivatives at 0
  are closed under `+, ·, ⁻¹` (Leibniz); `p_d(q) = ∏(1 − q^{d(n+1)})` has rational Taylor
  coefficients (finite products stabilize; locally uniform limits commute with iterated
  derivatives, `TendstoLocallyUniformlyOn.deriv`); `Complex.hasSum_taylorSeries_on_ball`.
* **Growth at every cusp** (ShimuraCusp, `etaCuspGrowth`): `x(γτ), y(γτ) = O(e^{12π Im τ})` for
  all `γ ∈ SL₂(ℤ)`. Method: `H(w) = |η(w)|⁴ Im w` is `SL₂(ℤ)`-invariant (from Mathlib's
  `CuspForm.discriminant`, `Δ = η²⁴`); Hermite decomposition `diag(δ,1)γ = γ'[[g,t],[0,e]]`
  gives `|η(δγτ)|⁴·δ·Im(γτ) = H(w_δ)` with `Im τ/δ ≤ Im w_δ ≤ δ Im τ`; compactness bounds for
  `∏(1 − qⁿ)` on `|q| ≤ e^{−2π}`; then `|x − 2|⁴H₄H₃₂² = 64H₂²H₁₆`, `|y|⁴H₄²H₃₂⁴ = 16H₈⁴H₁₆²`.
* **`Γ₀(32)`-invariance of `x, y` (x0-32's `EtaModelInvariant`)** (ShimuraEtaInv, ShimuraTheta):
  gz-theta's Euclidean exponent of the `η²` multiplier satisfies
  `φ ≡ (a − 2d)c − bd(c² − 1) + 3d − 3 (mod 12)` for `d` odd, `≡ (a + d)c − bd(c² − 1) − 3c` for
  `c` odd (`etaSqExp_closed`; induction along the Euclidean recursion, each step a polynomial
  congruence checked in `ZMod 4`, `ZMod 3` by `decide`; tested first on 11 962 random matrices,
  `scratch/tyz-cm/etasq.py`). For `γ ∈ Γ₀(32)`, `η(δγτ)² = ζ^{X_δ}(cτ+d)η(δτ)²`, and for the
  even-exponent quotients `y`, `(x − 2)²` and `η(16)⁶/(η(8)²η(32)⁴)` the exponents combine to
  `−36bd`, `12(2k(a−2d) − bd(64k²+4))`, `−24bd`. The eta identity
  `x = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` (`xC_eq_even`; found by Ligozat's order formula,
  `scratch/tyz-cm/etaq.py`) is proved through Jacobi's triple product (gz-theta):
  `θ₀₁(4τ) = η(2τ)²/η(4τ)`, `θ₀₀(16τ) = AC²`, `θ(8τ;16τ) = 2AB²`, Euler `BCD = 1`, and the parity
  split `θ₀₁(4τ) = θ₀₀(16τ) − Q²θ(8τ;16τ)` (the series `Σ(−1)ⁿQ^{2n²}` split by the parity of `n`).
  Also `EtaModelInvariant ⇐ EtaModelEquation` by a sign argument (`etaModelInvariant_of_equation`,
  now superseded).
* **Heegner point from algebraic coordinates** (ShimuraModFn, `heegnerPt_of_alg`), and
  `ShimuraReciprocityPic` from the general leaf (`shimuraReciprocityPic_of`).

## 4. Why not the `j(τ), j(32τ)` route

The task suggested: coordinates of `X₀(32)` lie in `ℚ(j(τ), j(32τ))` (Shimura Prop. 6.9) and
`j(τ_Q), j(32τ_Q)` are CM values in `H_D`. As a statement about values at points this needs care:
`x ∈ ℚ(j, j_32)` as functions does not give `x(τ) ∈ ℚ(j(τ), j(32τ))` at points where `(j, j_32)`
does not separate points of `X₀(32)` (singular points of the plane model `Φ₃₂(X, Y) = 0`), and
formalizing `x` as an explicit rational function of `j, j_32` is out of reach (no `j` in Mathlib;
the expression has large degree). The leaf `CMValueRingClass` is the moduli version and avoids
both problems.

## 5. `ShimuraZn.lean` (for the integrator; target now owned by cm-numeric)

Committed by an earlier run of this task (8ca00d4d), left unchanged:
`tyzSigmaFixesZn_of (hS : ShimuraReciprocityPic) (hF : X0.EtaModelFricke) : Package.TYZSigmaFixesZn`.
It proves every TYZ-specific step: `𝔟 = (3+2√−n)𝓞_K ∩ O_{n,4} = ℤ⟨6+4√−n, 3−4n+8√−n⟩`;
the lattice identity `𝔟·(⟨1,τ_{Q'}⟩, ⟨1/32,τ_{Q'}⟩) = c·(⟨1,τ_Q⟩, ⟨1/32,τ_Q⟩)` with
`Q'_n = [16(n+9), −8(2n+15), 4n+25]`, `c = ((5n+9) − 2(n+3)√−n)/(n+9)`; `τ_{Q'} = N₀τ_Q`,
`N₀ = SWSW`, `φ(N₀τ) = φ(τ) + (0,0)` (from `φ(τ+1/2) = −φ(τ)` and the Fricke leaf); `σ_{1+2ϖ}`
fixes `i`. Combined with this task's `shimuraReciprocityPic_of_shimuraModFn`, `TYZSigmaFixesZn`
follows from `ShimuraReciprocityModFn ∧ X0.EtaModelFricke` (one line:
`tyzSigmaFixesZn_of (shimuraReciprocityPic_of_shimuraModFn hS) hF`; not stated as a theorem here
because the target belongs to cm-numeric). The numerics behind it
(`scratch/tyz-cm/twist*.py`, `coeffs*.py`; 18 values of `n`, 37 digits) are VERIFIED.

## 6. Caveats (kept visible)

* Reading A of TYZ Theorem 3.5 is not printed in any refereed text; TYZ was read in arXiv v1 only.
  `~/tyz-src/Period7.tex` is not on this host; TYZ line numbers are quoted from project notes.
* `z_n = (1 − [i])f₀(P_n)` comes from task tyz-t1 (AI-derived, checked numerically).
* The two CM leaves do not mention x0-32's eta model. The target `CM.CMFieldOfDefinition` is about
  the points `(x(τ_Q), y(τ_Q))` of the eta model; our proof uses only that `x, y ∈ ℚ(X₀(32))`
  (proved here), not x0-32's other analytic leaves. (If `X0.EtaModelEquation` failed, `heegnerPt Q`
  would be the junk value `0`, which also lies in every `ptsOver`.)
* Theorem numbers in the sources above are from memory (no network): UNVERIFIED.
* The direction convention of the Artin map (`Art(𝔟)` sends `L` to `𝔟⁻¹L`) matters only for
  `ShimuraReciprocityModFn`/`ShimuraReciprocityPic` (used by `ShimuraZn`), not for the main
  result; it was cross-checked numerically in the TYZ case (log, 09:30 numerics) and agrees with
  Silverman GTM 151 Thm. II.4.3 as remembered (UNVERIFIED).

## 7. Statement changes proposed

None. `CM.CMFieldOfDefinition` holds as stated (no Heegner condition is needed).

## 8. Not proved

* The two CM leaves (textbook theorems; Mathlib and Tau Ceti have no CM theory of elliptic curves).
* Not needed here but noted for x0-32's remaining leaves: with the theta forms above,
  `y = −θ₁₀(4τ)²/θ₁₀(16τ)²` and `x = 2θ₀₀(16τ)/θ₁₀(16τ)`, so `EtaModelEquation` (`y² = x³ + 4x`)
  is equivalent to `θ₁₀(τ/4)⁴ = 8θ₀₀θ₁₀(θ₀₀² + θ₁₀²)` (at `τ = 16τ₀`), which follows from the two
  duplication formulas `θ₁₀(τ)² = 2θ₀₀(2τ)θ₁₀(2τ)` and `θ₀₀(τ)² = θ₀₀(2τ)² + θ₁₀(2τ)²` (STANDARD;
  not formalized).
