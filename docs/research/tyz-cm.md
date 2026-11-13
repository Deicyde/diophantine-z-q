# tyz-cm: the CM leaf of the TYZ genus package

Task tyz-cm, 2026-11-13. Branch `wip/tyz-cm`. Files (all new, owned by tyz-cm):
`ZInQKernel/Contrib/TYZGenus/Shimura{Recip,Zn,Field,ModFn,QExp,Cusp,Main}.lean`.
Log: `scratch/tyz-cm/log.md`.

## 1. Main result

Target: cm-points' leaf `CM.CMFieldOfDefinition ringClassFieldD` (every Heegner point of
discriminant `D` on `X₀(32) = A`, through x0-32's `X0.phiC`, has coordinates in the ring class
field of discriminant `D`), and with it `Package.CMFieldOfDefinitionTYZ`.

**Status: reduced to one new textbook leaf plus one existing x0-32 leaf.** All
`X₀(32)`-specific steps are proved except `X0.EtaModelInvariant` (x0-32's leaf, unchanged).

```lean
-- ShimuraMain.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_cmValue
    (hV : Shimura.CMValueRingClass) (hI : X0.EtaModelInvariant) :
    CM.CMFieldOfDefinition RingClass.ringClassFieldD
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldTYZ_of_cmValue
    (hV : Shimura.CMValueRingClass) (hI : X0.EtaModelInvariant) :
    Package.CMFieldOfDefinitionTYZ
theorem ZInQ.Contrib.TYZGenus.Shimura.tyzThm35ReadingA_of_cmValue
    (h11 : TYZDecomp.TYZThm11Integral) (h1 : TYZDecomp.TYZLcalOne)
    (h29 : TYZDecomp.TYZLemma29Mod2) (hV : Shimura.CMValueRingClass)
    (hI : X0.EtaModelInvariant) (hs : Package.TYZSigmaFixesZn)
    (h318 : Package.Lemma318Literal RingClass.HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, TYZDecomp.IsTYZLcal ℓ → Package.GenusPointLeafCM ℓ) :
    ZInQ.Literature.TYZThm35ReadingA
theorem ZInQ.Contrib.TYZGenus.Shimura.cmValueRingClass_of_modFn :
    Shimura.ShimuraReciprocityModFn → Shimura.CMValueRingClass
theorem ZInQ.Contrib.TYZGenus.Shimura.shimuraReciprocityPic_of_modFn :
    Shimura.ShimuraReciprocityModFn → X0.EtaModelInvariant → Shimura.ShimuraReciprocityPic
-- ShimuraCusp.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.etaCuspGrowth : Shimura.EtaCuspGrowth
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of_modFn_inv
    (hS : Shimura.ShimuraReciprocityModFn) (hI : X0.EtaModelInvariant) :
    CM.CMFieldOfDefinition RingClass.ringClassFieldD
-- ShimuraQExp.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.xQExpRational : Shimura.XQExpRational
theorem ZInQ.Contrib.TYZGenus.Shimura.yQExpRational : Shimura.YQExpRational
-- ShimuraField.lean
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldOfDefinition_of
    (hS : Shimura.ShimuraReciprocityPic) : CM.CMFieldOfDefinition RingClass.ringClassFieldD
theorem ZInQ.Contrib.TYZGenus.Shimura.cmFieldTYZ_of_shimura
    (hS : Shimura.ShimuraReciprocityPic) : Package.CMFieldOfDefinitionTYZ
theorem ZInQ.Contrib.TYZGenus.Shimura.tyzThm35ReadingA_of_shimura (h11 h1 h29)
    (hS : Shimura.ShimuraReciprocityPic) (hF : X0.EtaModelFricke) (h318 hG) :
    ZInQ.Literature.TYZThm35ReadingA
-- ShimuraZn.lean (earlier run; target since passed to cm-numeric)
theorem ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of
    (hS : Shimura.ShimuraReciprocityPic) (hF : X0.EtaModelFricke) : Package.TYZSigmaFixesZn
```

`#print axioms` (VERIFIED, `scratch/tyz-cm/ax5.lean`, `ax.lean`, Lean 4.35.0): every declaration
above depends on axioms `[propext, Classical.choice, Quot.sound]`. Built with
`lake build ZInQKernel.Contrib.TYZGenus.ShimuraMain` (VERIFIED, 2026-11-13 10:57; also
`ShimuraField`, `ShimuraZn`).

`python3 ~/dzq-runs/tc/diffcheck2.py`: MOD-UNNOTED 0, NOTE-ONLY 0 (nothing vendored by this task).

## 2. The leaves (what remains)

Dependency graph for the target:

```
CM.CMFieldOfDefinition ringClassFieldD
  ⇐ CMValueRingClass ∧ X0.EtaModelInvariant                  (cmFieldOfDefinition_of_cmValue)
CMValueRingClass ⇐ ShimuraReciprocityModFn                   (cmValueRingClass_of_modFn)
ShimuraReciprocityPic ⇐ ShimuraReciprocityModFn ∧ X0.EtaModelInvariant
Package.TYZSigmaFixesZn ⇐ ShimuraReciprocityPic ∧ X0.EtaModelFricke   (ShimuraZn, earlier run)
```

| Leaf | File | Statement (informal) | Source | Refereed |
|---|---|---|---|---|
| `Shimura.CMValueRingClass` | ShimuraMain | for every `g ∈ ℚ(X₀(N))` regular on `ℍ` (`IsRatModFn N g`) and every Heegner form `Q` of level `N`, discriminant `D`: `g(τ_Q) = ιC(a)` with `a ∈ ringClassFieldD D` | main theorem of CM + rational structure of `X₀(N)`: Shimura 1971, Thm. 5.7, Prop. 6.9 / Thm. 6.23, §6.8; Gross 1984 §1–§3; Cox, *Primes of the form x²+ny²*, Thm. 11.1 (all numbers UNVERIFIED, from memory) | yes (textbooks) |
| `Shimura.ShimuraReciprocityModFn` (optional, stronger) | ShimuraModFn | Gross's form: if `ρ` acts on `H_O` as `Art([J∩O])` and `κ(J∩O)·(L', L'_N) = c·(L, L_N)` then `ρ(g(τ_Q)) = g(τ_{Q'})` | Shimura 1971 Thm. 5.4; Silverman GTM 151 Thm. II.8.2; Gross 1984 §3 (UNVERIFIED numbers) | yes |
| `X0.EtaModelInvariant` (x0-32, unchanged) | X0 | `x, y` invariant under `Γ₀(32)` | Ligozat / Newman / Gordon–Hughes eta-quotient criterion (Ono, *Web of modularity*, Thm. 1.64; UNVERIFIED) | yes |

`IsRatModFn N g` (ShimuraModFn, a definition, not a leaf): `g` is `Γ₀(N)`-invariant, for every
`γ ∈ SL₂(ℤ)` `g(γτ) = O(e^{2πk Im τ})` as `Im τ → ∞`, and `q^k g(τ) = Σ_{n≥0} a_n qⁿ` on `ℍ` with
`a_n ∈ ℚ`. These are exactly the functions of `ℚ(X₀(N))` with no poles on `ℍ` (q-expansion
principle; Shimura Prop. 6.9, Diamond–Shurman §7.5–7.7, UNVERIFIED numbers). Neither CM leaf
mentions x0-32's eta model; the model enters only through `EtaModelInvariant`.

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
fixes `i`. Combined with this task's `shimuraReciprocityPic_of_modFn`, `TYZSigmaFixesZn` follows from
`ShimuraReciprocityModFn ∧ X0.EtaModelInvariant ∧ X0.EtaModelFricke`. The numerics behind it
(`scratch/tyz-cm/twist*.py`, `coeffs*.py`; 18 values of `n`, 37 digits) are VERIFIED.

## 6. Caveats (kept visible)

* Reading A of TYZ Theorem 3.5 is not printed in any refereed text; TYZ was read in arXiv v1 only.
  `~/tyz-src/Period7.tex` is not on this host; TYZ line numbers are quoted from project notes.
* `z_n = (1 − [i])f₀(P_n)` comes from task tyz-t1 (AI-derived, checked numerically).
* All CM leaves are stated through x0-32's eta model `X0.phiC` only via `EtaModelInvariant`; they
  are true because that model is the `ℚ`-rational parametrization (x0-32's `X0AnalyticModel`).
* Theorem numbers in the sources above are from memory (no network): UNVERIFIED.
* The direction convention of the Artin map (`Art(𝔟)` sends `L` to `𝔟⁻¹L`) matters only for
  `ShimuraReciprocityModFn`/`ShimuraReciprocityPic` (used by `ShimuraZn`), not for the main
  result; it was cross-checked numerically in the TYZ case (log, 09:30 numerics) and agrees with
  Silverman GTM 151 Thm. II.4.3 as remembered (UNVERIFIED).

## 7. Statement changes proposed

None. `CM.CMFieldOfDefinition` holds as stated (no Heegner condition is needed).

## 8. Not proved

* `X0.EtaModelInvariant`. Partial analysis (not formalized): from the invariance of `H`,
  `|x(γτ) − 2| = |x(τ) − 2|` for `γ ∈ Γ₀(32)`, so `x∘γ − 2 = ε_γ(x − 2)` with `ε_γ^{24} = 1`, a
  character of `Γ₀(32)`. Showing `ε = 1` needs the eta multiplier (Dedekind sums / Petersson) or a
  generating set of `Γ₀(32)` with its multipliers; neither is in Mathlib or Tau Ceti.
* The two CM leaves (textbook theorems; Mathlib and Tau Ceti have no CM theory of elliptic curves).
