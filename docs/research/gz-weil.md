# gz-weil: the modular parametrization of `C_d` in Lean from Jacobi's derivative formula (no Eichler–Shimura, no Faltings)

Status: research note (task gz-weil, 2026-11-15), branch `wip/gz-weil` (base c118e9d2 = gz-hl3, merged with
gz-hl3's later commits up to bbb6c764). Lean: three new contributor files under
`ZInQKernel/Contrib/OneProof/GrossZagierHeegner/` (`Weil.lean`, `WeilParam.lean`, `WeilTheta.lean`). Nothing else
under `ZInQKernel/` was edited. Development files, checks and log: `scratch/gz-weil/`.

Marks. **VERIFIED**: read in a source named here, computed, or compiled. **STANDARD**: a published theorem with
an exact reference. **SPECULATIVE**: an assessment. This host has no network and no copy of Shimura, Faltings,
Cremona, Chandrasekharan or Rankin. **Every theorem number and locator of the literature below is UNVERIFIED.**

---

## 0. Main result

**On the route the proof uses (the curves `C_d`), gz-hl3's two composite leaves `StrongWeilCurve`
(Eichler–Shimura with a rational Manin constant) and `IsogenyLattice` (Faltings 1983, analytic form) are gone.
Their only consumer is the analytic parametrization `GZHL3.ShimuraCMParamCd`, which is now a Lean theorem from
one classical printed identity:**

```lean
-- WeilTheta.lean
theorem ZInQ.GZWeil.shimuraCMParamCd_of_jacobiLambdaDeriv (h : JacobiLambdaDeriv) :
    ZInQ.GZHL3.ShimuraCMParamCd

/-- Jacobi: λ = θ₂⁴/θ₃⁴ satisfies dλ/dt = πi λ θ₄⁴ on ℍ (over Mathlib's `jacobiTheta₂`). -/
def ZInQ.GZWeil.JacobiLambdaDeriv : Prop :=
  ∀ t : ℂ, 0 < t.im → HasDerivAt (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4)
    (π * I * (thetaTwo t ^ 4 / thetaThree t ^ 4) * thetaFour t ^ 4) t
```

with `thetaTwo t = e^{πit/4} jacobiTheta₂ (t/2) t = Σ e^{πi(n+1/2)²t}`, `thetaThree t = jacobiTheta₂ 0 t` and
`thetaFour t = jacobiTheta₂ (1/2) t`. All new theorems depend only on `[propext, Classical.choice, Quot.sound]`.
That is VERIFIED, compiled: `scratch/gz-weil/Check.lean`, output `out_check.txt`, 21 theorems.

Consequently (VERIFIED, compiled):

```lean
theorem ZInQ.GZWeil.grossZagierHeegnerCd_of_printed (hU : GZHL3.WeierstrassUniformization)
    (hJ : JacobiLambdaDeriv) (hHP : GZHL3.HeegnerPointRationalCd)
    (hGZ : GZHL3.GrossZagierFormulaCd) (hGC : GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd
```

`scratch/gz-weil/MainEdit.lean` proves `ZInQ.FrozenTarget` from `frozenTarget`'s open hypotheses, with `hL3`
replaced by these five leaves (`frozenTarget_gzweil`, standard axioms). It goes through gz-statements' proved chain
`GrossZagierHeegnerCd → GrossZagierCd`.

**The leaf count.** All counts are SPECULATIVE ratings as in gz-hl3; the leaves are read in §2.

| | parametrization leaves | composite (not printed) leaves in the split of `hL3` |
| --- | --- | --- |
| `hL3` itself | (folded in) | 1 |
| gz-hl3, general form | `WeierstrassUniformization`, `StrongWeilCurve`, `IsogenyLattice` | 3 (`StrongWeilCurve`, `IsogenyLattice`, `HeegnerPointRational`) |
| gz-hl3, `C_d` form | `WeierstrassUniformization`, `ShimuraCMParamCd` | 2 (`ShimuraCMParamCd`, `HeegnerPointRationalCd`) |
| **gz-weil, `C_d` form** | `WeierstrassUniformization`, **`JacobiLambdaDeriv` (printed form)** | **1 (`HeegnerPointRationalCd`)** |

So gz-weil removes two composite leaves from gz-hl3's split. The split of `hL3` on the `C_d` route now has one
composite, the Heegner point's rationality, which was outside this task. The other four leaves are printed (one
with its constant forgotten). Against `hL3` alone, the count of composites is now neutral (1 → 1), not negative.
Making it negative needs `HeegnerPointRational`; gz-hl3 §10 sketches that route.

**The general form is unchanged.** `hL3` as stated quantifies over every elliptic curve over `ℚ`, and for an
arbitrary `E` the parametrization still needs Eichler–Shimura and Faltings. The gain is on the `C_d` form,
gz-statements' `GrossZagierHeegnerCd`, which suffices for the headline (`GZStatements.Weak`, proved). The
integrator therefore has to replace `hL3` by the `C_d` chain (§5); `#discharges` cannot show it as a discharge of
`hL3` itself.

---

## 1. What the proof uses (VERIFIED, read)

* `StrongWeilCurve` and `IsogenyLattice` are used only in `GZHL3.eichlerShimuraParamAt_of_leaves`
  (`GrossZagierHeegner.lean` §5). That lemma feeds `grossZagierHeegner_of_leaves` (all `E`) and
  `shimuraCMParamCd_of_leaves` (`Cd.lean`).
* The chain to the headline uses `hL3` only at `E = C_d`, `d ≡ 5 (mod 8)` squarefree, in
  `GZDecomp.grossZagierCd_of_leaves`. The newform `f` there comes from `modular_cd`. gz-statements' `Weak.lean`
  proves that the restricted `GrossZagierHeegnerCd` closes the chain
  (`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`).
* So the parametrization that is used is exactly `GZHL3.ShimuraCMParamCd = ∀ d ≡ 5 (8) squarefree,
  EichlerShimuraParamAt C_d`. Inside it, the level is forced to `N = 32 d²`
  (`GZStatements.level_eq_of_coeff_cd`, proved). `eichler f` depends only on `aₙ(f) = aₙ(C_d) =
  heckeCoeff d n` (Deuring, `GZStatements.LFunction_cd_eq_heckeCoeff`, proved). So the statement is about one
  explicit function `Φ_d` per `d`.

---

## 2. The leaves, before and after

| Leaf | Statement | Source (UNVERIFIED locators) | Rating | Reason |
| --- | --- | --- | --- | --- |
| `GZHL3.StrongWeilCurve` (gz-hl3) | newform `f` with rational `aₙ` ⇒ `∃ E'/ℚ`, `aₙ(E') = aₙ(f)`, `c Λ_f ⊆ L(E')`, `c ∈ ℚ^×` | Shimura 1971 Thm 7.14; Manin 1972 | composite | **eliminated** on the `C_d` route |
| `GZHL3.IsogenyLattice` (gz-hl3) | `L(E) = L(E')` ⇒ `m L(E') ⊆ L(E)`, `m ∈ ℚ^×` | Faltings 1983 Kor. 2; Silverman VI.4.1 | composite | **eliminated** on the `C_d` route |
| `GZHL3.ShimuraCMParamCd` (gz-hl3, `Cd.lean`) | `EichlerShimuraParamAt C_d` for all `d ≡ 5 (8)` squarefree | Shimura, Nagoya Math. J. 43 (1971) | composite | **now a theorem** (`shimuraCMParamCd_of_jacobiLambdaDeriv`) |
| `GZWeil.ModularParamC1` (new, intermediate) | `∀ L` with `g₂ = 4, g₃ = 0` (lattice of `C₁ : y² = x³ − x`): `∃ c ∈ ℚ^×`, `c(Φ₁(γτ) − Φ₁(τ)) ∈ L` for `γ ∈ Γ₀(32)` | Eichler–Shimura for the one newform of level 32 | — | **a theorem** (`modularParamC1_of_jacobiLambdaDeriv`); also implied by gz-hl3's leaves (`modularParamC1_of_leaves`) |
| `X0.EtaModelDifferential` (x0-32's leaf, existing) | `x'(τ) = 4πi f₁(τ) y(τ)` on the eta-quotient model of `X₀(32)` | Manin constant 1 for 32a1 (Cremona) | — | **a theorem** (`etaModelDifferential_of_jacobiLambdaDeriv`) |
| **`GZWeil.JacobiLambdaDeriv`** (new) | `dλ/dt = πi λ θ₄⁴`, `λ = θ₂⁴/θ₃⁴` | Jacobi, *Fundamenta nova* (1829); Chandrasekharan, *Elliptic functions* (1985), Ch. VII; Rankin, *Modular forms and functions* (1977); Lawden (1989) §3 | **printed form** (textbook, classical) | a classical identity of theta constants, stated verbatim over Mathlib's `jacobiTheta₂`. It is equivalent to `d/dt log(θ₂/θ₃) = (πi/4) θ₄⁴`, and through the triple product to Jacobi's four-square identity. VERIFIED numerically (§4) |

What stays from gz-hl3's `C_d` split: `WeierstrassUniformization` (printed), `HeegnerPointRationalCd` (composite),
`GrossZagierFormulaCd` (printed, constant forgotten) and `GrossConjugationCd` (printed).

---

## 3. The proof (all VERIFIED, compiled)

### 3.1 The twist step: `ShimuraCMParamCd ⇐ ModularParamC1` (`Weil.lean`)

* `eichlerCd d z = Σ_{n≥1} heckeCoeff d n / n · e^{2πinz}`. It is summable on `ℍ`, from the elementary bound
  `|heckeCoeff d m| ≤ (2m + 1)³`.
* **Twist formula** (`twist_formula`): `d Φ_d(z) = Σ_{a mod d} 𝓕χ_d(a) Φ₁(z + a/d)`, where `χ_d = (·/d)` is
  gz-theta's `jacobiChar`. It follows from Fourier inversion on `ℤ/d` and `heckeCoeff d n = (n/d) heckeCoeff 1 n`.
* **Period identity** (`period_identity`): for `γ ∈ Γ₀(32 d²)` there are `γ'_a ∈ Γ₀(32)` and `τ'_a ∈ ℍ` with
  `d(Φ_d(γτ) − Φ_d(τ)) = Σ_a 𝓕χ_d(a)(Φ₁(γ'_a τ'_a) − Φ₁(τ'_a))`. This uses Tau Ceti's lemma moving
  `[1, a/d; 0, 1]` past `γ` (`exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom`) and reindexes
  `a ↦ aD²`, using `χ(D²) = 1`.
* **Gauss sum** (`jacobiChar_isPrimitive`, `dft_jacobiChar`, `gaussD_sq`): `(·/d)` is primitive for odd
  squarefree `d`. The proof builds `U ≡ 1 (mod d/p)` with `(U/p) = −1`. Hence `𝓕χ_d = g χ_d` with
  `g² = χ(−1)d = d`.
* **Scaling** (`scalePP`, `g₂_scalePP`, `g₃_scalePP`): `g₂(gL) = g⁻⁴ g₂(L)` and `g₃(gL) = g⁻⁶ g₃(L)`.
  `isPeriodLattice_cd_iff` gives `IsPeriodLattice C_d L ↔ g₂(L) = 4d², g₃(L) = 0`.
* **Assembly** (`periods_cd`): `gL_d` is a lattice of `C₁`, so `c(Φ₁(γ'τ') − Φ₁(τ')) = g m_a` with `m_a ∈ L_d`.
  Then `c(Φ_d(γτ) − Φ_d(τ)) = d⁻¹ Σ χ(a) g · g m_a = Σ χ(a) m_a ∈ L_d`. `eichlerShimuraParamAt_cd` adds
  `N = 32d²` and `eichler f = Φ_d`.

### 3.2 The uniformization step: `ModularParamC1 ⇐ X0.EtaModelDifferential` (`WeilParam.lean`)

The model: x0-32's eta quotients `x, y` on `ℍ`. tyz-cm proved `y² = x³ + 4x` (`etaModelEquation`) and
`Γ₀(32)`-invariance (`etaModelInvariant`). x0-32 proved that `y` and `f₁` do not vanish.

* **C1** `Φ₁' = 2πi f₁`. This is termwise differentiation (`hasDerivAt_tsum_of_isPreconnected`) together with
  gz-theta's `etaThetaIdentity`, `f₁ = Σ heckeCoeff 1 n qⁿ`.
* **C3** `Φ₁(γτ) − Φ₁(τ)` is constant for `γ ∈ Γ₀(32)`: `f₁` has weight 2 (gz-theta's `etaQuot32_slash_eq`),
  and the derivative of the Möbius map is `(cτ + d)⁻²`.
* **C4** `℘_L : ℂ ∖ L → ℂ` is onto. Its image is open (open mapping) and closed (reduce mod `L` to the compact
  closure of `ZSpan.fundamentalDomain`, and `℘ → ∞` at lattice points by Mathlib's `order_weierstrassP`).
* **C5** Take a lattice `L` of `32a1` (`g₂ = −16`, `g₃ = 0`) and `z₀` with `℘(z₀) = x(τ₀)`, `℘'(z₀) = 2y(τ₀)`
  (from C4, with the sign fixed by `z₀ ↦ −z₀`). Then `Ψ = ℘(Φ₁ + c₀) − x` satisfies `Ψ' = hΨ` near `τ₀`, with `h`
  analytic, because `℘'(w)² − 4y² = 4Ψ(℘² + ℘x + x² + 4)`. Since `Ψ(τ₀) = 0`, its order of vanishing is
  infinite (`analyticOrderAt_deriv_of_pos`). This replaces ODE uniqueness.
* **C6** `x = ℘(Φ₁ + c₀)` and `Φ₁ + c₀ ∉ L` on all of `ℍ`. The set where this holds locally is open, closed in
  `ℍ` (identity theorem; at a point mapping to `L`, `℘ → ∞` contradicts continuity of `x`) and nonempty.
* **C7** Put `ω = Φ₁(γτ) − Φ₁(τ)`. Then `℘(u + ω) = ℘(u)` on `Φ₁(ℍ) + c₀`, which is open by the local open
  mapping theorem. So it holds on the connected set `ℂ ∖ (L ∪ (L − ω))`. If `ω ∉ L`, `℘` would be bounded near
  `0`. Hence `ω ∈ L` (`period_mem`).
* **C8** For a lattice `L` of `C₁`, `((1 ± i)/2)L` are lattices of `32a1`. Both contain `ω`, so
  `2ω = (1 − i)ω + (1 + i)ω ∈ L`. That gives `ModularParamC1` with `c = 2`. No uniqueness of the lattice with
  given `g₂, g₃` is needed.

### 3.3 The eta identity from Jacobi's formula (`WeilTheta.lean`)

* `x = 2θ₃(16τ)/θ₂(16τ)` and `y = −θ₂(4τ)²/θ₂(16τ)²` (tyz-cm's `xC_theta`, `yC_theta`, with
  `θ₂(16τ) = Q²θ(8τ; 16τ)`).
* From `JacobiLambdaDeriv` and uniqueness of derivatives: `(θ₃/θ₂)'(t) = −(πi/4)(θ₃/θ₂)θ₄⁴`. Hence
  `x' = −4πi x θ₄(16τ)⁴`. Here `θ₂, θ₃ ≠ 0` from the product forms.
* `product_star`: `f₁ θ(2τ; 4τ)² = 2Q θ(0; 16τ) θ(8τ; 16τ) θ(1/2; 16τ)⁴`. It follows from the product forms
  (gz-theta's triple product; tyz-cm's `theta_k_2k`, `theta00_sixteen`, `theta_eight_sixteen`, and the new
  `theta_half_sixteen`), `η = q^{1/24}∏(1 − qⁿ)` and Euler's identity `euler_BCD`. It turns
  `−x θ₄(16τ)⁴` into `f₁ y`, so `x' = 4πi f₁ y`.

---

## 4. Are the statements right? (VERIFIED where marked)

* **`JacobiLambdaDeriv` is true** (VERIFIED numerically, `scratch/gz-weil/lambda_check.py`). The central
  difference of `θ₂⁴/θ₃⁴` matches `πiλθ₄⁴` to `4·10⁻¹⁰` at `t = 0.3 + 0.8i`, `−0.2 + 1.1i` and `0.45 + 0.6i`
  (series truncated at `|n| ≤ 60`). It is classical. The printed locators are UNVERIFIED, so it enters as printed
  form, unread.
* **It is not vacuous or inert.** `etaModelDifferential_of_jacobiLambdaDeriv` applies it at `t = 16τ` for every
  `τ ∈ ℍ`.
* **`X0.EtaModelDifferential` is true** (VERIFIED, exact integer `q`-series, `scratch/gz-weil/etadiff_check.py`):
  `q dx/dq = 2yf` to `q^113`. The same script checks `y² = x³ + 4x` to `q^109` and `f = Σ heckeCoeff 1 n qⁿ` to
  `q^119`. `product_star` is also VERIFIED numerically (error `10⁻¹⁶`).
* **`ModularParamC1` is no stronger than gz-hl3's leaves.** `modularParamC1_of_leaves` derives it from
  `WeierstrassUniformization`, `StrongWeilCurve` and `IsogenyLattice` (compiled). It is now a theorem anyway.
* **Genuine definitions.** Mathlib's `PeriodPair` (`℘`, `g₂`, `g₃`), `jacobiTheta₂`, `CongruenceSubgroup.Gamma0`,
  `ZMod.dft`, `gaussSum` and `DirichletCharacter.IsPrimitive`; the kernel's `heckeCoeff`, `jacobiChar`, x0-32's
  `xC`, `yC`, `fC` and gz-hl3's `eichler`, `PeriodsIn`, `IsPeriodLattice`. No structure was invented.
* **Statements unchanged.** `ShimuraCMParamCd`, `EichlerShimuraParamAt`, `X0.EtaModelDifferential` and
  `GrossZagierHeegnerCd` are used verbatim from their defining modules.

---

## 5. Integration

* **Contributor files.**
  - `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Weil.lean` (twist step; imports `GrossZagierHeegner.Cd`,
    `GZStatements.Level`, Tau Ceti `Cusps.Basic`).
  - `.../WeilParam.lean` (uniformization; imports `Weil`, `TYZGenus.ShimuraThetaDup`, `GZTheta.EtaForm32`,
    `GZTheta.EtaTheta`).
  - `.../WeilTheta.lean` (Jacobi's formula; imports `WeilParam`).

  None imports `OneProof.Main`. `lake build ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilTheta`: success
  (11341 jobs).
* **`#discharges`** (`scratch/gz-weil/Discharges.lean` → `discharges-output.txt`): 65 open hypotheses, 1434
  theorems checked, 6 discharge one. The six are the same as before, including gz-hl3's general discharge of
  `hL3`. The new theorems discharge no open hypothesis directly, as expected: `hL3` is stated for all `E`, and
  the new leaves cover `C_d`.
* **The `Main.lean` edit** (checked out of tree: `scratch/gz-weil/MainEdit.lean`, `frozenTarget_gzweil`,
  standard axioms):
  1. add `import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilTheta`;
  2. replace the binder `(hL3 : ZInQ.GZDecomp.GrossZagierHeegner)` by
     `(hU : ZInQ.GZHL3.WeierstrassUniformization) (hJ : ZInQ.GZWeil.JacobiLambdaDeriv)
     (hHP : ZInQ.GZHL3.HeegnerPointRationalCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
     (hGC : ZInQ.GZHL3.GrossConjugationCd)`;
  3. replace the body's call of `GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves … hL3` by
     `ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
     (HDec.HSyn.sixContactMin_of_open27 r t l g) (tyzThm35ReadingA_of_leaves …)
     (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing hL2)
     (ZInQ.GZWeil.grossZagierHeegnerCd_of_printed hU hJ hHP hGZ hGC)`
     (verbatim in `MainEdit.lean`).

  `kinds.tsv` then has five rows in place of `hL3`:
  - `WeierstrassUniformization`: LEAF, textbook, printed form;
  - `JacobiLambdaDeriv`: LEAF, textbook, printed form, unread;
  - `HeegnerPointRationalCd`: LEAF, composite;
  - `GrossZagierFormulaCd` and `GrossConjugationCd`: LEAF, research, printed form, unread.

  Each needs a `locators.md` row. Alternatively, with `X0.EtaModelDifferential` in place of `JacobiLambdaDeriv`:
  `frozenTarget_gzweil'`.

---

## 6. What remains

* **`JacobiLambdaDeriv` could itself be proved.** Two routes:
  - through the triple product (proved in the kernel): `d/dt log(θ₂/θ₃)` is a Lambert series, so the formula is
    Jacobi's four-square identity `θ₄⁴ = 1 + 8Σ(−1)^m m q^m/(1 + q^m)` (Hirschhorn's elementary proof uses only
    the triple product);
  - through modular forms of level 1: symmetric functions of the three permuted identities are level-one cusp
    forms of weight `< 12`.

  Either would make the parametrization of `C_d` a theorem outright. This task did not attempt it.
* **`HeegnerPointRationalCd`** is the last composite leaf of the `C_d` split (gz-hl3 §10).
* **The general form of `hL3`** (all `E/ℚ`) still needs Eichler–Shimura and Faltings. The present result does not
  apply to it.
* **Literature check.** Read the printed form of Jacobi's derivative formula (any of the books in §2). Since the
  formula is numerically exact, the check concerns the normalization: `θ₂ = Σ e^{πi(n+1/2)²t}` and the factor
  `πi`.

---

## 7. Reproduction

```
lake build ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilTheta
lake env lean scratch/gz-weil/Check.lean          # #print axioms → out_check.txt
lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
lake env lean scratch/gz-weil/Discharges.lean     # → discharges-output.txt
lake env lean scratch/gz-weil/MainEdit.lean       # frozenTarget_gzweil, axioms
python3 scratch/gz-weil/etadiff_check.py          # exact q-series checks
python3 scratch/gz-weil/lambda_check.py           # Jacobi's formula and product_star, numerically
```

Development files: `scratch/gz-weil/Twist.lean` (= `Weil.lean`), `Unif.lean` (= `WeilParam.lean` with copies) and
`Lambda.lean` (= `WeilTheta.lean`).
