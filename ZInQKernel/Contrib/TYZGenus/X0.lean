import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import ZInQKernel.Contrib.TYZDecomp.CurveA

/-!
# x0-32: the modular curve `X₀(32)` over Mathlib's objects

Report: `docs/research/x0-32.md`. Owner: task x0-32 (wave of the TYZ genus-point split; the sibling
files `TYZGenus/RingClass.lean` and `TYZGenus/CM.lean`, `TYZGenus/Package.lean` belong to the tasks
ring-class and cm-points).

`X₀(32)` has genus one; with the cusp `∞` as origin it is an elliptic curve over `ℚ`, the optimal
curve `32a1 : y² = x³ + 4x` of the conductor-32 isogeny class (Cremona's labels; UNVERIFIED from
memory). That is the curve `CurveA.curveA` of `TYZDecomp/CurveA.lean` (`ℚ`-isomorphic to TYZ's
`A : 2y² = x³ + x`). This file

* §1 fixes the four curves of the isogeny class `32a` as Weierstrass curves over `ℚ`:
  `curveX0 = y² = x³ + 4x` (= `curveA`), `curveC1 = y² = x³ − x` (`C₁`, the congruent-number curve
  for `n = 1`), `curve32a3 = y² = x³ − 11x − 14`, `curve32a4 = y² = x³ − 11x + 14`;
* §2 defines the analytic model of `X₀(32)` by eta quotients over Mathlib's `ModularForm.eta`:
  `x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2`, `y = −η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴)`, the newform
  `f = η(4τ)²η(8τ)²`, and the map `phiC : ℍ → A(ℂ)`;
* §3 states, as leaves (`def … : Prop`, not proved here), the identities that make
  `τ ↦ (x(τ), y(τ))` the modular parametrization `X₀(32) ≅ A` with `dx/2y = 2πi f(τ) dτ`, its cusp
  dictionary, and the modularity `f = Σ aₙ(A) qⁿ` (each VERIFIED numerically, see the docstrings);
* §4–§10 (proved) relate `X₀(32) = A` and `C₁`: `ι : A ≅ C₁` over `ℚ(i)` (`(x, y) ↦ (w²x, w³y)`,
  `w = (1 + i)/2`); the `2`-isogenies `φ = ι ∘ (1 + [i]) : A → C₁` and `ψ = (1 − [i]) ∘ ι⁻¹`,
  additive, with `ψ ∘ φ = 2`, `φ ∘ ψ = 2`, the rational formulas
  `φ(x, y) = (y²/4x², y(x² − 4)/8x²)`, `ψ(x, y) = (y²/x², y(x² + 1)/x²)` and `Gal(ℚ̄/ℚ)`-equivariance;
  `A[(1+i)³]` listed explicitly (`two_nsmul_add_iPt_eq_zero_iff`), hence the half
  `A[(1+i)³] ⊆ A(ℚ(i))` of TYZ Lemma 3.16 (`lemma316_mpr`, `tyzLemma316_iff`); discriminants,
  `c₄`, `j`; `X₀(32) ≇ C₁` over `ℚ` (`not_exists_variableChange_X0_C1`) but `≅` over `ℚ(i)`
  (`isoVC_smul`); and the cusp images of §2 are `A[(1+i)³]` (`isCuspImage_toC`).
* §11–§12 (proved) basic analytic facts: `x, y, f` are holomorphic on `ℍ`, `f` and `y` have no
  zeros there, `phiC τ = (x(τ), y(τ))` under `EtaModelEquation`, and `x, y, f` are invariant under
  `T = [[1,1],[0,1]] ∈ Γ₀(32)` (`xC_yC_fC_T_smul`, a piece of `EtaModelInvariant`).
* §14 (proved) the Fricke involution on the eta quotients: `xC_fricke`, `yC_fricke`, and
  `fC_fricke : f(−1/(32τ)) = −32τ² f(τ)` (`f` is a `W₃₂`-eigenform, eigenvalue `−1`).
* §13 (proved) `x, y, f` have real `q`-expansions: `η(−z̄) = conj η(z)` and
  `phiC (−τ̄) = conj (phiC τ)` (`phiC_neg_conj`), the analytic input for complex conjugation on
  Heegner points.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Complex

namespace ZInQ.Contrib.TYZGenus.X0

open ZInQ.Contrib.TYZDecomp.CurveA

/-! ## §1 The isogeny class `32a` over `ℚ` -/

/-- **`X₀(32)` as a Weierstrass curve over `ℚ`**: `y² = x³ + 4x` (Cremona `32a1`, the optimal
curve of conductor 32; `X₀(32)` has genus one and this is its model with origin the cusp `∞`).
Definitionally `CurveA.curveA`. -/
abbrev curveX0 : WeierstrassCurve ℚ := curveA

/-- `C₁ : y² = x³ − x` (Cremona `32a2`), syntactically `TYZDecomp.curveC 1`. -/
abbrev curveC1 : WeierstrassCurve ℚ := shortCurve (-((1 : ℕ) : ℚ) ^ 2)

/-- `y² = x³ − 11x − 14` (Cremona `32a3`, label UNVERIFIED), the image of `C₁` under the
`2`-isogeny with kernel `⟨(1, 0)⟩` (Vélu; computed by hand, not proved here). -/
def curve32a3 : WeierstrassCurve ℚ := ⟨0, 0, 0, -11, -14⟩

/-- `y² = x³ − 11x + 14` (Cremona `32a4`, label UNVERIFIED), the image of `C₁` under the
`2`-isogeny with kernel `⟨(−1, 0)⟩` (Vélu; computed by hand, not proved here). -/
def curve32a4 : WeierstrassCurve ℚ := ⟨0, 0, 0, -11, 14⟩

/-! ## §2 The analytic model: eta quotients on `ℍ` -/

/-- `η(d z)` with Mathlib's Dedekind eta `η(z) = e^{2πiz/24} ∏ₙ (1 − e^{2πi(n+1)z})`. -/
def etaD (d : ℕ) (z : ℂ) : ℂ := ModularForm.eta ((d : ℂ) * z)

/-- `x(z) = η(2z)²η(16z) / (η(4z)η(32z)²) + 2 = q⁻² + 2 − 2 + … `
(`q = e^{2πiz}`; the eta quotient is `q⁻²(1 − 2q² + 2q⁸ + …)`). -/
def xC (z : ℂ) : ℂ := etaD 2 z ^ 2 * etaD 16 z / (etaD 4 z * etaD 32 z ^ 2) + 2

/-- `y(z) = −η(8z)⁴η(16z)² / (η(4z)²η(32z)⁴) = −q⁻³(1 + 2q⁴ + q⁸ + …)`. -/
def yC (z : ℂ) : ℂ := -(etaD 8 z ^ 4 * etaD 16 z ^ 2 / (etaD 4 z ^ 2 * etaD 32 z ^ 4))

/-- The weight-two newform of level 32: `f(z) = η(4z)²η(8z)² = q − 2q⁵ − 3q⁹ + 6q¹³ + …`. -/
def fC (z : ℂ) : ℂ := etaD 4 z ^ 2 * etaD 8 z ^ 2

/-- `X₀(32) = A` over `ℂ`. -/
abbrev curveAC : WeierstrassCurve ℂ := curveA.baseChange ℂ

/-- Classical decidable equality on `ℂ` (for Mathlib's group law on points). -/
instance : DecidableEq ℂ := Classical.decEq _

/-- `A(ℂ)`. -/
abbrev PtAC : Type := curveAC.toAffine.Point

open Classical in
/-- **The modular parametrization `ℍ → X₀(32)(ℂ) = A(ℂ)`**, `τ ↦ (x(τ), y(τ))` (the `else` branch
is never taken under `EtaModelEquation`). -/
def phiC (τ : UpperHalfPlane) : PtAC :=
  if h : curveAC.toAffine.Nonsingular (xC τ) (yC τ) then .some (xC τ) (yC τ) h else 0

/-- The images of the eight cusps of `Γ₀(32)`: `O` (from `∞`) and the seven affine points
`(0,0), (2,±4), (−2,±4i), (±2i,0)`, i.e. `A[(1+i)³] = A(ℚ(i))`. -/
def IsCuspImage : PtAC → Prop
  | .zero => True
  | .some x y _ => (x, y) ∈ ({(0, 0), (2, 4), (2, -4), (-2, 4 * I), (-2, -4 * I), (2 * I, 0),
      (-2 * I, 0)} : Set (ℂ × ℂ))

/-! ## §3 The leaves of the analytic model (`def … : Prop`; not proved here) -/

/-- **Leaf X0-EQ** (the eta-quotient model satisfies the Weierstrass equation of `32a1`):
`y(τ)² = x(τ)³ + 4x(τ)` on `ℍ`.

Content: an identity of eta quotients, a finite check by the Sturm bound once `x, y` are known to be
modular functions on `Γ₀(32)` (`EtaModelInvariant`). VERIFIED numerically here: the two
`q`-expansions agree to `O(q³⁴)` (exact integer arithmetic, `scratch/x0-32/eta.py`). Printed
source for the eta-quotient model: none located on this host; Ligozat, *Courbes modulaires de genre
1*, Bull. SMF Mém. 43 (1975) gives eta-quotient models of the genus-one `X₀(N)` (that it prints these
two quotients for `N = 32`: UNVERIFIED). -/
def EtaModelEquation : Prop :=
  ∀ τ : UpperHalfPlane, yC τ ^ 2 = xC τ ^ 3 + 4 * xC τ

/-- **Leaf X0-INV** (`x, y` are modular functions on `Γ₀(32)`): invariance under `Γ₀(32)`.

Source: Ligozat's criterion for eta quotients (Ligozat 1975, op. cit.; also Gordon–Hughes–Newman;
locators UNVERIFIED): `Σ r_δ = 0`, `Σ δr_δ ≡ Σ (32/δ)r_δ ≡ 0 (mod 24)`, `∏ δ^{r_δ}` a square, all
VERIFIED for both exponent vectors `(r₁,…,r₃₂) = (0,2,−1,0,1,−2)`, `(0,0,−2,4,2,−4)`. -/
def EtaModelInvariant : Prop :=
  ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma0 32 →
    ∀ τ : UpperHalfPlane, xC ↑(γ • τ) = xC τ ∧ yC ↑(γ • τ) = yC τ

/-- **Leaf X0-BIJ** (`X₀(32) ≅ A`, analytically): `τ ↦ (x(τ), y(τ))` induces a bijection
`Γ₀(32)\ℍ ≅ A(ℂ) ∖ A[(1+i)³]`; the eight cusps go to `A[(1+i)³]`.

Source: `X₀(32)` is the optimal curve `32a1` (modular degree 1; Cremona, *Algorithms for modular
elliptic curves*, 2nd ed. 1997, Table 1: UNVERIFIED locator); by Ligozat's order formula `x, y` have
poles only at `∞`, of orders 2 and 3, so `(x, y) : X₀(32) → A` has degree one; the cusps are torsion
(Manin–Drinfeld) and defined over `ℚ(i)`, so they go to `A(ℚ(i))_tors = A[(1+i)³]` (8 points, 8
cusps). The cusp images are VERIFIED numerically (`CuspDictionary`). -/
def EtaModelBijective : Prop :=
  (∀ τ τ' : UpperHalfPlane, phiC τ = phiC τ' ↔
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma0 32 ∧ γ • τ = τ') ∧
    Set.range phiC = {P | ¬ IsCuspImage P}

/-- **Leaf X0-DIFF** (the parametrization is the modular parametrization, Manin constant `1`):
`dx/(2y) = 2πi f(τ) dτ`, i.e. `x'(τ) = 4πi f(τ) y(τ)` on `ℍ`. With `X0-BIJ` this says that
`τ ↦ (x, y)` is the map `τ ↦ ∫_{i∞}^τ 2πi f` followed by the Weierstrass uniformization of `A`.

VERIFIED numerically (`q d x/dq = 2 y f` to `O(q⁷⁸)`, exact). Printed source: the Manin constant of
`32a1` is `1` (Cremona's tables; UNVERIFIED locator); the explicit identity is a computation. -/
def EtaModelDifferential : Prop :=
  ∀ τ : UpperHalfPlane, HasDerivAt xC (4 * Real.pi * I * fC τ * yC τ) τ

/-- **Leaf X0-NEWFORM** (modularity of `32a`, explicit): the `q`-expansion coefficients of
`f = η(4τ)²η(8τ)²` are the Dirichlet coefficients of Mathlib's `L(A, s)`:
`f(τ) = Σₙ aₙ(A) qⁿ`, `q = e^{2πiτ}`.

Sources (refereed): Koblitz, *Introduction to elliptic curves and modular forms*, GTM 97, Ch. IV
(the curves `y² = x³ − n²x`, `f = η(4z)²η(8z)²`; proposition number UNVERIFIED); Martin–Ono,
*Eta-quotients and elliptic curves*, Proc. AMS 125 (1997), table (conductor 32: `η(4z)²η(8z)²`;
UNVERIFIED locator). `L(A,s) = L(C₁,s)` (isogenous, §2). VERIFIED numerically: `aₙ` from the Euler
product of point counts agree with the eta product for `n < 80` (`scratch/x0-32/newf.py`). -/
def NewformEta32 : Prop :=
  ∀ τ : UpperHalfPlane,
    HasSum (fun n : ℕ => (curveA.LFunction n : ℂ) * cexp (2 * Real.pi * I * τ) ^ n) (fC τ)

/-- **Leaf X0-CUSP** (`f` is a cusp form of weight 2 on `Γ₀(32)`). Source: Ligozat's /
Gordon–Hughes–Newman's eta-quotient criterion (orders at the cusps of `η(4z)²η(8z)²` are all
positive; VERIFIED by Ligozat's formula), Martin–Ono 1997 (UNVERIFIED locator). -/
def CuspFormEta32 : Prop :=
  ∃ F : CuspForm ((CongruenceSubgroup.Gamma0 32 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) 2, ∀ τ : UpperHalfPlane, F τ = fC τ

/-- **Leaf X0-DICT** (the cusp dictionary, Tian 2014 fact (3) as quoted by TYZ L1393–1404): along
vertical paths `r + it`, `t → 0⁺`, `(x, y)` tends to `[0] ↦ (2,−4)`, `[1/2] ↦ (2,4)`,
`[1/4] ↦ (−2,−4i)`, `[−1/4] ↦ (−2,4i)`, `[1/8] ↦ (−2i,0)`, `[−1/8] ↦ (2i,0)`, `[1/16] ↦ (0,0)`;
and `|x| → ∞` at `∞`. VERIFIED numerically here (`scratch/x0-32/cusps.py`, `t = 10⁻³`, 6 digits),
and it agrees with the PARI modular-symbol computation of `rv-tyz-inputs.md` §1.5a. -/
def CuspDictionary : Prop :=
  (∀ r ∈ ({(0, 2, -4), (1 / 2, 2, 4), (1 / 4, -2, -4 * I), (-1 / 4, -2, 4 * I),
      (1 / 8, -2 * I, 0), (-1 / 8, 2 * I, 0), (1 / 16, 0, 0)} : Set (ℝ × ℂ × ℂ)),
    Filter.Tendsto (fun t : ℝ => (xC (r.1 + t * I), yC (r.1 + t * I))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds r.2)) ∧
  Filter.Tendsto (fun t : ℝ => ‖xC (t * I)‖) Filter.atTop Filter.atTop

/-- **The Eichler integral of `f`**, `F(τ) = 2πi ∫_{i∞}^τ f = Σ_{m ≥ 1} (a_m/m) qᵐ`, with `a_m` the
coefficients of Mathlib's `L(A, s)` (the same expression as `TYZGenus.CM.modParam` of task
cm-points, so the two are equal by unfolding). -/
def modParamF (τ : ℂ) : ℂ :=
  ∑' m : ℕ, (((curveA.LFunction m : ℤ) : ℂ) / m) * Complex.exp (2 * Real.pi * I * m * τ)

/-- **Leaf X0-WEIERSTRASS** (the eta-quotient model is the modular parametrization through the
Weierstrass uniformization): for any period pair `L` with `g₂(L) = −16`, `g₃(L) = 0` (so that
`z ↦ (℘(z), ℘'(z)/2)` lands on `y² = x³ + 4x`), and every `τ ∈ ℍ`, `F(τ) ∉ L` and
`x(τ) = ℘_L(F(τ))`, `y(τ) = ℘'_L(F(τ))/2`.

Content: with `X0-EQ`, `X0-DIFF` and `X0-NEWFORM`, the elliptic logarithm of `(x(τ), y(τ))` has
derivative `dx/2y = 2πi f dτ = dF`, and both tend to `0` as `τ → i∞`, so they agree; the lattice
of `A` is the period lattice of `2πi f` because the Manin constant of `32a1` is `1` (Cremona's
tables; UNVERIFIED locator). STANDARD given those leaves; not proved here (needs the elliptic
logarithm, absent from Mathlib). Sign and normalization VERIFIED numerically (`x ~ q⁻²`,
`y ~ −q⁻³`, `F ~ q`). -/
def EtaModelWeierstrass : Prop :=
  ∀ L : PeriodPair, L.g₂ = -16 → L.g₃ = 0 → ∀ τ : UpperHalfPlane,
    modParamF τ ∉ L.lattice ∧ xC τ = L.weierstrassP (modParamF τ) ∧
      yC τ = L.derivWeierstrassP (modParamF τ) / 2

theorem nonsingular_TC : curveAC.toAffine.Nonsingular 2 (-4) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  have h4 : curveAC.a₄ = 4 := by simp [curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have h0 : curveAC.a₁ = 0 ∧ curveAC.a₂ = 0 ∧ curveAC.a₃ = 0 ∧ curveAC.a₆ = 0 := by
    simp [curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  rw [h4, h0.1, h0.2.1, h0.2.2.1, h0.2.2.2]
  refine ⟨by norm_num, Or.inr ?_⟩
  norm_num

/-- `T = (2, −4) ∈ A(ℂ)`, the image of the cusp `0` (`τ(1/2)` in TYZ's notation). -/
def ptTC : PtAC := .some 2 (-4) nonsingular_TC

/-- **Leaf X0-FRICKE** (the Fricke involution `W₃₂ : τ ↦ −1/(32τ)` on `X₀(32) = A`):
`φ(W₃₂τ) + φ(τ) = T = (2, −4)`, i.e. `W₃₂` acts on `A` as `P ↦ T − P` (`W₃₂`-eigenvalue `−1` on
`f`, root number `+1` of `A`; `W₃₂` swaps the cusps `∞ ↦ 0`, `O ↦ T`).

VERIFIED numerically here (`scratch/x0-32/fricke.py`, three `τ`, 12 digits). Exact forms PROVED in
§14 from Mathlib's `η(−1/z) = (√i)⁻¹√z η(z)`: `x(W₃₂τ) = 2 + 8η(2τ)η(16τ)²/(η(τ)²η(8τ))` (`xC_fricke`),
`y(W₃₂τ) = −4η(2τ)²η(4τ)⁴/(η(τ)⁴η(8τ)²)` (`yC_fricke`), `f(W₃₂τ) = −32τ²f(τ)` (`fC_fricke`); what
remains of this leaf is the eta identity saying that these are the coordinates of `T − (x, y)`. The
action of `W_N` on the modular parametrization (`φ ∘ W_N = −w_N φ + φ(0)`, `w_N` the
`W_N`-eigenvalue): STANDARD (e.g. Darmon, *Rational points on modular elliptic curves*, CBMS 101,
§2; locator UNVERIFIED); used by TYZ (rv-tyz-inputs §1.5: "`[∞]^W = [0]`"). -/
def EtaModelFricke : Prop :=
  ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = -1 / (32 * (τ : ℂ)) → phiC τ' + phiC τ = ptTC

/-- The analytic model of `X₀(32)`: the conjunction of the nine leaves of §3. -/
def X0AnalyticModel : Prop :=
  EtaModelEquation ∧ EtaModelInvariant ∧ EtaModelBijective ∧ EtaModelDifferential ∧
    NewformEta32 ∧ CuspFormEta32 ∧ CuspDictionary ∧ EtaModelWeierstrass ∧ EtaModelFricke

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §4 Scaling maps between short Weierstrass curves -/

section Scale

variable {F : Type*} [Field F] [DecidableEq F]

set_option linter.unusedSectionVars false

/-- `W, W'` are short Weierstrass curves (`a₁ = a₂ = a₃ = 0`) and `(x, y) ↦ (w²x, w³y)` maps `W`
to `W'`: `a₄' = w⁴a₄`, `a₆' = w⁶a₆`, `w ≠ 0`. -/
structure IsScale (W W' : WeierstrassCurve F) (w : F) : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0
  a₁' : W'.a₁ = 0
  a₂' : W'.a₂ = 0
  a₃' : W'.a₃ = 0
  a₄ : W'.a₄ = w ^ 4 * W.a₄
  a₆ : W'.a₆ = w ^ 6 * W.a₆
  ne : w ≠ 0

variable {W W' W'' : WeierstrassCurve F} {w w' : F}

theorem IsScale.nonsingular (hs : IsScale W W' w) {x y : F} (h : W.toAffine.Nonsingular x y) :
    W'.toAffine.Nonsingular (w ^ 2 * x) (w ^ 3 * y) := by
  rw [nonsingular_iff', equation_iff'] at h ⊢
  rw [hs.a₁, hs.a₂, hs.a₃] at h
  rw [hs.a₁', hs.a₂', hs.a₃', hs.a₄, hs.a₆]
  obtain ⟨he, hn⟩ := h
  have hw := hs.ne
  refine ⟨by linear_combination w ^ 6 * he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    have : w ^ 4 * (0 * y - (3 * x ^ 2 + 2 * 0 * x + W.a₄)) = 0 := by linear_combination h'
    simpa [hw] using this
  · right
    intro h'
    apply h
    have : w ^ 3 * (y - (-y - 0 * x - 0)) = 0 := by linear_combination h'
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hw)
    linear_combination this

/-- The scaling map `W(F) → W'(F)`, `(x, y) ↦ (w²x, w³y)`. -/
def scalePt (hs : IsScale W W' w) : W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (w ^ 2 * x) (w ^ 3 * y) (hs.nonsingular h)

theorem scalePt_some (hs : IsScale W W' w) {x y : F} (h : W.toAffine.Nonsingular x y) :
    scalePt hs (.some x y h) = .some (w ^ 2 * x) (w ^ 3 * y) (hs.nonsingular h) := rfl

theorem scalePt_zero (hs : IsScale W W' w) : scalePt hs 0 = 0 := rfl

theorem IsScale.slope (hs : IsScale W W' w) (x₁ x₂ y₁ y₂ : F) :
    W'.toAffine.slope (w ^ 2 * x₁) (w ^ 2 * x₂) (w ^ 3 * y₁) (w ^ 3 * y₂) =
      w * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hw := hs.ne
  by_cases hx : x₁ = x₂
  · have hx' : w ^ 2 * x₁ = w ^ 2 * x₂ := by rw [hx]
    by_cases hy : y₁ = W.toAffine.negY x₂ y₂
    · have hy' : w ^ 3 * y₁ = W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂) := by
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at hy ⊢
        rw [hy]; ring
      rw [slope_of_Y_eq hx hy, slope_of_Y_eq hx' hy', mul_zero]
    · have hy' : w ^ 3 * y₁ ≠ W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂) := by
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at hy ⊢
        intro h
        apply hy
        have : w ^ 3 * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h
        have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hw)
        linear_combination this
      rw [slope_of_Y_ne hx hy, slope_of_Y_ne hx' hy']
      simp only [negY, hs.a₁, hs.a₂, hs.a₃, hs.a₁', hs.a₂', hs.a₃', hs.a₄]
      have key : ∀ N D : F, (w ^ 4 * N) / (w ^ 3 * D) = w * (N / D) := by
        intro N D
        rw [mul_div_mul_comm]
        congr 1
        field_simp
      rw [← key]
      congr 1 <;> ring
  · have hx' : w ^ 2 * x₁ ≠ w ^ 2 * x₂ := fun h => hx (mul_left_cancel₀ (pow_ne_zero 2 hw) h)
    rw [slope_of_X_ne hx, slope_of_X_ne hx']
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp

/-- **Scaling maps are additive.** -/
theorem scalePt_add (hs : IsScale W W' w) (P Q : W.toAffine.Point) :
    scalePt hs (P + Q) = scalePt hs P + scalePt hs Q := by
  have hw := hs.ne
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · have hxy' : w ^ 2 * x₁ = w ^ 2 * x₂ ∧
          w ^ 3 * y₁ = W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂) := by
        refine ⟨by rw [hxy.1], ?_⟩
        have := hxy.2
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at this ⊢
        rw [this]; ring
      rw [Point.add_of_Y_eq hxy.1 hxy.2, scalePt_some, scalePt_some,
        Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(w ^ 2 * x₁ = w ^ 2 * x₂ ∧
          w ^ 3 * y₁ = W'.toAffine.negY (w ^ 2 * x₂) (w ^ 3 * y₂)) := by
        rintro ⟨h1, h2⟩
        apply hxy
        refine ⟨mul_left_cancel₀ (pow_ne_zero 2 hw) h1, ?_⟩
        simp only [negY, hs.a₁, hs.a₃, hs.a₁', hs.a₃'] at h2 ⊢
        have : w ^ 3 * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h2
        have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hw)
        linear_combination this
      rw [Point.add_some hxy, scalePt_some, scalePt_some, scalePt_some, Point.add_some hxy',
        Point.some.injEq]
      have hsl := hs.slope x₁ x₂ y₁ y₂
      constructor
      · simp only [addX, hs.a₁, hs.a₂, hs.a₁', hs.a₂']
        rw [hsl]
        ring
      · simp only [addY, negAddY, addX, negY, hs.a₁, hs.a₂, hs.a₃, hs.a₁', hs.a₂', hs.a₃']
        rw [hsl]
        ring

/-- The scaling map as an additive homomorphism. -/
def scaleHom (hs : IsScale W W' w) : W.toAffine.Point →+ W'.toAffine.Point :=
  AddMonoidHom.mk' (scalePt hs) (scalePt_add hs)

theorem IsScale.comp (hs : IsScale W W' w) (hs' : IsScale W' W'' w') :
    IsScale W W'' (w' * w) where
  a₁ := hs.a₁
  a₂ := hs.a₂
  a₃ := hs.a₃
  a₁' := hs'.a₁'
  a₂' := hs'.a₂'
  a₃' := hs'.a₃'
  a₄ := by rw [hs'.a₄, hs.a₄]; ring
  a₆ := by rw [hs'.a₆, hs.a₆]; ring
  ne := mul_ne_zero hs'.ne hs.ne

theorem scalePt_comp (hs : IsScale W W' w) (hs' : IsScale W' W'' w') (P : W.toAffine.Point) :
    scalePt hs' (scalePt hs P) = scalePt (hs.comp hs') P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [scalePt_some, Point.some.injEq]
    constructor <;> ring

theorem scalePt_one (hs : IsScale W W 1) (P : W.toAffine.Point) : scalePt hs P = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp [scalePt_some]

theorem scalePt_eq_of_eq (hs : IsScale W W' w) (hs' : IsScale W W' w') (he : w = w')
    (P : W.toAffine.Point) : scalePt hs P = scalePt hs' P := by
  subst he; rfl

end Scale

/-! ## §5 `X₀(32) = A` and `C₁` over `ℚ̄`: the isomorphism `ι` over `ℚ(i)` -/

open ZInQ.Contrib.TYZDecomp.CurveA

/-- `C₁` over `ℚ̄`. -/
abbrev curveC1bar : WeierstrassCurve Qbar := curveC1.baseChange Qbar

/-- `C₁(ℚ̄)`. -/
abbrev PtC1 : Type := curveC1bar.toAffine.Point

@[simp] theorem curveC1bar_a₁ : curveC1bar.a₁ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₂ : curveC1bar.a₂ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₃ : curveC1bar.a₃ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₄ : curveC1bar.a₄ = -1 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]
@[simp] theorem curveC1bar_a₆ : curveC1bar.a₆ = 0 := by
  simp [curveC1bar, curveC1, shortCurve, WeierstrassCurve.baseChange]

theorem iQ_pow_four : iQ ^ 4 = 1 := by
  have h := iQ_sq
  calc iQ ^ 4 = (iQ ^ 2) ^ 2 := by ring
    _ = 1 := by rw [h]; norm_num

/-- `(x, y) ↦ (w²x, w³y)` with `w = (1 + i)/2` maps `A : y² = x³ + 4x` to `C₁ : y² = x³ − x`
(`w⁴ = −1/4`). -/
theorem isScale_iota : IsScale curveAbar curveC1bar ((1 + iQ) / 2) where
  a₁ := curveAbar_a₁
  a₂ := curveAbar_a₂
  a₃ := curveAbar_a₃
  a₁' := curveC1bar_a₁
  a₂' := curveC1bar_a₂
  a₃' := curveC1bar_a₃
  a₄ := by
    rw [curveC1bar_a₄, curveAbar_a₄]
    linear_combination (-(5 : Qbar) / 4 - iQ - 1 / 4 * iQ ^ 2) * iQ_sq
  a₆ := by rw [curveC1bar_a₆, curveAbar_a₆, mul_zero]
  ne := by
    intro h
    have h1 : iQ = -1 := by linear_combination 2 * h
    have := iQ_sq
    rw [h1] at this
    norm_num at this

/-- `(x, y) ↦ (w²x, w³y)` with `w = 1 − i` maps `C₁` to `A` (`w⁴ = −4`). -/
theorem isScale_iotaInv : IsScale curveC1bar curveAbar (1 - iQ) where
  a₁ := curveC1bar_a₁
  a₂ := curveC1bar_a₂
  a₃ := curveC1bar_a₃
  a₁' := curveAbar_a₁
  a₂' := curveAbar_a₂
  a₃' := curveAbar_a₃
  a₄ := by
    rw [curveC1bar_a₄, curveAbar_a₄]
    linear_combination (5 - 4 * iQ + iQ ^ 2) * iQ_sq
  a₆ := by rw [curveC1bar_a₆, curveAbar_a₆, mul_zero]
  ne := by
    intro h
    have h1 : iQ = 1 := by linear_combination -h
    have := iQ_sq
    rw [h1] at this
    norm_num at this

/-- **`A ≅ C₁` over `ℚ(i)`**: `ι(x, y) = (ix/2, (i − 1)y/4)`, an additive bijection
`A(ℚ̄) → C₁(ℚ̄)` with coefficients in `ℚ(i)`. -/
def iota : PtA →+ PtC1 := scaleHom isScale_iota

/-- The inverse of `ι`: `(x, y) ↦ (−2ix, −(2 + 2i)y)`. -/
def iotaInv : PtC1 →+ PtA := scaleHom isScale_iotaInv

theorem iota_some {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) :
    iota (.some x y h) = .some (((1 + iQ) / 2) ^ 2 * x) (((1 + iQ) / 2) ^ 3 * y)
      (isScale_iota.nonsingular h) := rfl

theorem iotaInv_some {x y : Qbar} (h : curveC1bar.toAffine.Nonsingular x y) :
    iotaInv (.some x y h) = .some ((1 - iQ) ^ 2 * x) ((1 - iQ) ^ 3 * y)
      (isScale_iotaInv.nonsingular h) := rfl

theorem iotaInv_iota (P : PtA) : iotaInv (iota P) = P := by
  change scalePt isScale_iotaInv (scalePt isScale_iota P) = P
  rw [scalePt_comp]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [scalePt_some, WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · linear_combination x * (-(3 : Qbar) / 4 + 1 / 4 * iQ ^ 2) * iQ_sq
    · linear_combination y * (-(7 : Qbar) / 8 + 1 / 2 * iQ ^ 2 - 1 / 8 * iQ ^ 4) * iQ_sq

theorem iota_iotaInv (Q : PtC1) : iota (iotaInv Q) = Q := by
  change scalePt isScale_iota (scalePt isScale_iotaInv Q) = Q
  rw [scalePt_comp]
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · simp only [scalePt_some, WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · linear_combination x * (-(3 : Qbar) / 4 + 1 / 4 * iQ ^ 2) * iQ_sq
    · linear_combination y * (-(7 : Qbar) / 8 + 1 / 2 * iQ ^ 2 - 1 / 8 * iQ ^ 4) * iQ_sq

/-! ## §6 The `2`-isogenies `φ : A → C₁`, `ψ : C₁ → A` -/

/-- **`φ = ι ∘ (1 + [i]) : A → C₁`**, a `2`-isogeny with kernel `{O, (0, 0)}`; over `ℚ` it is
`(x, y) ↦ (y²/4x², y(x² − 4)/8x²)` (`phi_some`). -/
def phi : PtA →+ PtC1 := iota.comp (AddMonoidHom.id PtA + iHom)

/-- **`ψ = (1 − [i]) ∘ ι⁻¹ : C₁ → A`**, the dual `2`-isogeny; over `ℚ` it is
`(x, y) ↦ (y²/x², y(x² + 1)/x²)` (`psi_some`). -/
def psi : PtC1 →+ PtA := (AddMonoidHom.id PtA - iHom).comp iotaInv

theorem phi_apply (P : PtA) : phi P = iota (P + iPt P) := rfl

theorem psi_apply (Q : PtC1) : psi Q = iotaInv Q - iPt (iotaInv Q) := rfl

/-- **`ψ ∘ φ = [2]`.** -/
theorem psi_phi (P : PtA) : psi (phi P) = 2 • P := by
  rw [psi_apply, phi_apply, iotaInv_iota]
  have h1 : iPt (P + iPt P) = iPt P + iPt (iPt P) := iPt_add _ _
  rw [h1, iPt_iPt, two_nsmul]
  abel

/-- **`φ ∘ ψ = [2]`.** -/
theorem phi_psi (Q : PtC1) : phi (psi Q) = 2 • Q := by
  rw [phi_apply, psi_apply]
  have h1 : iPt (iotaInv Q - iPt (iotaInv Q)) = iPt (iotaInv Q) - iPt (iPt (iotaInv Q)) :=
    map_sub iHom _ _
  rw [h1, iPt_iPt]
  have h2 : iotaInv Q - iPt (iotaInv Q) + (iPt (iotaInv Q) - -iotaInv Q) = 2 • iotaInv Q := by
    rw [two_nsmul]; abel
  rw [h2, map_nsmul, iota_iotaInv]


theorem iQ_pow3 : iQ ^ 3 = -iQ := by linear_combination iQ * iQ_sq
theorem iQ_pow4 : iQ ^ 4 = 1 := by linear_combination (iQ ^ 2 - 1) * iQ_sq
theorem iQ_pow5 : iQ ^ 5 = iQ := by linear_combination (iQ ^ 3 - iQ) * iQ_sq
theorem iQ_pow6 : iQ ^ 6 = -1 := by linear_combination (iQ ^ 4 - iQ ^ 2 + 1) * iQ_sq
theorem iQ_pow7 : iQ ^ 7 = -iQ := by linear_combination (iQ ^ 5 - iQ ^ 3 + iQ) * iQ_sq
theorem iQ_pow8 : iQ ^ 8 = 1 := by linear_combination (iQ ^ 6 - iQ ^ 4 + iQ ^ 2 - 1) * iQ_sq

open WeierstrassCurve.Affine in
/-- **`φ` over `ℚ`**: `φ(x, y) = (y²/4x², y(x² − 4)/8x²)` for `x ≠ 0`. -/
theorem phi_some {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ h' : curveC1bar.toAffine.Nonsingular (y ^ 2 / (4 * x ^ 2)) (y * (x ^ 2 - 4) / (8 * x ^ 2)),
      phi (.some x y h) = .some _ _ h' := by
  have hx' : x ≠ -x := by
    intro h0; apply hx; linear_combination h0 / 2
  have he := (nonsingular_iff' _ _).mp h |>.1
  rw [equation_iff'] at he
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆] at he
  rw [phi_apply, iPt_some, Point.add_of_X_ne hx', iota_some]
  have hsl : curveAbar.toAffine.slope x (-x) y (iQ * y) = (y - iQ * y) / (x - -x) :=
    slope_of_X_ne hx'
  have e1 : ((1 + iQ) / 2) ^ 2 * curveAbar.toAffine.addX x (-x)
      (curveAbar.toAffine.slope x (-x) y (iQ * y)) = y ^ 2 / (4 * x ^ 2) := by
    rw [hsl]
    simp only [addX, curveAbar_a₁, curveAbar_a₂]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6]
    ring_nf
  have e2 : ((1 + iQ) / 2) ^ 3 * curveAbar.toAffine.addY x (-x) y
      (curveAbar.toAffine.slope x (-x) y (iQ * y)) = y * (x ^ 2 - 4) / (8 * x ^ 2) := by
    rw [hsl]
    simp only [addY, negAddY, negY, addX, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6, iQ_pow7, iQ_pow8]
    ring_nf
    linear_combination (-64 * y) * he
  refine ⟨by
    rw [← e1, ← e2]
    exact isScale_iota.nonsingular (nonsingular_add h (nonsingular_iPt h) fun hxy => hx' hxy.1),
    ?_⟩
  simp only [Point.some.injEq]
  exact ⟨e1, e2⟩


open WeierstrassCurve.Affine in
/-- **`ψ` over `ℚ`**: `ψ(x, y) = (y²/x², y(x² + 1)/x²)` for `x ≠ 0`. -/
theorem psi_some {x y : Qbar} (h : curveC1bar.toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ h' : curveAbar.toAffine.Nonsingular (y ^ 2 / x ^ 2) (y * (x ^ 2 + 1) / x ^ 2),
      psi (.some x y h) = .some _ _ h' := by
  have he := (nonsingular_iff' _ _).mp h |>.1
  rw [equation_iff'] at he
  simp only [curveC1bar_a₁, curveC1bar_a₂, curveC1bar_a₃, curveC1bar_a₄, curveC1bar_a₆] at he
  have hv : (1 - iQ) ^ 2 ≠ 0 := pow_ne_zero 2 isScale_iotaInv.ne
  have hv2 : (1 - iQ) ^ 2 = -2 * iQ := by linear_combination iQ_sq
  have hv3 : (1 - iQ) ^ 3 = -2 - 2 * iQ := by linear_combination (3 - iQ) * iQ_sq
  have hi0 := iQ_ne_zero
  set X := (1 - iQ) ^ 2 * x with hX
  set Y := (1 - iQ) ^ 3 * y with hY
  rw [hv2] at hX
  rw [hv3] at hY
  have hX0 : X ≠ 0 := mul_ne_zero hv hx
  have hx' : X ≠ -X := by
    intro h0; apply hX0; linear_combination h0 / 2
  have hR : curveAbar.toAffine.Nonsingular X Y := isScale_iotaInv.nonsingular h
  rw [psi_apply, iotaInv_some, sub_eq_add_neg, iPt_some, Point.neg_some]
  have hnegY : curveAbar.toAffine.negY (-X) (iQ * Y) = -(iQ * Y) := by
    simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring
  have hsl : curveAbar.toAffine.slope X (-X) Y (curveAbar.toAffine.negY (-X) (iQ * Y)) =
      (Y + iQ * Y) / (X - -X) := by
    rw [slope_of_X_ne hx', hnegY, sub_neg_eq_add]
  rw [Point.add_of_X_ne hx']
  have e1 : curveAbar.toAffine.addX X (-X)
      (curveAbar.toAffine.slope X (-X) Y (curveAbar.toAffine.negY (-X) (iQ * Y))) =
      y ^ 2 / x ^ 2 := by
    rw [hsl]
    simp only [addX, curveAbar_a₁, curveAbar_a₂, hX, hY]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6, iQ_pow7, iQ_pow8]
    ring_nf
  have e2 : curveAbar.toAffine.addY X (-X) Y
      (curveAbar.toAffine.slope X (-X) Y (curveAbar.toAffine.negY (-X) (iQ * Y))) =
      y * (x ^ 2 + 1) / x ^ 2 := by
    rw [hsl]
    simp only [addY, negAddY, negY, addX, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, hX, hY]
    field_simp
    ring_nf
    simp only [iQ_sq, iQ_pow3, iQ_pow4, iQ_pow5, iQ_pow6, iQ_pow7, iQ_pow8]
    ring_nf
    linear_combination (-8 * iQ * y) * he
  refine ⟨by
    rw [← e1, ← e2]
    exact nonsingular_add hR ((nonsingular_neg ..).mpr (nonsingular_iPt hR)) fun hxy => hx' hxy.1, ?_⟩
  simp only [Point.some.injEq]
  exact ⟨e1, e2⟩


/-! ### `ι`, `φ`, `ψ` are `ℤ[i]`-linear -/

theorem nonsingular_iPtC1 {x y : Qbar} (h : curveC1bar.toAffine.Nonsingular x y) :
    curveC1bar.toAffine.Nonsingular (-x) (iQ * y) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff'] at h ⊢
  simp only [curveC1bar_a₁, curveC1bar_a₂, curveC1bar_a₃, curveC1bar_a₄, curveC1bar_a₆] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by linear_combination y ^ 2 * iQ_sq - he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    linear_combination h'
  · right
    intro h'
    apply h
    have : iQ * (2 * y) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 iQ_ne_zero
    · linear_combination h0

/-- `[i]` on `C₁(ℚ̄)`: `(x, y) ↦ (−x, iy)`. -/
def iPtC1 : PtC1 → PtC1
  | .zero => .zero
  | .some x y h => .some (-x) (iQ * y) (nonsingular_iPtC1 h)

theorem iota_iPt (P : PtA) : iota (iPt P) = iPtC1 (iota P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [iPt_some, iota_some, iPtC1, WeierstrassCurve.Affine.Point.some.injEq]
    constructor <;> ring

/-- **`φ` is `ℤ[i]`-linear**: `φ ∘ [i] = [i] ∘ φ`. -/
theorem phi_iPt (P : PtA) : phi (iPt P) = iPtC1 (phi P) := by
  rw [phi_apply, phi_apply, ← iota_iPt, iPt_add]

/-! ## §7 `A[(1+i)³]` explicitly; half of TYZ Lemma 3.16 -/

theorem iota_eq_zero_iff (P : PtA) : iota P = 0 ↔ P = 0 := by
  constructor
  · intro h
    have := iotaInv_iota P
    rw [h, map_zero] at this
    exact this.symm
  · rintro rfl; exact map_zero _

open WeierstrassCurve.Affine in
theorem two_nsmul_some_C1_eq_zero_iff {x y : Qbar} (h : curveC1bar.toAffine.Nonsingular x y) :
    2 • (Point.some x y h : PtC1) = 0 ↔ y = 0 := by
  rw [two_nsmul]
  by_cases hy : y = curveC1bar.toAffine.negY x y
  · rw [Point.add_self_of_Y_eq hy]
    simp only [negY, curveC1bar_a₁, curveC1bar_a₃] at hy
    simp only [true_iff]
    linear_combination hy / 2
  · rw [Point.add_self_of_Y_ne hy]
    simp only [reduceCtorEq, false_iff]
    intro h0
    apply hy
    simp only [negY, curveC1bar_a₁, curveC1bar_a₃, h0]
    ring

/-- `A[(1+i)³]` listed: `O, (0,0), (2,±4), (−2,±4i), (±2i,0)`. -/
def IsTorsI3 : PtA → Prop
  | .zero => True
  | .some x y _ => (x, y) ∈ ({(0, 0), (2, 4), (2, -4), (-2, 4 * iQ), (-2, -4 * iQ), (2 * iQ, 0),
      (-2 * iQ, 0)} : Set (Qbar × Qbar))

open WeierstrassCurve.Affine in
/-- **`A[(1+i)³]` explicitly**: `2(P + [i]P) = 0` iff `P` is one of the eight points
`O, (0,0), (2,±4), (−2,±4i), (±2i,0)`. -/
theorem two_nsmul_add_iPt_eq_zero_iff (P : PtA) : 2 • (P + iPt P) = 0 ↔ IsTorsI3 P := by
  have key : 2 • (P + iPt P) = 0 ↔ 2 • phi P = 0 := by
    rw [phi_apply, ← map_nsmul, iota_eq_zero_iff]
  rw [key]
  rcases P with _ | ⟨x, y, h⟩
  · simp only [IsTorsI3, map_zero, smul_zero, iff_true]
    rfl
  have he := (nonsingular_iff' _ _).mp h |>.1
  rw [equation_iff'] at he
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆] at he
  simp only [IsTorsI3, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  by_cases hx : x = 0
  · subst hx
    have hy : y = 0 := by
      have : y ^ 2 = 0 := by linear_combination he
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    subst hy
    simp only [true_and, true_or, iff_true]
    have : (Point.some 0 0 h : PtA) + iPt (Point.some 0 0 h) = 0 := by
      rw [iPt_some]
      apply Point.add_of_Y_eq
      · ring
      · simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring
    rw [phi_apply, this, map_zero, nsmul_zero]
  obtain ⟨h', hphi⟩ := phi_some h hx
  rw [hphi, two_nsmul_some_C1_eq_zero_iff]
  have hx2 : (8 : Qbar) * x ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)
  rw [div_eq_zero_iff, or_iff_left hx2]
  have hi := iQ_sq
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with hy | hx4
    · subst hy
      have : (x - 2 * iQ) * (x + 2 * iQ) = 0 := by
        have h1 : x * (x ^ 2 + 4) = 0 := by linear_combination -he
        have h2 := (mul_eq_zero.mp h1).resolve_left hx
        linear_combination h2 - 4 * hi
      rcases mul_eq_zero.mp this with h3 | h3
      · right; right; right; right; right; left
        exact ⟨by linear_combination h3, rfl⟩
      · right; right; right; right; right; right
        exact ⟨by linear_combination h3, rfl⟩
    · have : (x - 2) * (x + 2) = 0 := by linear_combination hx4
      rcases mul_eq_zero.mp this with h3 | h3
      · have hx' : x = 2 := by linear_combination h3
        subst hx'
        have : (y - 4) * (y + 4) = 0 := by linear_combination he
        rcases mul_eq_zero.mp this with h4 | h4
        · right; left; exact ⟨rfl, by linear_combination h4⟩
        · right; right; left; exact ⟨rfl, by linear_combination h4⟩
      · have hx' : x = -2 := by linear_combination h3
        subst hx'
        have : (y - 4 * iQ) * (y + 4 * iQ) = 0 := by linear_combination he - 16 * hi
        rcases mul_eq_zero.mp this with h4 | h4
        · right; right; right; left; exact ⟨rfl, by linear_combination h4⟩
        · right; right; right; right; left; exact ⟨rfl, by linear_combination h4⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      subst h1 <;> subst h2
    · exact absurd rfl hx
    all_goals ring

/-- **Half of TYZ Lemma 3.16, proved**: `A[(1+i)³] ⊆ A(ℚ(i))`. -/
theorem lemma316_mpr (P : PtA) (hP : 2 • (P + iPt P) = 0) : IsDefinedOver Qi P := by
  rw [two_nsmul_add_iPt_eq_zero_iff] at hP
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  have hi : iQ ∈ Qi := IntermediateField.mem_adjoin_simple_self ℚ iQ
  have h2 : (2 : Qbar) ∈ Qi := ofNat_mem Qi 2
  have h4 : (4 : Qbar) ∈ Qi := ofNat_mem Qi 4
  have h0 : (0 : Qbar) ∈ Qi := IntermediateField.zero_mem _
  simp only [IsTorsI3, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hP
  rcases hP with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩) <;> refine ⟨?_, ?_⟩ <;>
    first
    | assumption
    | exact neg_mem h2
    | exact neg_mem h4
    | exact mul_mem h4 hi
    | exact neg_mem (mul_mem h4 hi)
    | exact mul_mem h2 hi
    | exact neg_mem (mul_mem h2 hi)
    | (rw [neg_mul]; exact neg_mem (mul_mem h4 hi))
    | (rw [neg_mul]; exact neg_mem (mul_mem h2 hi))

/-- **TYZ Lemma 3.16 reduces to its rank-zero half**: given the proved `A[(1+i)³] ⊆ A(ℚ(i))`, the
leaf `TYZLemma316` is equivalent to `A(ℚ(i)) ⊆ A[(1+i)³]`. -/
theorem tyzLemma316_iff :
    TYZLemma316 ↔ ∀ P : PtA, IsDefinedOver Qi P → 2 • (P + iPt P) = 0 :=
  ⟨fun h P hP => (h P).mp hP, fun h P => ⟨h P, lemma316_mpr P⟩⟩


/-! ## §8 `φ` and `ψ` are defined over `ℚ` (Galois-equivariant) -/

open WeierstrassCurve.Affine in
theorem phi_zero_zero (h0 : curveAbar.toAffine.Nonsingular 0 0) : phi (.some 0 0 h0) = 0 := by
  have : (Point.some 0 0 h0 : PtA) + iPt (Point.some 0 0 h0) = 0 := by
    rw [iPt_some]
    apply Point.add_of_Y_eq
    · ring
    · simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring
  rw [phi_apply, this, map_zero]

open WeierstrassCurve.Affine in
theorem psi_zero_zero (h0 : curveC1bar.toAffine.Nonsingular 0 0) : psi (.some 0 0 h0) = 0 := by
  rw [psi_apply, iotaInv_some]
  generalize_proofs H
  have e : ((1 - iQ) ^ 2 * 0 : Qbar) = 0 := by ring
  have e' : ((1 - iQ) ^ 3 * 0 : Qbar) = 0 := by ring
  revert H
  rw [e, e']
  intro H
  rw [iPt_some, sub_eq_zero]
  simp only [neg_zero, mul_zero]

open WeierstrassCurve.Affine in
/-- **`φ` commutes with `Gal(ℚ̄/ℚ)`** (it is a `ℚ`-rational isogeny). -/
theorem phi_map (σ : Qbar →ₐ[ℚ] Qbar) (P : PtA) :
    phi (Point.map (W' := curveA) σ P) = Point.map (W' := curveC1) σ (phi P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : PtA) = 0 from rfl, map_zero, map_zero, map_zero]
  by_cases hx : x = 0
  · subst hx
    have he := (nonsingular_iff' _ _).mp h |>.1
    rw [equation_iff'] at he
    simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆] at he
    have hy : y = 0 := by
      have : y ^ 2 = 0 := by linear_combination he
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    subst hy
    rw [phi_zero_zero h, map_zero, Point.map_some]
    have e : ∀ pf : curveAbar.toAffine.Nonsingular (σ 0) (σ 0),
        (Point.some (σ 0) (σ 0) pf : PtA) = Point.some 0 0 h := fun pf => by
      simp only [Point.some.injEq, map_zero, and_self]
    rw [e]
    exact phi_zero_zero h
  have hσx : σ x ≠ 0 := by
    intro h0; apply hx; exact (map_eq_zero_iff σ σ.toRingHom.injective).mp h0
  obtain ⟨h', hphi⟩ := phi_some h hx
  rw [hphi, Point.map_some, Point.map_some]
  obtain ⟨h'', hphi'⟩ :=
    phi_some ((WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA) σ.injective _ _).mpr h) hσx
  rw [hphi', Point.some.injEq]
  constructor <;> simp [map_div₀, map_mul, map_pow, map_sub, map_ofNat]

open WeierstrassCurve.Affine in
/-- **`ψ` commutes with `Gal(ℚ̄/ℚ)`.** -/
theorem psi_map (σ : Qbar →ₐ[ℚ] Qbar) (Q : PtC1) :
    psi (Point.map (W' := curveC1) σ Q) = Point.map (W' := curveA) σ (psi Q) := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : PtC1) = 0 from rfl, map_zero, map_zero, map_zero]
  by_cases hx : x = 0
  · subst hx
    have he := (nonsingular_iff' _ _).mp h |>.1
    rw [equation_iff'] at he
    simp only [curveC1bar_a₁, curveC1bar_a₂, curveC1bar_a₃, curveC1bar_a₄, curveC1bar_a₆] at he
    have hy : y = 0 := by
      have : y ^ 2 = 0 := by linear_combination he
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    subst hy
    rw [psi_zero_zero h, map_zero, Point.map_some]
    have e : ∀ pf : curveC1bar.toAffine.Nonsingular (σ 0) (σ 0),
        (Point.some (σ 0) (σ 0) pf : PtC1) = Point.some 0 0 h := fun pf => by
      simp only [Point.some.injEq, map_zero, and_self]
    rw [e]
    exact psi_zero_zero h
  have hσx : σ x ≠ 0 := by
    intro h0; apply hx; exact (map_eq_zero_iff σ σ.toRingHom.injective).mp h0
  obtain ⟨h', hpsi⟩ := psi_some h hx
  rw [hpsi, Point.map_some, Point.map_some]
  obtain ⟨h'', hpsi'⟩ :=
    psi_some ((WeierstrassCurve.Affine.baseChange_nonsingular (W := curveC1) σ.injective _ _).mpr h) hσx
  rw [hpsi', Point.some.injEq]
  constructor <;> simp [map_div₀, map_mul, map_pow, map_add, map_one]


/-! ## §9 Invariants of the class `32a`; `X₀(32) ≇ C₁` over `ℚ`, `≅` over `ℚ(i)` -/

section Invariants

open WeierstrassCurve

theorem curveX0_c₄ : curveX0.c₄ = -192 := by
  simp [curveX0, curveA, shortCurve, c₄, b₂, b₄]; norm_num
theorem curveX0_Δ : curveX0.Δ = -4096 := by
  simp [curveX0, curveA, shortCurve, Δ, b₂, b₄, b₆, b₈]; norm_num
theorem curveC1_c₄ : curveC1.c₄ = 48 := by
  simp [curveC1, shortCurve, c₄, b₂, b₄]; norm_num
theorem curveC1_Δ : curveC1.Δ = 64 := by
  simp [curveC1, shortCurve, Δ, b₂, b₄, b₆, b₈]; norm_num
theorem curve32a3_c₄ : curve32a3.c₄ = 528 := by
  simp [curve32a3, c₄, b₂, b₄]; norm_num
theorem curve32a3_Δ : curve32a3.Δ = 512 := by
  simp [curve32a3, Δ, b₂, b₄, b₆, b₈]; norm_num
theorem curve32a4_c₄ : curve32a4.c₄ = 528 := by
  simp [curve32a4, c₄, b₂, b₄]; norm_num
theorem curve32a4_Δ : curve32a4.Δ = 512 := by
  simp [curve32a4, Δ, b₂, b₄, b₆, b₈]; norm_num

instance curveX0_isElliptic : curveX0.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [curveX0_Δ]; norm_num)⟩
instance curveC1_isElliptic : curveC1.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [curveC1_Δ]; norm_num)⟩
instance curve32a3_isElliptic : curve32a3.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [curve32a3_Δ]; norm_num)⟩
instance curve32a4_isElliptic : curve32a4.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [curve32a4_Δ]; norm_num)⟩

/-- `j(X₀(32)) = 1728` (CM by `ℤ[i]`). -/
theorem curveX0_j : curveX0.j = 1728 := by
  rw [j_eq, curveX0_Δ, curveX0_c₄]; norm_num
/-- `j(C₁) = 1728`. -/
theorem curveC1_j : curveC1.j = 1728 := by
  rw [j_eq, curveC1_Δ, curveC1_c₄]; norm_num
/-- `j(32a3) = j(32a4) = 287496 = 66³` (CM by `ℤ[2i]`). -/
theorem curve32a3_j : curve32a3.j = 287496 := by
  rw [j_eq, curve32a3_Δ, curve32a3_c₄]; norm_num
theorem curve32a4_j : curve32a4.j = 287496 := by
  rw [j_eq, curve32a4_Δ, curve32a4_c₄]; norm_num

/-- **`X₀(32) ≇ C₁` over `ℚ`**: no change of variables over `ℚ` maps `y² = x³ + 4x` to
`y² = x³ − x` (it would need `u⁴ = −4`). -/
theorem not_exists_variableChange_X0_C1 : ¬ ∃ C : VariableChange ℚ, C • curveX0 = curveC1 := by
  rintro ⟨C, hC⟩
  have h := congrArg WeierstrassCurve.c₄ hC
  rw [variableChange_c₄, curveX0_c₄, curveC1_c₄] at h
  have h0 : (0 : ℚ) ≤ ((C.u⁻¹ : ℚˣ) : ℚ) ^ 4 := by positivity
  nlinarith

/-- **`X₀(32) ≅ C₁` over `ℚ(i)`**: the change of variables `x = u²x'`, `y = u³y'` with `u = 1 − i`
maps `y² = x³ + 4x` to `y² = x³ − x`. -/
def isoVC : VariableChange Qbar :=
  ⟨Units.mk0 (1 - iQ) isScale_iotaInv.ne, 0, 0, 0⟩

theorem isoVC_smul : isoVC • curveAbar = curveC1bar := by
  have hu : ((isoVC.u⁻¹ : Qbarˣ) : Qbar) = (1 + iQ) / 2 := by
    simp only [isoVC, Units.val_inv_eq_inv_val, Units.val_mk0]
    have h1 : (1 - iQ) ≠ 0 := isScale_iotaInv.ne
    field_simp
    linear_combination iQ_sq
  ext
  · rw [variableChange_a₁, curveC1bar_a₁, curveAbar_a₁]; simp [isoVC]
  · rw [variableChange_a₂, curveC1bar_a₂, curveAbar_a₂, curveAbar_a₁]; simp [isoVC]
  · rw [variableChange_a₃, curveC1bar_a₃, curveAbar_a₃, curveAbar_a₁]; simp [isoVC]
  · rw [variableChange_a₄, curveC1bar_a₄, curveAbar_a₄, curveAbar_a₃, curveAbar_a₂,
      curveAbar_a₁, hu]
    simp only [isoVC]
    linear_combination ((5 : Qbar) / 4 + iQ + 1 / 4 * iQ ^ 2) * iQ_sq
  · rw [variableChange_a₆, curveC1bar_a₆, curveAbar_a₆]; simp [isoVC]

end Invariants


/-! ## §10 From `ℚ̄` to `ℂ`: the cusp images are `A[(1+i)³]` -/

/-- A fixed `ℚ`-embedding `ℚ̄ → ℂ`. -/
def embC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- `A(ℚ̄) → A(ℂ)` induced by `embC`. -/
def toC : PtA →+ PtAC := WeierstrassCurve.Affine.Point.map (W' := curveA) embC

theorem toC_injective : Function.Injective toC :=
  WeierstrassCurve.Affine.Point.map_injective embC

theorem embC_iQ : embC iQ = I ∨ embC iQ = -I := by
  have h : embC iQ ^ 2 = -1 := by rw [← map_pow, iQ_sq, map_neg, map_one]
  have : (embC iQ - I) * (embC iQ + I) = 0 := by
    linear_combination h - Complex.I_sq
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

/-- The eight-point set over `ℚ̄` maps onto the eight-point set over `ℂ`. -/
theorem image_torsI3 :
    (fun p : Qbar × Qbar => (embC p.1, embC p.2)) ''
      ({(0, 0), (2, 4), (2, -4), (-2, 4 * iQ), (-2, -4 * iQ), (2 * iQ, 0), (-2 * iQ, 0)} :
        Set (Qbar × Qbar)) =
      ({(0, 0), (2, 4), (2, -4), (-2, 4 * I), (-2, -4 * I), (2 * I, 0), (-2 * I, 0)} :
        Set (ℂ × ℂ)) := by
  simp only [Set.image_insert_eq, Set.image_singleton, map_zero, map_ofNat, map_neg, map_mul]
  rcases embC_iQ with h | h <;> rw [h]
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor <;>
  · rintro (h | h | h | h | h | h | h) <;> subst h <;> simp

/-- **The cusp images are the eight points of `A[(1+i)³]`**, transported to `ℂ`. -/
theorem isCuspImage_toC (P : PtA) : IsCuspImage (toC P) ↔ IsTorsI3 P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact Iff.rfl
  change ((embC x, embC y) ∈ _) ↔ ((x, y) ∈ _)
  rw [← image_torsI3]
  have hinj : Function.Injective (fun p : Qbar × Qbar => (embC p.1, embC p.2)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hab
    simp only [Prod.mk.injEq] at hab ⊢
    exact ⟨embC.injective hab.1, embC.injective hab.2⟩
  exact hinj.mem_set_image (a := (x, y))

/-! ## §11 Basic analytic facts about the eta-quotient model (proved) -/

section Analytic

open ModularForm UpperHalfPlane

theorem mul_mem_upperHalfPlaneSet {d : ℕ} (hd : 0 < d) (τ : UpperHalfPlane) :
    (d : ℂ) * (τ : ℂ) ∈ upperHalfPlaneSet := by
  show 0 < ((d : ℂ) * (τ : ℂ)).im
  rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast hd) τ.im_pos

theorem etaD_ne_zero {d : ℕ} (hd : 0 < d) (τ : UpperHalfPlane) : etaD d τ ≠ 0 :=
  eta_ne_zero (mul_mem_upperHalfPlaneSet hd τ)

theorem differentiableAt_etaD {d : ℕ} (hd : 0 < d) (τ : UpperHalfPlane) :
    DifferentiableAt ℂ (etaD d) τ := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (d : ℂ) * z) τ := by fun_prop
  exact (differentiableAt_eta_of_mem_upperHalfPlaneSet (mul_mem_upperHalfPlaneSet hd τ)).comp
    (τ : ℂ) h1

/-- `x` is holomorphic on `ℍ`. -/
theorem differentiableAt_xC (τ : UpperHalfPlane) : DifferentiableAt ℂ xC τ := by
  unfold xC
  apply DifferentiableAt.add_const
  refine DifferentiableAt.div ?_ ?_ ?_
  · exact ((differentiableAt_etaD (by norm_num) τ).pow 2).mul (differentiableAt_etaD (by norm_num) τ)
  · exact (differentiableAt_etaD (by norm_num) τ).mul
      ((differentiableAt_etaD (by norm_num) τ).pow 2)
  · exact mul_ne_zero (etaD_ne_zero (by norm_num) τ) (pow_ne_zero 2 (etaD_ne_zero (by norm_num) τ))

/-- `y` is holomorphic on `ℍ`. -/
theorem differentiableAt_yC (τ : UpperHalfPlane) : DifferentiableAt ℂ yC τ := by
  unfold yC
  refine DifferentiableAt.neg ?_
  refine DifferentiableAt.div ?_ ?_ ?_
  · exact ((differentiableAt_etaD (by norm_num) τ).pow 4).mul
      ((differentiableAt_etaD (by norm_num) τ).pow 2)
  · exact ((differentiableAt_etaD (by norm_num) τ).pow 2).mul
      ((differentiableAt_etaD (by norm_num) τ).pow 4)
  · exact mul_ne_zero (pow_ne_zero 2 (etaD_ne_zero (by norm_num) τ))
      (pow_ne_zero 4 (etaD_ne_zero (by norm_num) τ))

/-- `f` is holomorphic on `ℍ`. -/
theorem differentiableAt_fC (τ : UpperHalfPlane) : DifferentiableAt ℂ fC τ := by
  unfold fC
  exact ((differentiableAt_etaD (by norm_num) τ).pow 2).mul
    ((differentiableAt_etaD (by norm_num) τ).pow 2)

/-- `f` has no zeros on `ℍ` (an eta product). -/
theorem fC_ne_zero (τ : UpperHalfPlane) : fC τ ≠ 0 := by
  unfold fC
  exact mul_ne_zero (pow_ne_zero 2 (etaD_ne_zero (by norm_num) τ))
    (pow_ne_zero 2 (etaD_ne_zero (by norm_num) τ))

/-- `y` has no zeros on `ℍ`: the points `(x, 0)` (`2`-torsion) are cusp images, so they are not
hit by `ℍ` (consistent with `EtaModelBijective`). -/
theorem yC_ne_zero (τ : UpperHalfPlane) : yC τ ≠ 0 := by
  unfold yC
  refine neg_ne_zero.mpr (div_ne_zero ?_ ?_)
  · exact mul_ne_zero (pow_ne_zero 4 (etaD_ne_zero (by norm_num) τ))
      (pow_ne_zero 2 (etaD_ne_zero (by norm_num) τ))
  · exact mul_ne_zero (pow_ne_zero 2 (etaD_ne_zero (by norm_num) τ))
      (pow_ne_zero 4 (etaD_ne_zero (by norm_num) τ))

theorem curveAC_Δ : curveAC.Δ = -4096 := by
  have : curveA.Δ = -4096 := curveX0_Δ
  rw [curveAC, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, this]
  simp

/-- Under `EtaModelEquation`, `phiC τ` is the affine point `(x(τ), y(τ))`. -/
theorem phiC_eq_some (hEq : EtaModelEquation) (τ : UpperHalfPlane) :
    ∃ h, phiC τ = .some (xC τ) (yC τ) h := by
  have hN : curveAC.toAffine.Nonsingular (xC τ) (yC τ) := by
    rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (by rw [curveAC_Δ]; norm_num), WeierstrassCurve.Affine.equation_iff']
    have h4 : curveAC.a₄ = 4 := by simp [curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
    have h0 : curveAC.a₁ = 0 ∧ curveAC.a₂ = 0 ∧ curveAC.a₃ = 0 ∧ curveAC.a₆ = 0 := by
      simp [curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
    rw [h4, h0.1, h0.2.1, h0.2.2.1, h0.2.2.2]
    linear_combination hEq τ
  exact ⟨hN, by simp [phiC, hN]⟩

/-- Under `EtaModelEquation`, no point of `ℍ` maps to a `2`-torsion point or to `O`. -/
theorem phiC_ne_zero (hEq : EtaModelEquation) (τ : UpperHalfPlane) : phiC τ ≠ 0 := by
  obtain ⟨h, e⟩ := phiC_eq_some hEq τ
  rw [e]
  exact WeierstrassCurve.Affine.Point.some_ne_zero h

end Analytic

/-! ## §12 Invariance under `T = [[1,1],[0,1]] ∈ Γ₀(32)` (proved; a piece of `X0-INV`) -/

section Translation

open ModularForm

/-- `η(z + m) = e^{2πim/24} η(z)` for `m ∈ ℕ`. -/
theorem eta_add_nat (z : ℂ) (m : ℕ) :
    ModularForm.eta (z + m) = cexp (2 * Real.pi * I * m / 24) * ModularForm.eta z := by
  unfold ModularForm.eta
  have hq : ∀ n : ℕ, eta_q n (z + m) = eta_q n z := by
    intro n
    rw [eta_q_eq_cexp, eta_q_eq_cexp]
    have : 2 * Real.pi * I * (n + 1) * (z + m) =
        2 * Real.pi * I * (n + 1) * z + ((n + 1) * m : ℕ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  simp only [hq]
  rw [← mul_assoc]
  congr 1
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `η(d(z + 1)) = c^d η(dz)` with `c = e^{2πi/24}`. -/
theorem etaD_add_one (d : ℕ) (z : ℂ) :
    etaD d (z + 1) = cexp (2 * Real.pi * I / 24) ^ d * etaD d z := by
  unfold etaD
  rw [show (d : ℂ) * (z + 1) = d * z + (d : ℕ) by ring, eta_add_nat, ← Complex.exp_nat_mul]
  congr 2
  ring

theorem cexp_pow_24 : cexp (2 * Real.pi * I / 24) ^ 24 = 1 := by
  rw [← Complex.exp_nat_mul]
  have : ((24 : ℕ) : ℂ) * (2 * Real.pi * I / 24) = ((1 : ℕ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [this, Complex.exp_nat_mul_two_pi_mul_I]

/-- **`x(z + 1) = x(z)`.** -/
theorem xC_add_one (z : ℂ) : xC (z + 1) = xC z := by
  unfold xC
  simp only [etaD_add_one]
  set c := cexp (2 * Real.pi * I / 24)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have h24 := cexp_pow_24
  congr 1
  rcases eq_or_ne (etaD 4 z * etaD 32 z ^ 2) 0 with h0 | h0
  · have : (c ^ 4 * etaD 4 z * (c ^ 32 * etaD 32 z) ^ 2) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · rw [h]; ring
      · rw [pow_eq_zero_iff two_ne_zero |>.mp h]; ring
    rw [this, h0, div_zero, div_zero]
  · have h0' : c ^ 4 * etaD 4 z * (c ^ 32 * etaD 32 z) ^ 2 ≠ 0 := by
      have : c ^ 4 * etaD 4 z * (c ^ 32 * etaD 32 z) ^ 2 =
        c ^ 68 * (etaD 4 z * etaD 32 z ^ 2) := by ring
      rw [this]; exact mul_ne_zero (pow_ne_zero _ hc) h0
    rw [div_eq_div_iff h0' h0]
    have h68 : c ^ 68 = c ^ 20 := by
      rw [show c ^ 68 = c ^ 20 * (c ^ 24) ^ 2 by ring, h24]; ring
    linear_combination (-(etaD 2 z ^ 2 * etaD 16 z * etaD 4 z * etaD 32 z ^ 2)) * h68

/-- **`f(z + 1) = f(z)`.** -/
theorem fC_add_one (z : ℂ) : fC (z + 1) = fC z := by
  unfold fC
  simp only [etaD_add_one]
  linear_combination (etaD 4 z ^ 2 * etaD 8 z ^ 2) * cexp_pow_24

/-- **`y(z + 1) = y(z)`.** -/
theorem yC_add_one (z : ℂ) : yC (z + 1) = yC z := by
  unfold yC
  simp only [etaD_add_one]
  set c := cexp (2 * Real.pi * I / 24)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have h24 := cexp_pow_24
  congr 1
  rcases eq_or_ne (etaD 4 z ^ 2 * etaD 32 z ^ 4) 0 with h0 | h0
  · have : (c ^ 4 * etaD 4 z) ^ 2 * (c ^ 32 * etaD 32 z) ^ 4 = 0 := by
      rw [show (c ^ 4 * etaD 4 z) ^ 2 * (c ^ 32 * etaD 32 z) ^ 4 =
        c ^ 136 * (etaD 4 z ^ 2 * etaD 32 z ^ 4) by ring, h0, mul_zero]
    rw [this, h0, div_zero, div_zero]
  · have h0' : (c ^ 4 * etaD 4 z) ^ 2 * (c ^ 32 * etaD 32 z) ^ 4 ≠ 0 := by
      rw [show (c ^ 4 * etaD 4 z) ^ 2 * (c ^ 32 * etaD 32 z) ^ 4 =
        c ^ 136 * (etaD 4 z ^ 2 * etaD 32 z ^ 4) by ring]
      exact mul_ne_zero (pow_ne_zero _ hc) h0
    rw [div_eq_div_iff h0' h0]
    have h136 : c ^ 136 = c ^ 64 := by
      rw [show c ^ 136 = c ^ 64 * (c ^ 24) ^ 3 by ring, h24]; ring
    linear_combination (-(etaD 8 z ^ 4 * etaD 16 z ^ 2 * etaD 4 z ^ 2 * etaD 32 z ^ 4)) * h136

/-- **`x, y, f` are invariant under `T ∈ Γ₀(32)`** (`T • τ = τ + 1`). -/
theorem xC_yC_fC_T_smul (τ : UpperHalfPlane) :
    xC ↑(ModularGroup.T • τ) = xC τ ∧ yC ↑(ModularGroup.T • τ) = yC τ ∧
      fC ↑(ModularGroup.T • τ) = fC τ := by
  have h : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
    push_cast; ring
  rw [h]
  exact ⟨xC_add_one _, yC_add_one _, fC_add_one _⟩

end Translation

/-! ## §13 Complex conjugation: `x, y, f` have real `q`-expansions (proved)

`φ(−τ̄) = conj φ(τ)`. With the definition of Heegner points through `phiC` (task cm-points), this is the
analytic input of "complex conjugation maps the Heegner point of `[A, B, C]` to that of `[A, −B, C]`"
(`τ_{[A,−B,C]} = −conj τ_{[A,B,C]}`). -/

section Conj

open ModularForm

theorem conj_qParam (h : ℝ) (z : ℂ) :
    starRingEnd ℂ (Function.Periodic.qParam h z) = Function.Periodic.qParam h (-starRingEnd ℂ z) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_conj, map_div₀, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

/-- **`η(−z̄) = conj η(z)`.** -/
theorem eta_neg_conj (z : ℂ) :
    ModularForm.eta (-starRingEnd ℂ z) = starRingEnd ℂ (ModularForm.eta z) := by
  unfold ModularForm.eta
  rw [map_mul, conj_qParam]
  congr 1
  rw [Function.LeftInverse.map_tprod (g := starRingEnd ℂ) _ Complex.continuous_conj
    Complex.continuous_conj (fun w => Complex.conj_conj w)]
  congr 1
  funext n
  rw [map_sub, map_one]
  congr 1
  simp only [eta_q, map_pow, conj_qParam]

theorem etaD_neg_conj (d : ℕ) (z : ℂ) :
    etaD d (-starRingEnd ℂ z) = starRingEnd ℂ (etaD d z) := by
  unfold etaD
  rw [← eta_neg_conj, map_mul, Complex.conj_natCast, mul_neg]

theorem xC_neg_conj (z : ℂ) : xC (-starRingEnd ℂ z) = starRingEnd ℂ (xC z) := by
  simp only [xC, etaD_neg_conj, map_add, map_div₀, map_mul, map_pow, map_ofNat]

theorem yC_neg_conj (z : ℂ) : yC (-starRingEnd ℂ z) = starRingEnd ℂ (yC z) := by
  simp only [yC, etaD_neg_conj, map_neg, map_div₀, map_mul, map_pow]

theorem fC_neg_conj (z : ℂ) : fC (-starRingEnd ℂ z) = starRingEnd ℂ (fC z) := by
  simp only [fC, etaD_neg_conj, map_mul, map_pow]

/-- Complex conjugation as a `ℚ`-algebra map (the same expression as cm-points' `CM.conjQ`). -/
def conjQC : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.toAlgHom).restrictScalars ℚ

theorem conjQC_apply (z : ℂ) : conjQC z = starRingEnd ℂ z := rfl

/-- **`φ(−τ̄) = conj φ(τ)`** on `A(ℂ)` (conjugation acting through `Point.map`). -/
theorem phiC_neg_conj (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = -starRingEnd ℂ (τ : ℂ)) :
    phiC τ' = WeierstrassCurve.Affine.Point.map (W' := curveA) conjQC (phiC τ) := by
  have hx : xC τ' = conjQC (xC τ) := by rw [h, xC_neg_conj]; rfl
  have hy : yC τ' = conjQC (yC τ) := by rw [h, yC_neg_conj]; rfl
  have hiff : curveAC.toAffine.Nonsingular (xC τ') (yC τ') ↔
      curveAC.toAffine.Nonsingular (xC τ) (yC τ) := by
    rw [hx, hy]
    exact WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA) conjQC.injective _ _
  by_cases hN : curveAC.toAffine.Nonsingular (xC τ) (yC τ)
  · have hN' := hiff.mpr hN
    have e1 : phiC τ = .some (xC τ) (yC τ) hN := by simp [phiC, hN]
    have e2 : phiC τ' = .some (xC τ') (yC τ') hN' := by simp [phiC, hN']
    rw [e1, e2, WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
  · have hN' : ¬ curveAC.toAffine.Nonsingular (xC τ') (yC τ') := fun h' => hN (hiff.mp h')
    have e1 : phiC τ = 0 := by simp [phiC, hN]
    have e2 : phiC τ' = 0 := by simp [phiC, hN']
    rw [e1, e2, map_zero]

end Conj

/-! ## §14 The Fricke involution `W₃₂ : τ ↦ −1/(32τ)` on `x, y, f` (proved)

From Mathlib's `η(−1/z) = (√i)⁻¹ √z η(z)` (`ModularForm.eta_comp_eq_csqrt_I_inv`). In particular `f` is
a `W₃₂`-eigenform with eigenvalue `−1` (`(f|₂W₃₂)(τ) = 32⁻¹τ⁻² f(−1/(32τ)) = −f(τ)`), the sign
attached to root number `+1`. -/

section Fricke

open ModularForm

/-- `c k = e^{(log k)/2} = √k` (as a complex number). -/
def csq (k : ℕ) : ℂ := cexp (Real.log k / 2)

theorem csq_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : csq (a * b) = csq a * csq b := by
  unfold csq
  rw [← Complex.exp_add]
  congr 1
  push_cast
  rw [Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

theorem csq_sq {k : ℕ} (hk : 0 < k) : csq k ^ 2 = k := by
  unfold csq
  rw [← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * ((Real.log k : ℝ) / 2 : ℂ) = ((Real.log k : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hk)]
  push_cast; rfl

theorem csq_one : csq 1 = 1 := by simp [csq]

theorem csq_ne_zero (k : ℕ) : csq k ≠ 0 := Complex.exp_ne_zero _

theorem csqrt_natMul {k : ℕ} (hk : 0 < k) {z : ℂ} (hz : z ≠ 0) :
    Complex.sqrt ((k : ℂ) * z) = csq k * Complex.sqrt z := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [_root_.sqrt_eq_exp (mul_ne_zero (by exact_mod_cast hk.ne') hz), _root_.sqrt_eq_exp hz,
    show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl, Complex.log_ofReal_mul hk' hz, csq,
    ← Complex.exp_add]
  congr 1
  ring

theorem csqrt_sq {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 2 = z := by
  rw [_root_.sqrt_eq_exp hz, ← Complex.exp_nat_mul]
  rw [show ((2 : ℕ) : ℂ) * (Complex.log z / 2) = Complex.log z by push_cast; ring,
    Complex.exp_log hz]

/-- `η(−1/(kτ)) = (√i)⁻¹ · √k · √τ · η(kτ)`. -/
theorem eta_neg_inv_natMul {k : ℕ} (hk : 0 < k) (τ : UpperHalfPlane) :
    ModularForm.eta (-1 / ((k : ℂ) * τ)) =
      (Complex.sqrt I)⁻¹ * (csq k * Complex.sqrt τ * ModularForm.eta ((k : ℂ) * τ)) := by
  have hz := mul_mem_upperHalfPlaneSet hk τ
  have h := ModularForm.eta_comp_eq_csqrt_I_inv hz
  simp only [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  rw [h, csqrt_natMul hk τ.ne_zero]

theorem etaD_fricke {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hde : d * e = 32) (τ : UpperHalfPlane) :
    etaD d (-1 / (32 * (τ : ℂ))) =
      (Complex.sqrt I)⁻¹ * (csq e * Complex.sqrt τ * etaD e τ) := by
  unfold etaD
  have : (d : ℂ) * (-1 / (32 * (τ : ℂ))) = -1 / ((e : ℂ) * τ) := by
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have h32 : (32 : ℂ) = (d : ℂ) * e := by exact_mod_cast hde.symm
    rw [h32]
    field_simp [τ.ne_zero]
  rw [this, eta_neg_inv_natMul he]

theorem csq_values : csq 4 = 2 ∧ csq 16 = 4 ∧ csq 8 = 2 * csq 2 ∧ csq 32 = 4 * csq 2 := by
  have h2 := csq_sq (k := 2) (by norm_num)
  have h4 : csq 4 = 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, csq_mul (by norm_num) (by norm_num), ← sq, h2]; norm_num
  have h16 : csq 16 = 4 := by
    rw [show (16 : ℕ) = 4 * 4 by norm_num, csq_mul (by norm_num) (by norm_num), h4]; norm_num
  have h8 : csq 8 = 2 * csq 2 := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, csq_mul (by norm_num) (by norm_num), h4]
  have h32 : csq 32 = 4 * csq 2 := by
    rw [show (32 : ℕ) = 16 * 2 by norm_num, csq_mul (by norm_num) (by norm_num), h16]
  exact ⟨h4, h16, h8, h32⟩

/-- **`x(W₃₂τ) = 2 + 8η(2τ)η(16τ)²/(η(τ)²η(8τ))`.** -/
theorem xC_fricke (τ : UpperHalfPlane) :
    xC (-1 / (32 * (τ : ℂ))) =
      2 + 8 * (etaD 2 τ * etaD 16 τ ^ 2 / (etaD 1 τ ^ 2 * etaD 8 τ)) := by
  unfold xC
  rw [etaD_fricke (d := 2) (e := 16) (by norm_num) (by norm_num) (by norm_num),
    etaD_fricke (d := 16) (e := 2) (by norm_num) (by norm_num) (by norm_num),
    etaD_fricke (d := 4) (e := 8) (by norm_num) (by norm_num) (by norm_num),
    etaD_fricke (d := 32) (e := 1) (by norm_num) (by norm_num) (by norm_num)]
  obtain ⟨-, h16, h8, -⟩ := csq_values
  rw [h16, h8, csq_one]
  have hs : Complex.sqrt I ≠ 0 := by
    intro h; have := congrArg (· ^ 2) h; simp [csqrt_sq I_ne_zero] at this
  have hr : Complex.sqrt (τ : ℂ) ≠ 0 := by
    intro h; have := congrArg (· ^ 2) h; simp [csqrt_sq τ.ne_zero] at this; exact τ.ne_zero this
  have hc := csq_ne_zero 2
  have e1 := etaD_ne_zero (d := 1) (by norm_num) τ
  have e8 := etaD_ne_zero (d := 8) (by norm_num) τ
  field_simp
  ring

/-- **`y(W₃₂τ) = −4η(2τ)²η(4τ)⁴/(η(τ)⁴η(8τ)²)`.** -/
theorem yC_fricke (τ : UpperHalfPlane) :
    yC (-1 / (32 * (τ : ℂ))) =
      -(4 * (etaD 2 τ ^ 2 * etaD 4 τ ^ 4 / (etaD 1 τ ^ 4 * etaD 8 τ ^ 2))) := by
  unfold yC
  rw [etaD_fricke (d := 8) (e := 4) (by norm_num) (by norm_num) (by norm_num),
    etaD_fricke (d := 16) (e := 2) (by norm_num) (by norm_num) (by norm_num),
    etaD_fricke (d := 4) (e := 8) (by norm_num) (by norm_num) (by norm_num),
    etaD_fricke (d := 32) (e := 1) (by norm_num) (by norm_num) (by norm_num)]
  obtain ⟨h4, -, h8, -⟩ := csq_values
  rw [h4, h8, csq_one]
  have hs : Complex.sqrt I ≠ 0 := by
    intro h; have := congrArg (· ^ 2) h; simp [csqrt_sq I_ne_zero] at this
  have hr : Complex.sqrt (τ : ℂ) ≠ 0 := by
    intro h; have := congrArg (· ^ 2) h; simp [csqrt_sq τ.ne_zero] at this; exact τ.ne_zero this
  have hc := csq_ne_zero 2
  have hc2 := csq_sq (k := 2) (by norm_num)
  have e1 := etaD_ne_zero (d := 1) (by norm_num) τ
  have e8 := etaD_ne_zero (d := 8) (by norm_num) τ
  field_simp
  push_cast at hc2
  linear_combination (0 : ℂ) * hc2

/-- **`f` is a `W₃₂`-eigenform with eigenvalue `−1`**: `f(−1/(32τ)) = −32τ² f(τ)`. -/
theorem fC_fricke (τ : UpperHalfPlane) :
    fC (-1 / (32 * (τ : ℂ))) = -32 * (τ : ℂ) ^ 2 * fC τ := by
  unfold fC
  rw [etaD_fricke (d := 4) (e := 8) (by norm_num) (by norm_num) (by norm_num),
    etaD_fricke (d := 8) (e := 4) (by norm_num) (by norm_num) (by norm_num)]
  obtain ⟨h4, -, h8, -⟩ := csq_values
  rw [h4, h8]
  have hs : Complex.sqrt I ≠ 0 := by
    intro h; have := congrArg (· ^ 2) h; simp [csqrt_sq I_ne_zero] at this
  have hI : Complex.sqrt I ^ 2 = I := csqrt_sq I_ne_zero
  have hτ : Complex.sqrt (τ : ℂ) ^ 2 = τ := csqrt_sq τ.ne_zero
  have hc2 := csq_sq (k := 2) (by norm_num)
  push_cast at hc2
  field_simp
  linear_combination 16 * (etaD 8 τ ^ 2 * etaD 4 τ ^ 2) * Complex.sqrt (τ : ℂ) ^ 4 * hc2 +
    32 * (etaD 8 τ ^ 2 * etaD 4 τ ^ 2) * (Complex.sqrt (τ : ℂ) ^ 2 + τ) * hτ +
    32 * (etaD 8 τ ^ 2 * etaD 4 τ ^ 2) * (τ : ℂ) ^ 2 * (Complex.sqrt I ^ 2 + I) * hI +
    32 * (etaD 8 τ ^ 2 * etaD 4 τ ^ 2) * (τ : ℂ) ^ 2 * Complex.I_sq

end Fricke

end ZInQ.Contrib.TYZGenus.X0
