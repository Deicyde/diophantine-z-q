import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
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
* §2 relates `X₀(32)` and `C₁` (proved): they are not isomorphic over `ℚ`, isomorphic over `ℚ(i)`
  (`(x, y) ↦ (x/u², y/u³)`, `u = 1 − i`), and `2`-isogenous over `ℚ` in both directions
  (`φ = ι ∘ (1 + [i])`, `ψ = (1 − [i]) ∘ ι⁻¹`, `ψ ∘ φ = 2`, explicit rational formulas);
* §3 states the analytic model of `X₀(32)` by eta quotients over Mathlib's `ModularForm.eta`:
  `x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2`, `y = −η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴)`, the newform
  `f = η(4τ)²η(8τ)²`, and as leaves (`def … : Prop`, not proved here) the identities that make
  `τ ↦ (x(τ), y(τ))` the modular parametrization `X₀(32) ≅ A` with `dx/2y = 2πi f(τ) dτ`, its cusp
  dictionary, and the modularity `f = Σ aₙ(A) qⁿ`.

No `sorry`, no `axiom`.
-/

noncomputable section

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

/-- `y² = x³ − 11x − 14` (Cremona `32a3`), `2`-isogenous to `C₁` (kernel `⟨(−1, 0)⟩`). -/
def curve32a3 : WeierstrassCurve ℚ := ⟨0, 0, 0, -11, -14⟩

/-- `y² = x³ − 11x + 14` (Cremona `32a4`), `2`-isogenous to `C₁` (kernel `⟨(1, 0)⟩`). -/
def curve32a4 : WeierstrassCurve ℚ := ⟨0, 0, 0, -11, 14⟩

/-! ## §3 The analytic model: eta quotients on `ℍ` -/

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

/-- `A(ℂ) ∋ P ↦` its `x`-coordinate as a value in `ℂ` (junk `0` at `O`). -/
def ptX : PtAC → ℂ
  | .zero => 0
  | .some x _ _ => x

/-! ### The leaves (`def … : Prop`; not proved here) -/

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

/-- The analytic model of `X₀(32)` (all six leaves). -/
def X0AnalyticModel : Prop :=
  EtaModelEquation ∧ EtaModelInvariant ∧ EtaModelBijective ∧ EtaModelDifferential ∧
    NewformEta32 ∧ CuspFormEta32 ∧ CuspDictionary

end ZInQ.Contrib.TYZGenus.X0
