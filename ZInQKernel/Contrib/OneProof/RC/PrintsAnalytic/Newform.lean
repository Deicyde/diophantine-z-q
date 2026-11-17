import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.LFunction.Sign
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# Lane RC8: newforms, the modular parametrization of `E_ℓ`, and the GLUE linking them to `L(E, s)`

The analytic prints (Hoffstein–Luo, Bump–Friedberg–Hoffstein, the twisted functional equation,
Waldspurger) are statements about **newforms**. The tree vendors Tau Ceti's genuine theory:
`HeckeRing.GL2.Newform N k` (a nonzero cusp form of level `Γ₁(N)`, weight `k`, with a nebentypus,
a simultaneous eigenvector of the Hecke operators prime to `N`, lying in the new subspace and
normalized by `a₁ = 1`: Miyake's primitive form), its entire L-function `ModularForm.L`, its Fricke
sign `Newform.frickeSign` and Hecke's functional equation
`Λ_N(k - s, f) = i^k ε_N(f) Λ_N(s, f)` (`Newform.frickeCompletedL_sub_eq`, proved there).
A newform of trivial nebentypus is a newform for `Γ₀(N)` (`TauCeti.cuspFormCharSpaceOneEquiv`).

* `nfCoeff f n`: the `n`-th Fourier coefficient `a_n(f)`.
* `newformSign f hχ = i^k ε_N(f)`: **the sign in the functional equation of `f`** (BFH's `ε`,
  Hoffstein–Luo's `w`).
* `twistCoeff a D n = χ_D(n) aₙ`: the coefficients of `L(s, f, χ_D)`.
* `IsNewformOf E f`: `f` has trivial nebentypus and `a_n(f) = a_n(E)` for all `n ≥ 1`, i.e.
  `L(f, s) = L(E, s)`.
* `ModularNewform` (PRINT): every elliptic curve over `ℚ` has a newform (modularity, BCDT Theorem A
  in its Introduction condition (2), and Milne's Theorem 11.19, Remark 11.18 and Proposition 11.21).
* `HasseConvergence` (GLUE): `∑ a_n(E) n^{-s}` converges absolutely on `Re s > 3/2`.
* `TwistDictionary` (GLUE): for a fundamental discriminant `D` prime to the level of the newform of
  `E`, `a_n(E^{(D)}) = χ_D(n) a_n(E)`, with the blueprint's twist `qtwist`.

**Milne, Theorem 11.19 and Remark 11.18** (the manuscript's locator at tex L1781–1786 for the
modular parametrization `φ = α q_f : J₀(N) → E`). Read in J. S. Milne, *Modular functions and
modular forms*, v1.31 (March 22, 2017), p. 117:
* the definition preceding Remark 11.18: "An elliptic curve `E` over `ℚ` is said to be modular if
  there is a nonconstant map `X₀(N) → E` (defined over `ℚ`)";
* Remark 11.18: a pointed curve maps to its Jacobian universally; "Thus to say that `E` is modular
  means that there is a surjective homomorphism `J₀(N) → E`";
* Theorem 11.19: "An elliptic curve `E` over `ℚ` is modular if and only if it satisfies the strong
  Hasse–Weil conjecture (and in fact, there is a map `X₀(N) → E` with `N` equal to the geometric
  conductor of `E`)"; its proof: the pull-back of the Néron differential is `f(z) dz` with `f` a
  weight-2 cusp form for `Γ₀(N)` whose Mellin transform is `Λ(E, s)`;
* Proposition 11.21: elliptic curves with a surjection from `X₀(N)` but none from `X₀(M)`, `M < N`,
  correspond to newforms for `Γ₀(N)` with rational eigenvalues.
Modular curves `X₀(N)`, their Jacobians `J₀(N)` and Hecke correspondences are not in Mathlib or the
tree, so the geometric half (the quotient `q_f : J₀(N) ↠ A_f`, `φ T_q = [a_q] φ`) cannot be stated
over genuine definitions; it is used only by the Heegner-point steps (lanes RC9/RC10). Its analytic
half, the newform `f` with `L(f, s) = L(E, s)`, is `ModularNewform` below; its consequence in the
vocabulary of the shared top layer, the existence of a root number (`RootNumber E w`, Milne's
"strong Hasse–Weil" at the trivial character), is `MilneHasseWeil` in `Milne.lean`. **Use check:** the
11/5 text attributes to Milne a "rational weight-two newform `f` of level `N` and an elliptic
quotient `q_f : J₀(N) ↠ A_f` in the rational isogeny class of `E`". Theorem 11.19 with Remark 11.18
gives `J₀(N) ↠ E` itself and `L(E, s) = L(f, s)`; the newform property is Proposition 11.21 and the
Hecke equivariance `φ T_q = [a_q(f)] φ` is not in the cited statements. Version 19 of the
manuscript replaces this locator by Silverman, *AEC* 2nd ed., Theorems C.13.6 and C.16.4, Amir–Hong
Theorem 3.1, Shimura's Theorem 1 (J. Math. Soc. Japan 25 (1973)) and Faltings (DEPARTURE noted,
not followed: the 11/5 manuscript is the one formalized).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 HeckeRing.GL2 UpperHalfPlane Complex

/-- The `n`-th Fourier coefficient `a_n(f)` of a newform (`f(z) = ∑ a_n e^{2πinz}`; the
`q`-expansion at width `1`, the width of `Γ₁(N)` at `∞`). -/
def nfCoeff {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (n : ℕ) : ℂ :=
  (qExpansion 1 f.toCuspForm).coeff n

/-- **The sign in the functional equation of a newform of trivial nebentypus**: `i^k ε_N(f)`,
where `ε_N(f) = ±1` is the Fricke sign. By Tau Ceti's `Newform.frickeCompletedL_sub_eq`,
`Λ_N(k - s, f) = i^k ε_N(f) Λ_N(s, f)` for every `s`, with `Λ_N(s, f) = N^{s/2}(2π)^{-s}Γ(s)L(s, f)`;
since the sign is `±1` (`Newform.I_zpow_mul_frickeSign_eq_one_or_neg_one`) this is BFH's
`Λ(s, f) = εΛ(k - s, f)` (p. 543) and Hoffstein–Luo's root number `w` (p. 435, (1) at `d = 1`). -/
def newformSign {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (hχ : f.χ = 1) : ℂ :=
  Complex.I ^ k * f.frickeSign hχ

/-- The coefficients `χ_D(n) aₙ` of the twisted Dirichlet series `L(s, f, χ_D) = ∑ χ_D(n) a(n) n^{-s}`
(BFH p. 543; Hoffstein–Luo p. 435). -/
def twistCoeff (a : ℕ → ℂ) (D : ℤ) (n : ℕ) : ℂ :=
  (kronecker D n : ℂ) * a n

/-- **`f` is the newform of `E`**: trivial nebentypus and `a_n(f) = a_n(E)` for every `n ≥ 1`,
i.e. `L(f, s) = L(E, s)` as Dirichlet series (Mathlib's `L(E, s)`). -/
def IsNewformOf (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N] (f : Newform N 2) : Prop :=
  f.χ = 1 ∧ ∀ n : ℕ, 0 < n → nfCoeff f n = lcoeff E n

/-- **Modularity in newform form** (PRINT, composite). Every elliptic curve `E/ℚ` has a newform:
some `f : Newform N 2` of trivial nebentypus with `L(f, s) = L(E, s)`.

Locators: Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over `ℚ`: wild
3-adic exercises*, J. Amer. Math. Soc. 14 (2001) 843–939 (author manuscript read), Theorem A ("If
`E/ℚ` is an elliptic curve, then `E` is modular") with the Introduction's list of equivalent
conditions, condition (2): "The L-function `L(E, s)` of `E` equals the L-function `L(f, s)` for some
eigenform `f` of weight 2 and level `N(E)`"; an eigenform of level `N(E)` with `L(f, s) = L(E, s)`
is new (its eigenvalues would otherwise come from a lower level `M`, and Carayol's theorem would
give conductor `M`). Milne, *Modular functions and modular forms* v1.31, Theorem 11.19 (with its
proof), Remark 11.18 and Proposition 11.21, p. 117 (see the module docstring). This strengthens the
tree's `PoleS12.BCDTThmA`, whose `IsModular` asks only for a `Γ₀(N)` cusp form with the same
coefficients (the blueprint's `Prints.bcdt`); `Bridges.lean` derives `PoleS12.BCDTThmA` from it.
It is stated in addition to the blueprint's `BCDTThmA` because the literal prints of Hoffstein–Luo
and Bump–Friedberg–Hoffstein are about newforms: it is the bridge from them to the curve forms used
by the manuscript. -/
def ModularNewform : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    ∃ (N : ℕ) (_ : NeZero N) (f : Newform N 2), IsNewformOf E f

/-- **Absolute convergence of `L(E, s)` on `Re s > 3/2`** (GLUE, textbook): by Hasse's bound
`|a_p| ≤ 2√p` (Silverman, *AEC*, V.1.1), `|a_n| ≤ d(n) √n`, so `∑ a_n n^{-s}` converges absolutely
for `Re s > 3/2` (Silverman, *AEC*, C.16). Used only to move an entire continuation known on
`Re s > 2` (Hecke's elementary half-plane for weight-2 cusp forms) to the convention `Re s > 3/2`
of `Manuscript.AnalyticRankOne`. -/
def HasseConvergence : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (lcoeff E) s

/-- **The coefficients of a quadratic twist** (GLUE, textbook; not printed in the manuscript).
If `f : Newform N 2` is the newform of `E` and `D` is a fundamental discriminant prime to `N`, then
`a_n(E^{(D)}) = χ_D(n) a_n(E)` for every `n ≥ 1`, i.e. `L(E^{(D)}, s) = L(s, f, χ_D)`. At a prime
`p ∤ DN` the reduction of `E^{(D)}` is good with trace `χ_D(p) a_p`; at `p ∣ D` it is additive
(`a_p = 0 = χ_D(p)`); at `p ∣ N` the twist is unramified, so multiplicative reduction changes from
split to nonsplit according to `χ_D(p)` and additive reduction stays additive; the Euler factors
then match (`χ_D(p)² = 1` for `p ∤ D`). Hoffstein–Luo use exactly this identification ("the
Hasse–Weil L-function `L(E, s) = L(f, s)`", p. 435) for twists. -/
def TwistDictionary : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ (N : ℕ) [NeZero N] (f : Newform N 2),
    IsNewformOf E f → ∀ D : ℤ, IsFundamentalDiscriminant D → IsCoprime D (N : ℤ) →
      ∀ n : ℕ, 0 < n → lcoeff (qtwist E D) n = twistCoeff (lcoeff E) D n

end ZInQ.Manuscript.RC.PrintsAnalytic
