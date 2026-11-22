import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
import TauCeti.FieldTheory.FunctionField.Differential.Dimension

/-!
# Reading translation S2 of the Shimura leaf: the differential line of a Weierstrass curve

The package `RC53Assist/NewformPeriods` reads Shimura 1973, Theorem 1 (clause (iv), the
differential clause) through consequence translations S1–S5 (its README). Translation S2 reads:
"one-dimensional abelian varieties over `ℚ` are elliptic curves with Weierstrass equations, and
`D_A = ℂ ω_A`, `ω_A = dx/(2y + a₁x + a₃)`". It has no Lean statement of its own: the leaf
`Shimura1973Thm1RationalGamma0` already outputs a Weierstrass curve `A/ℚ` and states clause (iv)
with `ω_A` (`PullbackIsMultiple`). S2 is what justifies reading Shimura's quotient `A` that way.

**Precise reduction of S2.** S2 is the conjunction of three steps.
* **S2a** (scheme level; blocked by library absence). A one-dimensional abelian variety over `ℚ`
  (proper, smooth, geometrically connected group scheme) is a smooth projective geometrically
  integral curve of genus one with a rational point (the identity), and its holomorphic
  differentials `D_A` are the holomorphic differentials of that curve. Neither Mathlib nor
  Tau Ceti has abelian varieties, so this step stays a reading translation (or needs a print).
* **S2b** (function-field level; not in this tree). An elliptic function field over `k` with a
  rational place is the function field `k(W)` of a Weierstrass curve `W` with nonzero
  discriminant (Silverman, *The Arithmetic of Elliptic Curves*, III.3.1, from the Riemann–Roch
  spaces `L(2O)`, `L(3O)`). The Tau Ceti snapshot has only the converse direction
  (`WeierstrassCurve.Affine.isEllipticFunctionField`: `k(W)` is elliptic).
* **S2c** (the differential line of `k(W)`):
  - **PROVED here**: the holomorphic Weil differentials of `k(W)` form a one-dimensional
    `k`-vector space (`finrank_holomorphicWeilDifferentials_eq_one`, from Tau Ceti's
    `dim_k Ω(0) = g` and `g(k(W)) = 1`);
  - **PROVED here (restated from Tau Ceti)**: every Kähler differential of `k(W)` is `c · ω` for
    a unique function `c`, `ω = dx/(2y + a₁x + a₃)` (`kaehler_eq_smul_invariantDifferential`);
  - **missing**: that `ω` is holomorphic, i.e. the Kähler–Weil comparison sending `ω` into
    `Ω(0)`, equivalently `div ω = 0` (Silverman III.1.5). Tau Ceti's `InvariantDifferential`
    docstring places this in a file that is not in this snapshot. With it, the two facts above
    give `Ω(0) = k · ω`, and base change to `ℂ` gives `D_A = ℂ ω_A`.

**Classification.** The two S2c facts PROVED; S2a, S2b and the comparison step of S2c remain
reading translations (S2a needs abelian varieties, absent from the library).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open TauCeti

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]

/-- **S2c, dimension**: the holomorphic Weil differentials `Ω(0)` of the function field of a
Weierstrass curve with nonzero discriminant form a one-dimensional `k`-vector space (their
dimension is the genus, which is one). PROVED. -/
theorem finrank_holomorphicWeilDifferentials_eq_one :
    Module.finrank k ↥(weilDifferentialFiltration (0 : Divisor k W.FunctionField)) = 1 := by
  rw [finrank_weilDifferentialFiltration_zero W.isFunctionField
    (WeierstrassCurve.Affine.isIntegrallyClosedIn_functionField W),
    WeierstrassCurve.Affine.genus_functionField W]

/-- **S2c, Kähler differentials** (Tau Ceti, restated): every Kähler differential of the function
field is `c · ω` for a unique function `c`, where `ω = dx/(2y + a₁x + a₃)`. PROVED. -/
theorem kaehler_eq_smul_invariantDifferential (η : KaehlerDifferential k W.FunctionField) :
    ∃! c : W.FunctionField, c • WeierstrassCurve.Affine.invariantDifferential W = η :=
  WeierstrassCurve.Affine.existsUnique_smul_invariantDifferential W η

end ZInQ.Contrib.CloudB3RC53.ModularWeil
