import TailK

/-!
# qm-split, row H-44: `ThetaRatiosAlgebraic` split

The row (`HDec.HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic`, leaf-fold4 chain `TailA.lean` l.7345; imported)
has two parts: a nonvanishing statement and an algebraicity statement.

* **LEAF `ThetaNullNonvanishing`** (published form): in genus 2, at most one of the ten even theta constants
  vanishes at a point of the Siegel space.
* **GLUE `ThetaFourthRatiosAlgebraic`** (composite, stated here): for a period matrix `Ω` of an abelian
  surface over a number field, every `θ_m(Ω)⁴/θ_{m₀}(Ω)⁴` with `θ_{m₀}(Ω) ≠ 0` is algebraic.

The row follows (`thetaRatiosAlgebraic_of`): pick an even `m₀` with `θ_{m₀} ≠ 0` (ten even characteristics,
at most one zero), and a number whose fourth power is algebraic is algebraic.

Check: `scratch/qm-split/chk.sh scratch/qm-split/ThetaRatios.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.QMSplitTheta

open CategoryTheory AlgebraicGeometry Limits
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst)

/-- **LEAF (genus 2: at most one even theta constant vanishes).** For `Ω` in the Siegel upper half-space of
degree 2, if `θ_m(Ω) = 0` for an even characteristic `m`, then `θ_{m'}(Ω) ≠ 0` for every other even
characteristic `m'`. (All ten even theta constants are nonzero iff `Ω` is a period matrix of the Jacobian of
a smooth curve of genus 2; exactly one vanishes iff it is a period matrix of a product of elliptic curves.)

Sources: Mumford, *Tata Lectures on Theta II*, Birkhäuser 1984, IIIa §8 (Thomae) and the vanishing criterion
for genus 2 (statement there for hyperelliptic period matrices, with Frobenius' theta formula); Igusa,
*On Siegel modular forms of genus two*, Amer. J. Math. 84 (1962) (`χ₁₀ = −2⁻¹⁴∏θ_m²` vanishes exactly on the
reducible locus, simply); classical (Frobenius); locators UNVERIFIED (no network). Form: the printed
dichotomy with the identification of the two cases dropped (weaker). Even characteristics are those of
pkg-I1's `evenChars` (`a·b ≡ 0 mod 2`); `thetaConst` is the row's (`ZInQ.LeafPush2.thetaConst`). -/
def ThetaNullNonvanishing : Prop :=
  ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω →
    ∀ m ∈ PkgI1.evenChars, ∀ m' ∈ PkgI1.evenChars, m ≠ m' → thetaConst Ω m = 0 → thetaConst Ω m' ≠ 0

/-- **GLUE (composite; algebraicity of fourth powers of theta-constant ratios).** For an abelian surface
`A` over a number field `K`, an analytic uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ`, a period matrix
`Ω ∈ 𝔥₂` of `Λ` and an even `m₀` with `θ_{m₀}(Ω) ≠ 0`, every `θ_m(Ω)⁴/θ_{m₀}(Ω)⁴` is algebraic.

What it needs (each published; locators UNVERIFIED): (1) the polarization `(Im Ω)⁻¹` of `ℂ²/(Ωℤ² + ℤ²)`,
pulled back by the period map, is algebraic (Appell–Humbert, Lefschetz, GAGA) and defined over `ℚ̄`
(`NS(A_ℚ̄) = NS(A_ℂ)`), so `Ω` is a period matrix of a principally polarized abelian surface over `ℚ̄`;
(2) for a Jacobian of a curve `y² = ∏(x − a_i)` over `ℚ̄`, Thomae's formula writes `θ_m⁴/θ_{m₀}⁴` as a
rational function of the `a_i` (Mumford, *Tata II*, IIIa §8); for a product `E₁ × E₂` over `ℚ̄`, Jacobi's
formulas `θ²[a;b](τ)` in terms of `λ(τ)` (genus 1, Mumford *Tata I*); and Weil's dichotomy (a principally
polarized abelian surface is a Jacobian or a product with the product polarization). Equivalently, Shimura's
theorem on values of Siegel modular functions with algebraic Fourier coefficients at algebraic points
(Shimura, Duke Math. J. 43 (1976)). -/
def ThetaFourthRatiosAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ), IsUniformization σ Λ Φu →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ m₀ ∈ PkgI1.evenChars, thetaConst Ω m₀ ≠ 0 →
      ∀ m, IsAlgebraic ℚ ((thetaConst Ω m / thetaConst Ω m₀) ^ 4)

/-- **Row H-44 from the leaf and the glue.** -/
theorem thetaRatiosAlgebraic_of (hN : ThetaNullNonvanishing) (hA : ThetaFourthRatiosAlgebraic) :
    ThetaRatiosAlgebraic := by
  intro K _ _ A σ Λ Φu hU Ω hΩ hP
  -- two distinct even characteristics; one of them has a nonzero theta constant
  have h0 : ((0, 0) : Char2) ∈ PkgI1.evenChars := by decide
  have h1 : ((0, ![0, 1]) : Char2) ∈ PkgI1.evenChars := by decide
  have hne : ((0, 0) : Char2) ≠ (0, ![0, 1]) := by decide
  obtain ⟨m₀, hm₀, hθ⟩ : ∃ m₀ ∈ PkgI1.evenChars, thetaConst Ω m₀ ≠ 0 := by
    by_cases hz : thetaConst Ω (0, 0) = 0
    · exact ⟨_, h1, hN Ω hΩ _ h0 _ h1 hne hz⟩
    · exact ⟨_, h0, hz⟩
  exact ⟨m₀, hθ, fun m => IsAlgebraic.of_pow (by norm_num) (hA K A σ Λ Φu hU Ω hΩ hP m₀ hm₀ hθ m)⟩

end HDec.HSyn.G0Split.ThetaPt.QMSplitTheta

#print axioms HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of

example : HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaNullNonvanishing →
    HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.ThetaFourthRatiosAlgebraic →
    HDec.HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic :=
  HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of
