import TailK

/-!
# leafq-check: `ThetaRatiosAlgebraic` (LEAF?) — verbatim copy over leaf-fold4's chain

The Prop `HDec.HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` is copied verbatim (docstring and body) from `scratch/leaf-fold4/Leaves4.lean`
(def at line 43228), inside the sub-namespace `HDec.HSyn.G0Split.ThetaPt.LeafQCheckCopy` with the `open`s in force at its
location; what it depends on is imported from leaf-fold4's olean chain (`import TailK`, the same
constants as the flat file). `copy_iff` checks that the copy is the chain's Prop. Verdict, published
statement and decomposition: docs/research/leafq-check.md §2.5. Check: `scratch/leafq-check/chk.sh scratch/leafq-check/ThetaRatiosAlgebraic.lean`.
-/

namespace HDec.HSyn.G0Split.ThetaPt

open scoped MatrixGroups ModularForm
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight)
open Complex

namespace LeafQCheckCopy

/-- **LEAF candidate (theta-constant ratios are algebraic numbers).** For an abelian variety `A`
over a number field `K`, a uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` and any period matrix
`Ω ∈ 𝔥₂` of `Λ`: some theta constant `θ_{m₀}(0, Ω)` is nonzero and every ratio
`θ_m(0, Ω)/θ_{m₀}(0, Ω)` is an algebraic number. This is the form in which the literature states
it (values of Siegel modular functions with algebraic Fourier coefficients at a point whose
principally polarized abelian variety is defined over `ℚ̄` are algebraic: Shimura, Duke 43 (1976);
for genus 2 also Thomae's formula, Mumford, *Tata Lectures on Theta II*, IIIa §8; with
`NS(A_ℚ̄) = NS(A_ℂ)` for the polarization defined by `Ω`; all locators UNVERIFIED). Nonvanishing:
at most one of the ten even `θ_m(0, Ω)` vanishes in genus 2 (it vanishes exactly on products of
elliptic curves; UNVERIFIED locator: Igusa 1962/1967). `ThetaNullAlgebraic` follows
(`thetaNullAlgebraic_of_ratios`, proved). -/
def ThetaRatiosAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ), IsUniformization σ Λ Φu →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∃ m₀ : Char2, thetaConst Ω m₀ ≠ 0 ∧ ∀ m, IsAlgebraic ℚ (thetaConst Ω m / thetaConst Ω m₀)

end LeafQCheckCopy

theorem LeafQCheckCopy.copy_iff : LeafQCheckCopy.ThetaRatiosAlgebraic ↔ ThetaRatiosAlgebraic := Iff.rfl

end HDec.HSyn.G0Split.ThetaPt
