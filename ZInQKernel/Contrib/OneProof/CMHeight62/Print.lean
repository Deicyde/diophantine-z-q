import ZInQKernel.Contrib.OneProof.CMBranch

/-! # cmHeight62, step 1: the print row (Nakkajima–Taguchi, Prop. 1)

`CMBranch.CMHeight62` is the `≤` half of [cmheight, Eq. (6.2)] over `stableFaltingsHeight`. The
files of this directory reduce it to one refereed print, read on page images, plus Lean glue:

* Y. Nakkajima, Y. Taguchi, *A generalization of the Chowla–Selberg formula*, J. reine angew.
  Math. 419 (1991) 119–124, §1 "Heights", Prop. 1, p. 120 (open access: Göttinger
  Digitalisierungszentrum, volume `PPN243919689_0419`, article range `LOG_0011`). The proposition
  is stated as well known, with the references Faltings, Ann. of Math. 119 (1984), and Silverman,
  *Heights and elliptic curves*, in *Arithmetic Geometry* (1986).

The print (p. 120): let `F` be a number field, `d = [F:ℚ]`, `E` an elliptic curve over `𝓞_F`, and
for each `ι : F → ℂ` let `τ_ι` satisfy `Im τ_ι > 0` and `(E ⊗_{𝓞_F,ι} ℂ)(ℂ) ≅ ℂ/(ℤ + ℤτ_ι)`. Then
`exp(−d h(E)) = ∏_ι (Im τ_ι / π)^{1/2} |Δ(τ_ι)|^{1/12}`.

Normalizations, from the same pages. `h(E)` is Faltings' height in the normalization of Deligne,
*Preuve des conjectures de Tate et de Shafarevitch*, Astérisque 121-122 (1985) (reference [2] of
the print, p. 120: "we adopt the one in [2]"); in the tree that is `stableFaltingsHeightDeligne`,
each model height shifted by `(g/2) log π` (`stableFaltingsHeightDeligne_eq`), here `g = 1`. For a
lattice `L ⊂ ℂ`, `Δ(L)` is its discriminant (p. 119), so `Δ(τ) = Δ(ℤ + ℤτ) = (2π)¹² η(τ)²⁴`, which
is `discAn τ`. A numerical check of the normalizations: at `τ = e^{2πi/3}` the right side gives
`h(E) = −0.74875…`, the known minimal value of Deligne's normalization.

Transcription. `F = L`. The elliptic curve over `𝓞_L` is a proper smooth group model `𝒢` of
`E_L` (an abelian scheme of relative dimension one over `𝓞_L`). Its height in the print is the
Arakelov degree of `⋀¹ ω_𝒢` with Deligne's metric over `d`, which is
`M.hodge.modelHeight + (1/2) log π` for any metrization `M` of `𝒢` in dimension `1`
(`MetrizedModel`: lattice `𝒢.detLattice 1`, periods and coefficient maps from analytic
uniformizations of `𝒢(ℂ)_σ`). The row quantifies over such `M`, so it asserts nothing about their
existence; existence is the Lean glue of `Metrization.lean`. The periods are those of `E` at
`σ|_K` (`IsPeriodAt`), since `(E_L)(ℂ)_σ = E(ℂ)_{σ|_K}`. No statement about Néron models or the
infimum over extensions is involved: the print computes the height of the given model.
-/

namespace HDec
namespace CMBranch
namespace H62

open CategoryTheory AlgebraicGeometry
open _root_.CMBranch

/-- **Print row: Nakkajima–Taguchi, J. reine angew. Math. 419 (1991), Prop. 1, p. 120.** For an
elliptic curve `E/K`, a proper smooth group model `𝒢/𝓞_L` of `E_L`, a metrization `M` of `𝒢` in
dimension one, and periods `τ_σ` of `E` at `σ|_K` with `Im τ_σ > 0`:
`exp(−[L:ℚ] h(𝒢)) = ∏_σ (Im τ_σ / π)^{1/2} |Δ(τ_σ)|^{1/12}`, with `h(𝒢)` in Deligne's normalization
(`M.hodge.modelHeight + (1/2) log π`) and `Δ(τ) = (2π)¹² η(τ)²⁴` (`discAn`). -/
def NTProp1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : ZInQ.DefFaltings.AbVar K), E.dim = 1 →
    ∀ 𝒢 : ZInQ.DefFaltings.GroupModel E L, IsProper 𝒢.G.hom →
    ∀ M : ZInQ.DefFaltings.MetrizedModel E L 1, M.model = 𝒢 →
    ∀ τ : (L →+* ℂ) → ℂ,
      (∀ σ, 0 < (τ σ).im ∧
        IsPeriodAt (LeafAdopt.abVarEquiv K E) (σ.comp (algebraMap K L)) (τ σ)) →
      Real.exp (-(Module.finrank ℚ L : ℝ) * (M.hodge.modelHeight + 1 / 2 * Real.log Real.pi)) =
        ∏ σ, ((τ σ).im / Real.pi) ^ (1 / 2 : ℝ) * ‖discAn (τ σ)‖ ^ (1 / 12 : ℝ)

end H62
end CMBranch
end HDec
