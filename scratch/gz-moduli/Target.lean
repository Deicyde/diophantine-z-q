import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Cd

/-! gz-moduli: verbatim copy of the target `ZInQ.GZHL3.GrossZagierFormulaCd` and of
`ZInQ.GZHL3.GrossZagierFormulaAt` (ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean, lines 185-196,
and GrossZagierHeegner/Cd.lean), checked equal to the originals by `rfl`. -/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp ZInQ.GZHL3
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine Modular MatrixGroups

namespace ZInQ.GZModuliTarget

def GrossZagierFormulaAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℚ), IsPeriodLattice E L → c ≠ 0 → PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = heegnerC E L f c S →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

def GrossZagierFormulaCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → GrossZagierFormulaAt (shortCurve (-(d : ℚ) ^ 2))

example : GrossZagierFormulaCd = ZInQ.GZHL3.GrossZagierFormulaCd := rfl

end ZInQ.GZModuliTarget
