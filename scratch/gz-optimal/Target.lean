import ZInQKernel.Contrib.OneProof.GrossZagierModuli

/-! gz-optimal: verbatim copy of the target leaf `ZInQ.GZModuli.GrossZagierModuliCd` (with
`GrossZagierModuliAt`, `GrossZagierModuli`), from `ZInQKernel/Contrib/OneProof/GrossZagierModuli.lean`
at 85111fc7, checked against the original by `rfl`. Its dependencies (`IsModularParam`, `modPt`,
`IsHeegnerPointReps`, …) are used from the imported module. -/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp Filter Topology
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine MatrixGroups
open ZInQ.GZModuli (IsModularParam IsHeegnerPointReps modPt)

namespace ZInQ.GZOptimalTarget

def GrossZagierModuliAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ X Y : ℍ → ℂ, IsModularParam N E X Y →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), IsHeegnerPointReps N D β τ →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = ∑ r, modPt E X Y (τ r) →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- `GrossZagierModuliAt` for every elliptic curve over `ℚ`. -/
def GrossZagierModuli : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], GrossZagierModuliAt E

/-- `GrossZagierModuliAt C_d`, `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree (the curves of the
route; implied by `GrossZagierModuli`: `grossZagierModuliCd_of`). -/
def GrossZagierModuliCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → GrossZagierModuliAt (shortCurve (-(d : ℚ) ^ 2))

example : GrossZagierModuliCd = ZInQ.GZModuli.GrossZagierModuliCd := rfl
example (E : WeierstrassCurve ℚ) : GrossZagierModuliAt E = ZInQ.GZModuli.GrossZagierModuliAt E := rfl

end ZInQ.GZOptimalTarget
