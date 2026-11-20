import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FixedScaleComparison
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupLaw

/-! The fixed projective group law supplies the target operation in the
based comparison at the explicitly rational scale. Tex 1785–1787 and
2937–2942; on the spot (c). -/

noncomputable section

open scoped Classical

open HeckeRing.GL2
open AlgebraicGeometry CategoryTheory MonObj PkgI3 WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The existing Elkik reduction on the represented Jacobian, using the
constructed group law of the fixed target. The scale witness is an input. -/
theorem hElkikMD_atScale {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))]
    (hElkik : ElkikPrint.ManinDrinfeldTorsion (newformLevel (Ecurve ℓ))
      (algebraicCuspClass (newformLevel (Ecurve ℓ))))
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    (hgp : GenusPartner (Ecurve ℓ) d) {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f.toCuspForm Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  obtain ⟨g, hg⟩ := projectiveGroup_exists (Ecurve ℓ)
  letI := g
  exact hElkikMD_atScale_of_projectiveGroup hg hElkik hf hgp hLat hκ hr


end ZInQ.Manuscript.RC.J0Cusps
