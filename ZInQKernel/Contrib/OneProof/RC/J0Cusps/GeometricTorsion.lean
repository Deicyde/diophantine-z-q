import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeightedComparison
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Reduction

/-! Apply the existing Elkik torsion statement to the represented Jacobian's
classes. Tex 2937–2943 and 11158–11160. The specialization is on the spot (c). -/

noncomputable section

open CategoryTheory MonObj PkgI3 HeckeRing.GL2
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The printed torsion statement applied to the actual geometric classes
implies finiteness of their generated subgroup in the represented Jacobian. -/
theorem geometricCuspidalSubgroup_finite (N : ℕ) [NeZero N]
    (hElkik : ElkikPrint.ManinDrinfeldTorsion N (algebraicCuspClass N)) :
    ElkikMD.ManinDrinfeld N (algebraicCuspClass N) :=
  ElkikPrint.maninDrinfeld_of_torsion hElkik
    (ElkikPrint.cuspClass_finiteRange_of_cuspOrbits
      (classOfCusp N (aj0 N) (algebraicCusp N)) (algebraicCuspClass_factors N))

/-- The quadratic reduction on the specified Jacobian, using precisely its
actual geometric cusp classes. -/
theorem hElkikMD_of_geometricTorsion {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))]
    (hElkik : ElkikPrint.ManinDrinfeldTorsion (newformLevel (Ecurve ℓ))
      (algebraicCuspClass (newformLevel (Ecurve ℓ))))
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    (hgp : GenusPartner (Ecurve ℓ) d) (Lat : PeriodPair) {c : ℚ} (hc : c ≠ 0)
    (φ : Additive ((J0 (newformLevel (Ecurve ℓ))).Pt Qbar) →+ ℂ ⧸ Lat.lattice.toAddSubgroup)
    (hAJ : ∀ a < d.natAbs, chiD d a ≠ 0 →
      φ (algebraicCuspClass (newformLevel (Ecurve ℓ)) (((a : ℚ) / d.natAbs : ℚ) : OnePoint ℚ)) =
        QuotientAddGroup.mk' Lat.lattice.toAddSubgroup
          ((c : ℂ) * ElkikMD.cuspSymbol f.toCuspForm ((a : ℚ) / d.natAbs))) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d :=
  ElkikPrint.hElkikMD_of_elkikTorsion hElkik
    (classOfCusp _ (aj0 _) (algebraicCusp _)) (algebraicCuspClass_factors _)
    hf hgp Lat hc φ hAJ


end ZInQ.Manuscript.RC.J0Cusps
