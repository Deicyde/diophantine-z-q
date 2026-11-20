import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Reduction
import ZInQKernel.Contrib.OneProof.RC.ElkikPrint.Finiteness

/-! # The genus partner's rationality from Elkik's printed torsion theorem -/

open scoped MatrixGroups
open HeckeRing.GL2
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.ElkikPrint

/-- The base reduction with its finiteness input derived from the torsion print. The
class map must come from the cusps of `Γ₀(N)`; `hAJ` is the same rational-scale cusp
comparison as in `ElkikMD.hElkikMD_of_maninDrinfeld`. -/
theorem hElkikMD_of_elkikTorsion {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))] {J : Type*} [AddCommGroup J]
    {cuspClass : OnePoint ℚ → J}
    (hTorsion : ManinDrinfeldTorsion (newformLevel (Ecurve ℓ)) cuspClass)
    (classOfCusp : CuspOrbits (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) → J)
    (hCuspFactor : ∀ r, cuspClass r = classOfCusp (cuspOrbit (newformLevel (Ecurve ℓ)) r))
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    (hgp : GenusPartner (Ecurve ℓ) d) (Lat : PeriodPair) {κ : ℚ} (hκ : κ ≠ 0)
    (φ : J →+ ℂ ⧸ Lat.lattice.toAddSubgroup)
    (hAJ : ∀ a < d.natAbs, chiD d a ≠ 0 → φ (cuspClass (((a : ℚ) / d.natAbs : ℚ) : OnePoint ℚ)) =
      QuotientAddGroup.mk' Lat.lattice.toAddSubgroup
        ((κ : ℂ) * ElkikMD.cuspSymbol f.toCuspForm ((a : ℚ) / d.natAbs))) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  exact ElkikMD.hElkikMD_of_maninDrinfeld
    (maninDrinfeld_of_torsion hTorsion (cuspClass_finiteRange_of_cuspOrbits classOfCusp hCuspFactor))
    hf hgp Lat hκ φ hAJ


end ZInQ.Manuscript.RC.ElkikPrint
