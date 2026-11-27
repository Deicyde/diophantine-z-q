import ZInQKernel.Contrib.OneProof.CMjReroute.SplitBL
import ZInQKernel.Contrib.OneProof.CMjReroute.Consumer

/-!
# The CM branch without the degree of the singular modulus

`CMBranch.cmBranchOut_of` proves the CM branch (manuscript L581-631) from `CMFibreSplit`, Fowler's
Prop. 2·7, the degree of a singular modulus (`CMjDegree`, L586-587), potentially good reduction,
Eq. (6.2) of Barquero-Sanchez et al., the reduced periods and additivity; the degree is used only in
`CMBranch.faltingsHeight_le_bcm`, to bound `card Pic(R)` by `[L:ℚ] ≤ D` before applying Fowler at `n = D`.

* `cmBranchOut_of_bl`: the same proof from `CMFibreSplitBL`, with `faltingsHeight_le_bcm_of_sub`
  (Fowler at `n = 324` for the sub-order `R₀ ≤ R`) in place of `faltingsHeight_le_bcm`; it has no
  `CMjDegree` hypothesis.
* `CMInputs3BL`: the CM-branch inputs `CMBranch.CMInputs3` without `cmjDegree`, with `CMFibreSplitBL`
  in place of `CMFibreSplit`.
-/

namespace HDec
namespace CMBranch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch

/-- **The CM-branch inputs without the degree of the singular modulus**: `CMInputs3` without the
field `cmjDegree`, with the split carrying the sub-order bound. -/
structure CMjReroute.CMInputs3BL : Prop where
  cmFibreSplit : CMjReroute.CMFibreSplitBL
  fowlerProp27 : FowlerProp27
  cmPotentialGood : CMPotentialGood
  cmHeight62 : CMHeight62

/-- **The CM branch, proved without `CMjDegree`**: `cmBranchOut_of` with `CMFibreSplitBL` and
`CMjReroute.faltingsHeight_le_bcm_of_sub` (Fowler's Prop. 2·7 at `n = 324` for the sub-order of the
split) in place of `faltingsHeight_le_bcm`. -/
theorem CMjReroute.cmBranchOut_of_bl (hfin : StableHeightFinite) (hDim : DimBaseChange)
    (hTP : ThetaPazuki) (hSplit : CMjReroute.CMFibreSplitBL) (hF : FowlerProp27)
    (hPG : CMPotentialGood) (h62 : CMHeight62) (hRP : ReducedCMPeriod)
    (hAddU : HeightAdditivityUpper) (r19 : R19_GaudronRemond) (r20 : R20Lower) : CMBranchOut := by
  intro Y Φ π h1 h2 u hu hCM
  obtain ⟨L, A, E, Pr, k, _, _, R, hFib, hd, hE1, hPr2, hprod, hiso, hR, hCMR, R₀, hle, hR₀,
    hpic⟩ := hSplit Y Φ π h1 h2 u hu hCM
  obtain ⟨emb, y, P, hP, hy, hisoA⟩ := hFib
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hisoA P.surface
  obtain ⟨K', z, hF1, hPaz⟩ := hTP Y Φ π h1 h2 u hu L A ⟨emb, y, P, hP, hy, hisoA⟩ hA2 _
    (faltingsHeight_coe hfin A).symm
  refine ⟨K', z, faltingsHeight A, hF1, hPaz, ?_⟩
  exact cmOutput_of hfin hAddU r19 r20 A E Pr hd
    (CMjReroute.faltingsHeight_le_bcm_of_sub hfin hF hPG h62 hRP E hE1 R R₀ hR hR₀ hle hpic hCMR)
    hPr2 hprod hiso

end CMBranch
end HDec
