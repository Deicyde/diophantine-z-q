import ZInQKernel.Contrib.OneProof.H.EichlerBoundCopy
import ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosedReroute.Consumers
import ZInQKernel.Contrib.OneProof.CMBranch

/-! # cm-branch: the non-CM branch at fibres without CM, and `SixContactMin` with the manuscript's CM branch

`CMBranch.lean` proves the CM branch (`cmBranchOut_of`) and the case split (`glueOutputs_of_branches`).
This file supplies the other branch from the chain's own proof: `nonCMBranch_of` is
`HSyn.glueOutputs_of_leaves3_hf_pz_eb` (EichlerBoundCopy) verbatim, with the two glue pieces that the
chain proves from NoCM (FS5, `G0FibreSimple.FibreComTrivial`) taken only at fibres without CM:

* `FibreSimpleNC` (`FibreSimple` at `u` with `NoCMAt u`): proved here (`fibreSimpleNC_of_pieces_hf`),
  the chain's `fibreSimple_of_pieces_hf` with FS5 replaced by the hypothesis `NoCMAt u`;
* `ModularConstituentNC` (`ModularConstituent` at `u` with `NoCMAt u`): a named glue Prop. The chain
  proves the unrestricted Prop from FS5 and `FibreSimple`, each used only at the fibre in question; the
  localized copy of that proof is the remaining work (docs/research/cm-branch.md §5).
-/

namespace HDec
set_option maxHeartbeats 1000000
noncomputable section
namespace CMBranch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open scoped Quaternion TensorProduct

/-- **`FibreSimple` at fibres without CM** (G5-G6 of h-trust, at `u` with `NoCMAt u`). -/
def FibreSimpleNC : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet → NoCMAt Y Φ π u →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

/-- **`ModularConstituent` at fibres without CM** (glue G2, G4, G7-G16 of h-trust, at `u` with
`NoCMAt u`): `HSyn.G0Split.ModularConstituent` with the extra hypothesis `NoCMAt Y Φ π u`. -/
def ModularConstituentNC : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet → NoCMAt Y Φ π u →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* LeafQM.AV.Qbar) (A : ZInQ.DefFaltings.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K LeafQM.AV.Qbar := emb.toAlgebra; Nonempty ((A.baseChange LeafQM.AV.Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent (LeafAdopt.abVarEquiv L.K A)
        (LeafAdopt.abVarEquiv L.K (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K))

/-- The unrestricted Prop gives the restricted one (so the chain's current proof is a proof of
`ModularConstituentNC`, through FS5). -/
theorem modularConstituentNC_of (h : ModularConstituent) : ModularConstituentNC :=
  fun Y Φ π h1 h2 u hu _ y P hP hy => h Y Φ π h1 h2 u hu y P hP hy

theorem fibreSimpleNC_of (h : FibreSimple) : FibreSimpleNC :=
  fun Y Φ π h1 h2 u hu _ K A hF => h Y Φ π h1 h2 u hu K A hF

/-- **`FibreSimpleNC` without FS5** (the chain's `G0FibreSimple.fibreSimple_of_pieces_hf`, verbatim, with
`h5 Y Φ π hR1 hR2 u hu y P hP hval` replaced by the hypothesis `NoCMAt Y Φ π u`): T27 (Yu) gives
`End⁰(P.A) ≅ B` or `≅ M₂(ℚ(√d))`, and the second case has a non-integer element of `com P.q`. -/
theorem fibreSimpleNC_of_pieces_hf (hYu : QMLattice.YuB6Alg) (h1 : G0FibreSimple.EndDivisionDescent)
    (h2 : G0FibreSimple.EndDivisionOfSchemeIso) (h3 : G0FibreSimple.EndDivisionOfEnd0DivisionHF)
    (h4 : G0FibreSimple.CentralizerOfMatrixEnd0HF) : FibreSimpleNC := by
  intro Y Φ π hR1 hR2 u hu hNC K A hF
  obtain ⟨emb, y, P, hP, hval, hiso⟩ := hF
  let _ : Algebra K.K LeafQM.AV.Qbar := emb.toAlgebra
  have hY := hYu LeafQM.AV.Qbar P.A P.surface P.q
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ := h4 LeafQM.AV.Qbar _root_.HFReroute.sigmaQbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := hNC y P hP hval φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  have hPdiv : PkgI3.EndDivision P.A :=
    h3 LeafQM.AV.Qbar _root_.HFReroute.sigmaQbar P.A (G0FibreSimple.division_of_algEquiv e G0FibreSimple.B6_isUnit)
  have hAbar : PkgI3.EndDivision (LeafAdopt.abVarEquiv LeafQM.AV.Qbar (A.baseChange LeafQM.AV.Qbar)) :=
    h2 LeafQM.AV.Qbar _ P.A hiso hPdiv
  exact h1 K.K LeafQM.AV.Qbar A hAbar

/-- **The non-CM branch** from the chain's leaves and glue pieces, with `FibreSimpleNC` and
`ModularConstituentNC` (`HSyn.glueOutputs_of_leaves3_hf_pz_eb`, verbatim, restricted to `NoCMAt u`). -/
theorem nonCMBranch_of (r : HSyn.ResearchLeaves3EB) (t : HSyn.TextbookLeavesHFPZ)
    (hDimF : DimFinite) (hDim : DimBaseChange) (hPMH : ZInQ.H5Neron.ProductModelHeight)
    (hBC : StableHeightBaseChange) (hProdE : ProductExists) (hRev : ReverseIsogeny)
    (hThetaPt : ThetaPointOfFibre) (hCopies : HSyn.HeightCopiesAgree)
    (hSimp : FibreSimpleNC) (hMod : ModularConstituentNC) (h20 : R20Lower) : NonCMBranch := by
  have hBelyi : X1BelyiOnModel := x1BelyiOnModel_of_belyiX1 t.belyiX1
  have hAdd : HeightAdditivity := heightAdditivity_of_h5neron t.t41 r.h5.2 hPMH
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  intro Y Φ π h1 h2 hfib u hu hNC
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (ZInQ.JHeight.Jmap u)))
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu hNC y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  obtain ⟨K', z, hF1, hPaz⟩ := thetaPazuki hR22 hThetaPt Y Φ π h1 h2 u hu L A hFib hA2 _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, ?_⟩
  obtain ⟨f, hf⟩ := hom_of_common3_hf_pz_eb r t _ _ hCC
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu hNC L A hFib) f hf
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  obtain ⟨gJ, hgJ, hgN⟩ := dim_J1_le_of5 t34Le N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := javanpeykarJ1_of_le hR18 hBelyi t34Le N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  exact transfer_core r.r19 h20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

/-- **`SixContactMin` with the manuscript's CM branch** (the assembly this task delivers): the chain's
leaves and glue pieces of `HSyn.sixContactMin_of_leavesR3_hf_pz_eb` without `fibreSimple` and with
`modularConstituent` restricted to fibres without CM, plus the CM-branch leaves (`FowlerProp27`,
`CMHeight62`, `CMjDegree`, `CMPotentialGood`) and glue (`CMFibreSplit`, `ReducedCMPeriod`,
`HeightAdditivityUpper`). FS5 (NoCM), hence González–Rotger's Thm 5.12 and count and the `X₆` Kummer
fibre, are not used. -/
theorem sixContactMin_of_cmBranch (r : HSyn.ResearchLeaves3EB) (t : HSyn.TextbookLeavesHFPZ)
    (hDimF : DimFinite) (hDim : DimBaseChange) (hPMH : ZInQ.H5Neron.ProductModelHeight)
    (hBC : StableHeightBaseChange) (hProdE : ProductExists) (hRev : ReverseIsogeny)
    (hThetaPt : ThetaPointOfFibre) (hCopies : HSyn.HeightCopiesAgree)
    (hYu : QMLattice.YuB6Alg) (h1 : G0FibreSimple.EndDivisionDescent)
    (h2 : G0FibreSimple.EndDivisionOfSchemeIso) (h3 : G0FibreSimple.EndDivisionOfEnd0DivisionHF)
    (h4 : G0FibreSimple.CentralizerOfMatrixEnd0HF)
    (hMod : ModularConstituentNC) (h20 : R20Lower)
    (hSplit : CMFibreSplit) (hF : FowlerProp27) (hJ : CMjDegree) (hPG : CMPotentialGood)
    (h62 : CMHeight62) (hRP : ReducedCMPeriod) (hAddU : HeightAdditivityUpper) :
    _root_.ZInQ.SixContactMin :=
  sixContactMin_of_branches (LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r.r1r2))
    (nonCMBranch_of r t hDimF hDim hPMH hBC hProdE hRev hThetaPt hCopies
      (fibreSimpleNC_of_pieces_hf hYu h1 h2 h3 h4) hMod h20)
    (cmBranchOut_of r.h5.1 hDim (thetaPazuki (r22Concrete_of r.r22 hCopies) hThetaPt) hSplit hF hJ
      hPG h62 hRP hAddU r.r19 h20)

end CMBranch
end
end HDec
