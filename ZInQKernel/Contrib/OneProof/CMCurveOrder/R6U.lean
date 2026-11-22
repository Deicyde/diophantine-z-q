import ZInQKernel.Contrib.OneProof.CMBranch
import ZInQKernel.Contrib.OneProof.CMCurveOrder
import ZInQKernel.Contrib.OneProof.D2A6Wrap

/-! # CM fibre splitting on the live good-reduction route

The Hom-field proof from `CMFibreSplit.Reduction` uses the proper integral
full-level-three model for good reduction, as in `thm:height`, L529–530 and
L557–561. The curve order and matrix units are the existing proofs of L582–586.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace HDec.CMBranch.FibreSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch
open TwistDescentXC TwistDescentHFD G0ModField G0ModField.KernelField
open scoped Quaternion TensorProduct

/-- A8 for a CM fibre (`thm:height`, L540–561). The Hom-field construction is
unchanged; for good reduction use the integral model in `R6U` and
`T324 ⊆ T u`. -/
theorem cmHomFieldModel_of_R6U (hCover : G0ModField.FibreCoverExists)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) : CMHomFieldModel := by
  intro Y Φ π u P hctx
  obtain ⟨K, hfK, hgK, hKF, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model_hf hHFF hNOS K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3U hNOS hRay hTors K PK (T u) (_root_.HDec.D2A6.T324_subset_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hKF hE hr
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  obtain ⟨hR1, -, -, -⟩ := hctx
  obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2.1 K LeafQM.AV.Qbar K.val yK PK hyK
  have hQP : M3.mk Q = M3.mk P := hQ.symm.trans hyKP
  obtain ⟨e⟩ := Quotient.exact hQP
  obtain ⟨θ₁, θ₁', h11, h12, -⟩ := bc_transport G0FibreSimple.rigidityHom PK K.val Q hbc
  obtain ⟨-, θ₀, θ₀', h01, h02, -⟩ := paste_iso PK.A (le_sup_right : K ≤ E ⊔ K)
  refine ⟨E ⊔ K, inferInstance, hdeg, @PkgI3.AbVar.baseChange K _ PK.A ↥(E ⊔ K) _ (incAlg le_sup_right),
    PkgI3.AbVar.Hom.mk' (θ₀.hom ≫ θ₁.hom ≫ e.φ.hom), PkgI3.AbVar.Hom.mk' (e.ψ.hom ≫ θ₁'.hom ≫ θ₀'.hom),
    ?_, ?_, endBC_surjective_of_homField PK.A le_sup_right hfix⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% e.left, reassoc_of% h11, h01]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h02, reassoc_of% h12, e.right]

/-- The unchanged CM fibre split (`thm:height`, L582–586), using the live A8
good-reduction input and the original curve order proof. -/
theorem cmFibreSplit_of_curveOrder324_R6U (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hCover : G0ModField.FibreCoverExists) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) : CMFibreSplit :=
  cmFibreSplit_of hYu hHF (cmHomFieldModel_of_R6U hCover hHF hNOS hRay hTors)
    (cmMatrixUnitSplit_of (cmCurveOrder_of_324 (cmCurveOrder324_of hHF)))

end HDec.CMBranch.FibreSplit
