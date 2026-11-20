import ZInQKernel.Contrib.OneProof.NOSNarrow
import ZInQKernel.Contrib.OneProof.CMBranchUC8

/-! # NOS narrowing on the CM-branch route (fibres without CM)

Since fold-cm the live chain reads the Néron–Ogg–Shafarevich field through the localized readers
`G0ModField.KernelField.kernelFieldExistsNC_of_split_hf_u` and `HSyn.modelG3G6NC_of_leaves3U`
(`CMBranchUC8.lean`), in place of the readers nos-narrow copied (`NOSNarrow.lean`). Both read only the forward
implication, through the same leaf-level readers: `kernelField_of_model_hf` and `good_of_QML3U` for the kernel
field (L557-560), `D2A6.qmModelG3U_of_z30` for A6 (L752-753). The copies below take `NOSNarrow.NOSForward` (proved:
`NOSNarrow.nosForward_proof`) in place of the field and call nos-narrow's `_nos` readers; otherwise they are
`CMBranchUC8.lean`'s proofs verbatim. Each has an example recovering the original signature through
`NOSNarrow.nosForward_of_r7a`.
-/

set_option linter.style.haveILetI false

namespace HDec
set_option maxHeartbeats 1000000
noncomputable section

section KFNOS
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
namespace G0ModField.KernelField
open G0ModField

/-- `kernelFieldExistsNC_of_pieces_hf_u` with the forward implication in place of the NOS field. -/
theorem kernelFieldExistsNC_of_pieces_hf_u_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hCount : TorsionCountPts)
    (hMaps : ConjMapsOnHomFieldNC) : KernelFieldExistsNC := by
  intro Y Φ π u P hctx K _ _ hKF hramK PK hPK
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model_hf_nos hHFF hF K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3U_nos hRay hTors K PK (T u) (_root_.HDec.D2A6.T324_subset_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  obtain ⟨m, hm⟩ := hMaps Y Φ π u P hctx K hKF hramK PK hPK (E ⊔ K) le_sup_right hfix
  obtain ⟨c, hc⟩ := conjugacyData_of_conjMaps _ _ m
    (hCount _ _ (bc_dim le_sup_right PK.A PK.surface)) hm
  exact ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hc⟩

/-- Kernel-field reader at fibres without CM (L557-560) with only the forward implication. -/
theorem kernelFieldExistsNC_of_split_hf_u_nos (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hF : _root_.NOSNarrow.NOSForward) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hYu : QMLattice.YuB6Alg)
    (hmax : OMaximal) (hb : EndTransport) (hG : ConjIsogMaps) : KernelFieldExistsNC :=
  kernelFieldExistsNC_of_pieces_hf_u_nos hHFF hF hRay hTors (torsionCountPts_of_leaf hTors)
    (conjMapsOnHomFieldNC_of (conjMapsNoCM_of hTors hG
      (endEqOOnHomField_of (endEqOFibre_of_hf hYu hHFF hmax) hb)))

example (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : _root_.HDec.D2A6.R6U)
    (hTors : PkgI2.TorsionStructure.{0}) (hYu : QMLattice.YuB6Alg)
    (hmax : OMaximal) (hb : EndTransport) (hG : ConjIsogMaps) : KernelFieldExistsNC :=
  kernelFieldExistsNC_of_split_hf_u_nos hHFF (_root_.NOSNarrow.nosForward_of_r7a hNOS) hRay hTors hYu hmax hb hG

end G0ModField.KernelField
end KFNOS

section MGNOS
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

namespace HSyn
/-- A6 reader at fibres without CM (L752-753) with only the forward implication. -/
theorem modelG3G6NC_of_leaves3U_nos (hFS : CMBranch.FibreSimpleNC) (hF : _root_.NOSNarrow.NOSForward)
    (hRay : D2A6.R6U) (_hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6NC :=
  HSyn.LinkedTate.modelG3G6NC_of_U hFS (_root_.HDec.D2A6.qmModelG3U_of_z30_nos hF hRay.2)

example (hFS : CMBranch.FibreSimpleNC) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : D2A6.R6U) (hTors : PkgI2.TorsionStructure.{0}) :
    G0AssembleMod.ModelG3G6NC :=
  modelG3G6NC_of_leaves3U_nos hFS (_root_.NOSNarrow.nosForward_of_r7a hNOS) hRay hTors
end HSyn
end MGNOS

end
end HDec

#print axioms HDec.G0ModField.KernelField.kernelFieldExistsNC_of_split_hf_u_nos
#print axioms HDec.HSyn.modelG3G6NC_of_leaves3U_nos
