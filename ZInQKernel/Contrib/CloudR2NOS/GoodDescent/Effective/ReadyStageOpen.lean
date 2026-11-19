/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Thin ready-stage OPEN-interface consumer of the frozen original-data stage
producer. No H4/model/counting/line theorem is copied: the genuine stage is
obtained from OriginalDataGoodStage, the original-O/ORIGINAL-K generic open
from DVRGenericOpen, and the SAME original-K GROUP iso is converted using
GenericBaseChange. The complete output is the literal stage-side interface
of hasGoodReduction_from_actual_line. Actual native M/VA/psi/coherence
suppliers remain separately owned by C6; this is NOT full NOS or effectivity.
One canonical cp7/Lane4 Source world, no new H5 Lake Source-world mixture.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.OriginalDataGoodStage
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.DVRGenericOpen
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericBaseChange
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces OrdinaryStages

/-- The actual SAME good stage, now with the literal original-K generic
    OPEN/group interface needed by the original-O effective constructor.
    All data are output; no caller model/presentation/base/property is added. -/
theorem exists_ready_stage_open_of_original_targetOrders
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : Algebra O C) (V : (Base O).Opens) (iV : V.toScheme ≅ Spec (CommRingCat.of K))
      (H : Grp (Over (Cover C))),
      iV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = V.ι ∧
      (∀ z : Base O, z ∉ V → z = closedPoint O) ∧
      Algebra.Etale O C ∧ Module.FaithfullyFlat O C ∧
      Etale (baseMap O C) ∧
      IsIso ((baseMap O C).fiberToSpecResidueField (closedPoint O)) ∧
      PkgI2.IsAbelianScheme H ∧
      Nonempty ((Over.pullback ((baseMap O C) ⁻¹ᵁ V).ι).mapGrp.obj H ≅
        (Over.pullback ((baseMap O C) ∣_ V)).mapGrp.obj ((Over.pullback iV.hom).mapGrp.obj A)) := by
  obtain ⟨E, hE, hPDVR, hHensel, hSep, hPacket⟩ :=
    exists_good_local_stage_of_original_targetOrders O w hw A hS
  let P : ValuationSubring E := w.comap (algebraMap E (AlgebraicClosure K))
  letI : IsDiscreteValuationRing P := hPDVR
  letI : Algebra O P := (comapHom hE).toAlgebra
  obtain ⟨hInd, eκ, hκ, hPoint, hFixed, N, hNGood, hGenE, hNMP,
    C, hComm, hDomain, hDVR, hAlg, H, β, hEt, hFF, hFiber,
    hβLocal, hβInj, hβFF, hβSurj, hHGood, hUp, hGen⟩ := hPacket
  letI : CommRing C := hComm
  letI : IsDomain C := hDomain
  letI : IsDiscreteValuationRing C := hDVR
  letI : Algebra O C := hAlg
  letI : Algebra.Etale O C := hEt
  obtain ⟨V, iV, hiV, hV⟩ := exists_dvr_genericOpen_originalField O K
  obtain ⟨gen⟩ := hGen
  let genOpen := genericGroupIso_open_of_pullback (baseMap O C) V A H iV
    (Spec.map (CommRingCat.ofHom (algebraMap O K))) hiV gen
  have hEtSpec : Etale (baseMap O C) := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap O C)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap O C).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  refine ⟨C, hComm, hDomain, hDVR, hAlg, V, iV, H, hiV, hV, hEt, hFF, hEtSpec, ?_, hHGood, ⟨genOpen⟩⟩
  exact hFiber

#print axioms exists_ready_stage_open_of_original_targetOrders

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
