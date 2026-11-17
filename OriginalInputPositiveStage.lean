/-
H5 Lane5 original-DVR SOURCE work, 2026-11-16.

Concrete original-input seam: original K/O/w/hw/A/hS-infinity -> an ACTUALLY
constructed ordinary local-DVR abelian stage and an ACTUALLY constructed original
line / model extension with positive actual fibre H0 and nonzero actual Euler.
No stage model, line, beta, hAS, rank/Pic0 Fact or Factory is a caller premise.

SOURCE DRAFT ONLY, UNCOMPILED/native HELD. The recovered exact source bodies and
all external canonical suppliers need fresh Parent SOURCE/runtime selection.
This is NOT a final HasGoodReduction or NOS proof: relative closed-by-sections
and the actual module-line psi/cocycle must still be constructed, not assumed.
No imported old object/cache world or old host grade is used as a proof body.

Reused actual text: OriginalDataGoodStage f6 + ReadyStageOpen f9d from successful
OWN journal write/edit payloads; lead OriginalStageLineChoice c136 from exact
SOURCE bank169197. Their source/copyright bodies are unchanged in recovery.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.ReadyStageOpen
import OriginalStageLineChoice
import Mathlib.RingTheory.RingHom.FaithfullyFlat

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces
open ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

namespace H5OriginalDVR.Lane5

local notation "SrcInv" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- ONLY original NOS input data. The stage group and both lines are constructed
outputs, not inputs. All actual original coefficient maps/group isomorphisms
and native/Source line identities remain literal. This is a positive-stage
seam, not original-O effective model construction or a claimed NOS theorem. -/
theorem exists_positive_stage_line_of_original_targetOrders
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : Algebra O C) (V : (Base O).Opens) (iV : V.toScheme ≅ Spec (CommRingCat.of K))
      (H : Grp (Over (Cover C)))
      (e : (Over.pullback ((baseMap O C) ⁻¹ᵁ V).ι).mapGrp.obj H ≅
        (Over.pullback ((baseMap O C) ∣_ V)).mapGrp.obj ((Over.pullback iV.hom).mapGrp.obj A)),
      iV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = V.ι ∧
      (∀ z : Base O, z ∉ V → z = closedPoint O) ∧
      Algebra.Etale O C ∧ Module.FaithfullyFlat O C ∧ Etale (baseMap O C) ∧
      IsIso ((baseMap O C).fiberToSpecResidueField (closedPoint O)) ∧
      PkgI2.IsAbelianScheme H ∧ Function.Injective (algebraMap O C) ∧
      ∃ L₀ : A.X.left.Modules, SrcInv L₀ ∧ L₀.IsInvertible ∧
        0 < L₀.hFiber A.X.hom 0 (closedPoint K) ∧
        L₀.eulerCharFiber A.X.hom (closedPoint K) ≠ 0 ∧
        ∃ M : H.X.left.Modules, SrcInv M ∧
          ∃ β : (Scheme.Modules.pullback
              (H.X.hom ⁻¹ᵁ ((baseMap O C) ⁻¹ᵁ V)).ι).obj M ≅
            (Scheme.Modules.pullback
              (ZInQ.Contrib.CloudR2NOS.GoodDescent.genericModelOfGroupIso
                (baseMap O C) V H ((Over.pullback iV.hom).mapGrp.obj A) e).q).obj
                  (pullbackLine iV A L₀),
            M.IsInvertible ∧ 0 < M.hFiber H.X.hom 0 (closedPoint C) ∧
              M.eulerCharFiber H.X.hom (closedPoint C) ≠ 0 := by
  obtain ⟨C, hComm, hDom, hDVR, hAlg, V, iV, H, hiV, hV,
    hEtAlg, hFF, hEt, hFiber, hH, hGen⟩ :=
    exists_ready_stage_open_of_original_targetOrders O w hw A hS
  letI : CommRing C := hComm
  letI : IsDomain C := hDom
  letI : IsDiscreteValuationRing C := hDVR
  letI : Algebra O C := hAlg
  letI : Module.FaithfullyFlat O C := hFF
  letI : PkgI2.IsAbelianScheme H := hH
  obtain ⟨e⟩ := hGen
  have hinj : Function.Injective (algebraMap O C) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hFF).injective
  obtain ⟨L₀, hLsrc, hLnat, hL0, hLχ, M, hMsrc, β, hMnat, hM0, hMχ⟩ :=
    ZInQ.Contrib.CloudR2NOS.Review.OriginalStageLineChoice.
      exists_original_line_and_positive_model_extension hinj V hV iV H A e
  exact ⟨C, hComm, hDom, hDVR, hAlg, V, iV, H, e,
    hiV, hV, hEtAlg, hFF, hEt, hFiber, hH, hinj,
    L₀, hLsrc, hLnat, hL0, hLχ, M, hMsrc, β, hMnat, hM0, hMχ⟩

/-
No inference `H0>0 and Euler!=0 => closed immersion` is made here. That exact
nondegenerate effective-line ampleness/power-presentation edge, and construction
of the literal psi with ActualLineCocycle, remain needed on the SAME constructed
stage before GoodDescentFromLine can construct the original-O model. In
particular NativeEffectivity b6 only supplies an effective Cartier ideal, and
SourceFieldSerre 3ede already assumes a finite section presentation: neither
can be reversed into the missing closed-by-sections input.
-/

end H5OriginalDVR.Lane5
