/-
H5 lane3: CONVERSE-ONLY status module for the new target (lead 07:41Z, per Parent). 2026-11-17.
New file. SOURCE-ONLY, UNCOMPILED. Universe u.

It proves the original (c) ⇒ (a) with NO forward imports: no FwdEd1, no ForwardBridge, and none of
the lead's `OriginalCriterionAssembly*` modules. The statement is written out in full. It is the
same Prop as `H5Reactivation20261116.OriginalInfiniteConverse.{u}`, but that definition is not
imported.

The proof is the body of lane3 `EndToEnd/OriginalStatus.lean` (b3d94ba5),
`originalInfiniteConverse_status`, with its six named inputs supplied by their bound producers, by
exact name:
* `hKa`: C5 `H5OriginalDVR.Lane5.I0Native.codimOneLocalizationsDetermine`
  (CodimOneLocalizationsDetermine.lean eb972871);
* `hL3`: C2 `H5OriginalDVR.Lane2.B1HeightOneLocalization.heightOneLocalizationDVR` (8b04bd87);
* `hL4`: C2 `H5OriginalDVR.Lane2.B1OffSupportLocalization.offSupportLocalizationTop` (d799d549);
* `hPur`: C5 `H5OriginalDVR.Lane5.I0Native.purityTranslateEquality` (a5c942c4);
* `hInt`: C4 `ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.integralOnIrreducible`
  (FinalSmall a0193e93);
* `hSpan`: C4 `ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.pulledSectionsSpan`
  (FinalSmall a0193e93).

SOURCE STATUS ONLY. It depends on the stage chain's bodies and on the open Source/native gates
recorded in the V5 plans (plan 004 and later). It claims no compile, admission or kernel result.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1StatusV3
import ZInQKernel.Contrib.CloudR2NOS.Step2WiringV2
import OriginalInputPositiveStage
import OriginalSpecialFibreEffectivity
import NativeAuxiliaryFBSFromAffineCore
import NativeApplicationOneAssembly
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3AssemblyFinal
import GM12OriginalDVRConsumer
import CodimOneLocalizationsDetermine
import B1HeightOneLocalizationDVR
import B1OffSupportLocalizationTop
import PurityTranslateEquality
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.FinalSmall

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.EndToEnd

/-- **(c) ⇒ (a) on the original objects, converse only** (no forward edge in the import closure).
Every input is supplied by its bound producer. SOURCE STATUS. -/
theorem originalInfiniteConverse_only :
    ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (w : ValuationSubring (AlgebraicClosure K)),
      w.comap (algebraMap K (AlgebraicClosure K)) = O →
      ∀ (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A],
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite →
        PkgI2.HasGoodReduction A O := by
  have hKa : ZInQ.Contrib.CloudR2NOS.Step2B1.CodimOneLocalizationsDetermine.{u} :=
    H5OriginalDVR.Lane5.I0Native.codimOneLocalizationsDetermine
  have hL3 : ZInQ.Contrib.CloudR2NOS.Step2B1.HeightOneLocalizationDVR.{u} :=
    H5OriginalDVR.Lane2.B1HeightOneLocalization.heightOneLocalizationDVR
  have hL4 : ZInQ.Contrib.CloudR2NOS.Step2B1.OffSupportLocalizationTop.{u} :=
    H5OriginalDVR.Lane2.B1OffSupportLocalization.offSupportLocalizationTop
  have hPur : ZInQ.Contrib.CloudR2NOS.Step2B2.PurityTranslateEquality.{u} :=
    H5OriginalDVR.Lane5.I0Native.purityTranslateEquality
  have hInt : ZInQ.Contrib.CloudR2NOS.Step2B2.IntegralOnIrreducible.{u} :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.integralOnIrreducible
  have hSpan : ZInQ.Contrib.CloudR2NOS.Step2B3.PulledSectionsSpan.{u} :=
    ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.pulledSectionsSpan
  intro K _ O _ w hw A _ hS
  -- 1. the original-input stage (C5)
  obtain ⟨C, hComm, hDom, hDVR, hAlg, V, iV, H, e, hiV, hV, hEtAlg, hFF, hEt, hFiber, hH, hinj,
      L₀, hLsrc, hLnat, hL0, hLχ, M, hMsrc, β, hMnat, hM0, hMχ⟩ :=
    H5OriginalDVR.Lane5.exists_positive_stage_line_of_original_targetOrders O w hw A hS
  letI : CommRing C := hComm
  letI : IsDomain C := hDom
  letI : IsDiscreteValuationRing C := hDVR
  letI : Algebra O C := hAlg
  haveI := hEt
  haveI := hFiber
  haveI := hH
  haveI := hLnat
  haveI := hMnat
  -- 2. the special-fibre seam on the SAME H, M (C5)
  obtain ⟨hHsAV, hMsInv, hχ, θ, hθ, D, hD, hZero, hMsD⟩ :=
    H5OriginalDVR.Lane5.SpecialFibreResearch.effective_and_euler_ne_zero_on_actual_special_fibre
      H M hM0 hMχ
  let s := IsLocalRing.closedPoint C
  let k : Type u := (Spec (CommRingCat.of C)).residueField s
  let g := (Spec (CommRingCat.of C)).fromSpecResidueField s
  let Hs := (Over.pullback g).mapGrp.obj H
  let Ms := (Scheme.Modules.pullback (H.X.hom.fiberι s)).obj M
  haveI : PkgI2.IsAbelianVariety Hs := hHsAV
  haveI : Ms.IsInvertible := hMsInv
  have hχ' : (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
      Ms.eulerChar k) ≠ 0 := hχ
  -- 4. I0 (C2), fed by lane3's wired B2
  have hFin := ZInQ.Contrib.CloudR2NOS.Step2Wiring.finiteSquarePresentation_wired_v2
    hKa hL3 hL4 hPur hInt
  have hI0 := H5OriginalDVR.Lane2.NativeAuxiliaryFBSFromAffineCore.existsFBSLine_of_finiteSquare hFin
  -- 3. Step 1 I1 (lane3), on the SAME Hs, Ms
  have hI1 := ZInQ.Contrib.CloudR2NOS.Step1.stabilizer_finite_of_I0 hI0 (k := k) Hs Ms hχ'
  -- 5. I2 (C2), fed by lane3's wired B2 and B3
  have hDesc := ZInQ.Contrib.CloudR2NOS.Step2Wiring.nativeFBSFieldDescent_wired hSpan
  obtain ⟨b, hb, hFBS⟩ :=
    H5OriginalDVR.Lane2.NativeApplicationOneAssembly.native_positive_power_finite_by_sections_of_effective_and_I1
      hFin hDesc (k := k) Hs Ms θ hθ D hD hZero hI1
  -- 6. I3 (C4) on the SAME H, M
  have hI3 := ZInQ.Contrib.CloudR2NOS.ClosedSection.step3_I3_unconditional H M ⟨b, hb, hFBS⟩
  -- 7. Step 4 (C5): the original-O good model
  exact H5OriginalDVR.Lane5.GM12.OriginalDVR.hasGoodReduction_from_native_power_output
    O hFF V iV hiV hV H A e L₀ M β hI3

end ZInQ.Contrib.CloudR2NOS.EndToEnd
