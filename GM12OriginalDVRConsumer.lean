/-
H5 Lane5 GM12 — original-DVR consumer of the derived I3 power output.
SOURCE ONLY, UNCOMPILED; source/default-limit/CI/Std3/native gates remain open.

NO-LINE ANALYSIS IN THE THEOREM STRUCTURE:
The conclusion below is PkgI2.HasGoodReduction A O: an abelian-scheme GROUP
on ORIGINAL O and generic GROUP fibre ≅ SAME A/K, with no line in the result.
Its C/H/M/L0/beta/hFF/I3 arguments are INTERMEDIATE stage outputs, not final
NOS premises. The original-input producer constructs L0 and M existentially.
The final (c)⇒(a) wrapper must first call that producer and then C4's genuine
I3 supplier; no line/model/FBS/Factory premise may be inserted into NOS.

The descended line here is EXACTLY Source.tensorPow M n, and L0' is EXACTLY
Source.tensorPow L0 n on the SAME A. beta_n uses the actual Source monoidal
pullback/power maps on the original beta. C6 constructs the canonical psi
and proves its actual cocycle; they are not input Facts. The stage's derived
FF is installed before the effective-descent consumer is called.

No wholesale FLT port, Source/W07 alias, high numeric option, native run,
protected-source edit, field or dimension restriction occurs in this file.
All referenced Source definitions/theorems and surviving producer imports
are listed separately for later binding review, not presumed admitted.
-/
import GM12FiniteSectionsTransport
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleCoefficientBridge
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorActualCocycle
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GoodDescentFromLine
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericLineCohomology

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ZInQ.Contrib.CloudR2NOS.GoodDescent
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces
open ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

namespace H5OriginalDVR.Lane5.GM12.OriginalDVR

local notation "SrcInv" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible
local notation "SrcFinite" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
local notation "SPow" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.tensorPow

/-- Both powers' Source invertibility is proved from the actual native/Source
pointwise-unit criterion and the constructed power isomorphism. -/
theorem source_invertible_power {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible] (n : ℕ) :
    SrcInv (SPow M n) :=
  (ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.
      source_isInvertible_iff_sheaf (SPow M n)).mpr
    (SourcePower.nativeInvertible M n)

/-- This is the GM12 INTERMEDIATE composition from I3 on the actual original
stage. It produces a no-line ORIGINAL-O good-reduction conclusion, including
its generic GROUP iso, and does not declare the upstream I3 proof finished. -/
theorem hasGoodReduction_from_native_power_output
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    {C : Type u} [CommRing C] [Algebra O C]
    (hFF : Module.FaithfullyFlat O C)
    (V : (Base O).Opens) (iV : V.toScheme ≅ Spec (CommRingCat.of K))
    (hiV : iV.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = V.ι)
    (hV : ∀ z : Base O, z ∉ V → z = closedPoint O)
    (H : Grp (Over (Cover C))) [PkgI2.IsAbelianScheme H]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (e : (Over.pullback ((baseMap O C) ⁻¹ᵁ V).ι).mapGrp.obj H ≅
      (Over.pullback ((baseMap O C) ∣_ V)).mapGrp.obj ((Over.pullback iV.hom).mapGrp.obj A))
    [Etale (baseMap O C)]
    [IsIso ((baseMap O C).fiberToSpecResidueField (closedPoint O))]
    (L0 : A.X.left.Modules) [L0.IsInvertible]
    (M : H.X.left.Modules) [M.IsInvertible]
    (beta : (Scheme.Modules.pullback
        (H.X.hom ⁻¹ᵁ ((baseMap O C) ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback
        (genericModelOfGroupIso (baseMap O C) V H
          ((Over.pullback iV.hom).mapGrp.obj A) e).q).obj (pullbackLine iV A L0))
    (hI3 : ∃ a : ℕ, 0 < a ∧
      SrcFinite (_root_.AlgebraicGeometry.Scheme.Modules.tensorPow M a) H.X.hom) :
    PkgI2.HasGoodReduction A O := by
  -- hFF is the ORIGINAL stage-producer output, not a final additional Fact.
  letI : Module.FaithfullyFlat O C := hFF
  obtain ⟨n, hn, hclosed⟩ := FiniteSections.exists_closed_source_power_of_I3 M hI3
  let A_v := (Over.pullback iV.hom).mapGrp.obj A
  let q := (genericModelOfGroupIso (baseMap O C) V H A_v e).q
  let r := pullback.fst A.X.hom iV.hom
  let M_n := SPow M n
  let L0' := SPow L0 n
  let L_v' := pullbackLine iV A L0'
  have hM_n : SrcInv M_n := source_invertible_power M n
  have hL0' : SrcInv L0' := source_invertible_power L0 n
  -- The isomorphism is on the SAME M/L0 and original generic maps.
  have beta_n : (Scheme.Modules.pullback
        (H.X.hom ⁻¹ᵁ ((baseMap O C) ⁻¹ᵁ V)).ι).obj M_n ≅
      (Scheme.Modules.pullback q).obj L_v' :=
    SourcePower.originalBetaPow
      (H.X.hom ⁻¹ᵁ ((baseMap O C) ⁻¹ᵁ V)).ι q r M L0 beta n
  let psi := ZInQ.Contrib.CloudR2NOS.Review.LineDescent.tensorLineIso
    C V H A_v e (closedPoint O) hV M_n L_v' beta_n
  have hpsi : ActualLineCocycle C V H A_v e (closedPoint O) hV M_n psi :=
    ZInQ.Contrib.CloudR2NOS.Review.LineDescent.tensorLineIso_actualLineCocycle
      C V H A_v e (closedPoint O) hV M_n L_v' beta_n
  -- The effective constructor returns the original-O abelian GROUP model
  -- and original-K GROUP iso; the line data do not enter HasGoodReduction.
  exact hasGoodReduction_from_actual_line O C V iV hiV hV H A e
    M_n hM_n hclosed psi hpsi

/-
The exact remaining ORIGINAL-input assembly is not admitted here:
  K/O/w/hw/A[AV]/hS∞ -> constructed C/H/L0/M/beta/hFF from83ada ->
  genuine I1/I2/I3 producers -> hasGoodReduction_from_native_power_output.
Only the original input telescope may appear in that final wrapper. Until
C4 supplies I3 from the constructed stage and the other lanes' actual proofs,
this intermediate composition must not be relabelled (c)⇒(a) or NOS.
-/

end H5OriginalDVR.Lane5.GM12.OriginalDVR
