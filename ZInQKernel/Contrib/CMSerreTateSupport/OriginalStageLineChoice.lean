import ZInQKernel.Contrib.CloudR2NOS.Review.ActualExtensionNativePositivity
import Lean

/-
H5 lead source-only composition of the existing original-A native line choice,
the actual Source/native invertibility bridge, and C6's actual M/original-beta
extension constructor. This is an intermediate stage theorem, NOT NOS.

No line, model coefficient M, beta, H0 positivity or Euler nonvanishing is
supplied. The given stage scheme/group/isomorphism data remain explicit.
The file is UNCOMPILED until the five C6 consumers have genuine source-paired
outputs in a single parent-selected current context and this additional check
is separately selected. No existing source, provider or prefix is changed.
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

namespace ZInQ.Contrib.CloudR2NOS.Review.OriginalStageLineChoice

local notation "SrcInv" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- Construct both the original line and its actual positive model extension.
All stage maps, the generic open and the original group isomorphism are retained. -/
theorem exists_original_line_and_positive_model_extension
    {O Bs : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing Bs] [IsDomain Bs] [IsDiscreteValuationRing Bs] [Algebra O Bs]
    (hinj : Function.Injective (algebraMap O Bs))
    (V : (Spec (CommRingCat.of O)).Opens)
    (hV : ∀ z : Spec (CommRingCat.of O), z ∉ V → z = IsLocalRing.closedPoint O)
    {K : Type u} [Field K] (iV : V.toScheme ≅ Spec (CommRingCat.of K))
    (G : Grp (Over (Spec (CommRingCat.of Bs)))) [PkgI2.IsAbelianScheme G]
    (A₀ : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A₀]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ∣_ V)).mapGrp.obj
        ((Over.pullback iV.hom).mapGrp.obj A₀)) :
    ∃ L₀ : A₀.X.left.Modules, SrcInv L₀ ∧ L₀.IsInvertible ∧
      0 < L₀.hFiber A₀.X.hom 0 (IsLocalRing.closedPoint K) ∧
      L₀.eulerCharFiber A₀.X.hom (IsLocalRing.closedPoint K) ≠ 0 ∧
      ∃ M : G.X.left.Modules, SrcInv M ∧
        ∃ β : (Scheme.Modules.pullback
              (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
            (Scheme.Modules.pullback (ZInQ.Contrib.CloudR2NOS.GoodDescent.genericModelOfGroupIso
              (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
                ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀),
          M.IsInvertible ∧ 0 < M.hFiber G.X.hom 0 (IsLocalRing.closedPoint Bs) ∧
            M.eulerCharFiber G.X.hom (IsLocalRing.closedPoint Bs) ≠ 0 := by
  obtain ⟨L₀, hL₀, h0, hχ⟩ :=
    ZInQ.Contrib.CloudR2NOS.SingleOrder.GenericLinePositivity.exists_line_hFiber_pos_eulerCharFiber_ne_zero A₀
  have hSrc : SrcInv L₀ :=
    (ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.source_isInvertible_iff_sheaf L₀).mpr hL₀
  obtain ⟨M, hM, β, hMn, hM0, hMχ⟩ :=
    ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.exists_actual_extension_special_positive_of_originalLine
      hinj V hV iV G A₀ e L₀ hSrc h0 hχ
  exact ⟨L₀, hSrc, hL₀, h0, hχ, M, hM, β, hMn, hM0, hMχ⟩

namespace Audit

/-- Independently written entire stage contract, not a self-type comparison. -/
def Expected : Prop :=
  ∀ {O Bs : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing Bs] [IsDomain Bs] [IsDiscreteValuationRing Bs] [Algebra O Bs],
    Function.Injective (algebraMap O Bs) →
    ∀ (V : (Spec (CommRingCat.of O)).Opens),
    (∀ z : Spec (CommRingCat.of O), z ∉ V → z = IsLocalRing.closedPoint O) →
    ∀ {K : Type u} [Field K] (iV : V.toScheme ≅ Spec (CommRingCat.of K))
      (G : Grp (Over (Spec (CommRingCat.of Bs)))) [PkgI2.IsAbelianScheme G]
      (A₀ : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A₀]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V).ι).mapGrp.obj G ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ∣_ V)).mapGrp.obj
          ((Over.pullback iV.hom).mapGrp.obj A₀)),
      ∃ L₀ : A₀.X.left.Modules, SrcInv L₀ ∧ L₀.IsInvertible ∧
        0 < L₀.hFiber A₀.X.hom 0 (IsLocalRing.closedPoint K) ∧
        L₀.eulerCharFiber A₀.X.hom (IsLocalRing.closedPoint K) ≠ 0 ∧
        ∃ M : G.X.left.Modules, SrcInv M ∧
          ∃ β : (Scheme.Modules.pullback
                (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
              (Scheme.Modules.pullback (ZInQ.Contrib.CloudR2NOS.GoodDescent.genericModelOfGroupIso
                (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
                  ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀),
            M.IsInvertible ∧ 0 < M.hFiber G.X.hom 0 (IsLocalRing.closedPoint Bs) ∧
              M.eulerCharFiber G.X.hom (IsLocalRing.closedPoint Bs) ≠ 0

/-- Wrong scope: a Type-0-only contract does not match the universe-u theorem. -/
def NegativeTypeZero : Prop := Expected.{0}

/-- Wrong direction: supplying the original positive line is not constructing it. -/
def NegativeCallerLine : Prop :=
  ∀ {O Bs : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing Bs] [IsDomain Bs] [IsDiscreteValuationRing Bs] [Algebra O Bs],
    Function.Injective (algebraMap O Bs) →
    ∀ (V : (Spec (CommRingCat.of O)).Opens),
    (∀ z : Spec (CommRingCat.of O), z ∉ V → z = IsLocalRing.closedPoint O) →
    ∀ {K : Type u} [Field K] (iV : V.toScheme ≅ Spec (CommRingCat.of K))
      (G : Grp (Over (Spec (CommRingCat.of Bs)))) [PkgI2.IsAbelianScheme G]
      (A₀ : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A₀]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V).ι).mapGrp.obj G ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ∣_ V)).mapGrp.obj
          ((Over.pullback iV.hom).mapGrp.obj A₀)) (L₀ : A₀.X.left.Modules),
      SrcInv L₀ → L₀.IsInvertible →
      0 < L₀.hFiber A₀.X.hom 0 (IsLocalRing.closedPoint K) →
      L₀.eulerCharFiber A₀.X.hom (IsLocalRing.closedPoint K) ≠ 0 →
      ∃ M : G.X.left.Modules, SrcInv M ∧
        ∃ β : (Scheme.Modules.pullback
              (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
            (Scheme.Modules.pullback (ZInQ.Contrib.CloudR2NOS.GoodDescent.genericModelOfGroupIso
              (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
                ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀),
          M.IsInvertible ∧ 0 < M.hFiber G.X.hom 0 (IsLocalRing.closedPoint Bs) ∧
            M.eulerCharFiber G.X.hom (IsLocalRing.closedPoint Bs) ≠ 0

open Lean Meta Elab Command

/-- Return a real whole-type match. Lookup or resource failures propagate. -/
private def sameWholeType (actual expected : Name) : TermElabM Bool := do
  let ci ← getConstInfo actual
  let .thmInfo _ := ci | throwError "not a theorem: {actual}"
  let ei ← getConstInfo expected
  let some ev := ei.value? | throwError "expected statement missing: {expected}"
  if ci.levelParams.length != ei.levelParams.length then return false
  let rhs := ev.instantiateLevelParams ei.levelParams (ci.levelParams.map Level.param)
  if ci.type.hasLevelMVar || rhs.hasLevelMVar || ci.type.hasMVar || rhs.hasMVar then
    throwError "metavariable in declaration/expected whole type"
  isDefEq ci.type rhs

run_cmd liftTermElabM do
  let actual := ``exists_original_line_and_positive_model_extension
  unless ← sameWholeType actual ``Expected do
    throwError "entire original-stage line-choice type differs"
  let ci ← getConstInfo actual
  let .thmInfo ti := ci | throwError "no stored theorem body"
  let ax ← collectAxioms actual
  for a in ax do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "non-AX3 axiom: {a}"
  logInfo m!"ORIGINAL_STAGE_LINE_WHOLE_TYPE_KIND_RIGID_U_AX3_OK {actual} {ci.levelParams} {ax}"
  for n in [``NegativeTypeZero, ``NegativeCallerLine] do
    if ← sameWholeType actual n then throwError "wrong contract accepted: {n}"
    logInfo m!"ORIGINAL_STAGE_LINE_NEGATIVE_REJECTED {n}"
  let used := ti.value.getUsedConstants
  for a in [
      ``ZInQ.Contrib.CloudR2NOS.SingleOrder.GenericLinePositivity.exists_line_hFiber_pos_eulerCharFiber_ne_zero,
      ``ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.source_isInvertible_iff_sheaf,
      ``ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.exists_actual_extension_special_positive_of_originalLine] do
    unless used.contains a do throwError "actual proof does not use supplier {a}"
  logInfo m!"ORIGINAL_STAGE_LINE_BODY_SUPPLIERS_OK {actual}"

end Audit
end ZInQ.Contrib.CloudR2NOS.Review.OriginalStageLineChoice
