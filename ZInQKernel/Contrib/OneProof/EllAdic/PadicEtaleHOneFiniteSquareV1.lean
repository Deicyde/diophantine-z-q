import ZInQKernel.Contrib.OneProof.EllAdic.FiniteAbDictionary
import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneGeometryFiniteMapsV1
import ZInQKernel.Contrib.OneProof.EllAdic.ExtOneRebaseCompositionV1
import ZInQKernel.Contrib.OneProof.EllAdic.RebaseEndpointMathlibV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped RC53.EllAdic.FiniteAbDictionary

namespace RC53.EllAdic

universe u

local instance geomSquareEtaleEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    (etaleAbRebasePullback σ).IsEquivalence :=
  inferInstanceAs (etaleAbRebaseEquivalence σ).functor.IsEquivalence

local instance geomSquareProEtEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    (proEtAbRebasePullback σ).IsEquivalence :=
  inferInstanceAs (proEtAbRebaseEquivalence σ).functor.IsEquivalence

local instance geomSquareEtaleAdditive {S T : Scheme.{u}} (σ : S ≅ T) :
    (etaleAbRebasePullback σ).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance geomSquareProEtAdditive {S T : Scheme.{u}} (σ : S ≅ T) :
    (proEtAbRebasePullback σ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The finite comparison commutes with geometric rebase, without a bijectivity premise. -/
theorem smallEtaleResidueHOneForward_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p n : ℕ)
    (x : (etaleConstantResidue T p n).H 1) :
    smallEtaleResidueHOneForward S p n (etaleResidueHOne_rebase σ p n x) =
      proEtResidueHOne_rebase σ p n (smallEtaleResidueHOneForward T p n x) := by
  let z : Ab.{u+1} := FiniteAbDictionary.zCoeff
  let M : Ab.{u+1} := liftedResidueCoefficient.{u} p n
  let U := etaleAbRebasePullback σ
  let V := proEtAbRebasePullback σ
  let L := smallEtaleAbPullback S
  let L' := smallEtaleAbPullback T
  let θ : U ⋙ L ≅ L' ⋙ V := smallEtaleRebaseNormalizedMate σ
  let ZT := (constantSheaf T.smallEtaleTopology Ab.{u+1}).obj z
  let FT := etaleConstantResidue T p n
  let tZ := θ.hom.app ZT
  let tM := θ.hom.app FT
  let keZ := (etaleConstantRebaseIso σ).app z
  let kpZ := (proEtConstantRebaseIso σ).app z
  let cSZ := (smallEtaleConstantComparison S).app z
  let cTZ := (smallEtaleConstantComparison T).app z
  let keM := (etaleConstantRebaseIso σ).app M
  let kpM := (proEtConstantRebaseIso σ).app M
  let cSM := (smallEtaleConstantComparison S).app M
  let cTM := (smallEtaleConstantComparison T).app M
  let dS := liftedResidueConstantSheafIso S p n
  let dT := liftedResidueConstantSheafIso T p n
  let lamN := liftedFiniteResidueProEtRebaseIso σ p n
  let iS := smallEtalePulledResidueIso S p n
  let iT := smallEtalePulledResidueIso T p n
  -- Check the actual residue endpoints, before assembling either Ext route.
  have hiS : iS.hom = cSM.hom ≫ dS.hom := by rfl
  have hiT : iT.hom = cTM.hom ≫ dT.hom := by rfl
  have hZ : L.map keZ.hom ≫ tZ ≫ V.map cTZ.hom = cSZ.hom ≫ kpZ.hom := by
    exact smallEtaleConstantComparison_rebase σ z
  have hM : L.map keM.hom ≫ tM ≫ V.map cTM.hom = cSM.hom ≫ kpM.hom := by
    exact smallEtaleConstantComparison_rebase σ M
  have hDiag : kpM.hom ≫ V.map dT.hom ≫ lamN.hom = dS.hom := by
    exact liftedResidueConstantSheafIso_rebase σ p n
  have hS : (cSZ.inv ≫ L.map keZ.hom) ≫ tZ = kpZ.hom ≫ V.map cTZ.inv :=
    EndpointComparison.source_after_rebase cSZ (L.mapIso keZ) tZ (V.mapIso cTZ) kpZ hZ
  have hT₀ : L.map keM.inv ≫ cSM.hom ≫ dS.hom =
      tM ≫ V.map cTM.hom ≫ V.map dT.hom ≫ lamN.hom :=
    EndpointComparison.target_after_rebase cSM (L.mapIso keM) tM (V.mapIso cTM) kpM
      (V.map dT.hom) lamN.hom dS.hom hM hDiag
  have hT : L.map keM.inv ≫ iS.hom = tM ≫ (V.map iT.hom ≫ lamN.hom) := by
    rw [hiS, hiT, V.map_comp, Category.assoc (V.map cTM.hom) (V.map dT.hom) lamN.hom]
    exact hT₀
  -- Check the forward maps at application, not by identifying arbitrary isomorphisms.
  have forwardS (y : (etaleConstantResidue S p n).H 1) :
      smallEtaleResidueHOneForward S p n y = extOneTransport L cSZ.inv iS.hom y := by rfl
  have forwardT (y : FT.H 1) :
      smallEtaleResidueHOneForward T p n y = extOneTransport L' cTZ.inv iT.hom y := by rfl
  have h₁ :
      extOneTransport L cSZ.inv iS.hom (extOneTransport U keZ.hom keM.inv x) =
        extOneTransport (U ⋙ L) (cSZ.inv ≫ L.map keZ.hom) (L.map keM.inv ≫ iS.hom) x := by
    simpa only [AddMonoidHom.comp_apply] using
      (congrArg (fun (f : _ →+ _) => f x)
        (extOneTransport_comp U L keZ.hom keM.inv cSZ.inv iS.hom))
  have h₂ :
      extOneTransport V kpZ.hom lamN.hom (extOneTransport L' cTZ.inv iT.hom x) =
        extOneTransport (L' ⋙ V) (kpZ.hom ≫ V.map cTZ.inv) (V.map iT.hom ≫ lamN.hom) x := by
    simpa only [AddMonoidHom.comp_apply] using
      (congrArg (fun (f : _ →+ _) => f x)
        (extOneTransport_comp L' V cTZ.inv iT.hom kpZ.hom lamN.hom))
  have hm :
      extOneTransport (U ⋙ L) (cSZ.inv ≫ L.map keZ.hom) (L.map keM.inv ≫ iS.hom) x =
        extOneTransport (L' ⋙ V) (kpZ.hom ≫ V.map cTZ.inv) (V.map iT.hom ≫ lamN.hom) x :=
    extOneTransport_naturality (U ⋙ L) θ hS hT x
  rw [forwardS (etaleResidueHOne_rebase σ p n x), forwardT x]
  exact h₁.trans (hm.trans h₂.symm)

end RC53.EllAdic
