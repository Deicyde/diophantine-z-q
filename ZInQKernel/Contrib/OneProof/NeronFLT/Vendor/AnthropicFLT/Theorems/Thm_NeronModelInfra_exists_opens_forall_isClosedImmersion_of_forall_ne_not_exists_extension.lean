/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType open NeronModelInfra

universe u

theorem NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ V : ∀ i, (Y i).Opens,
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsIso (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1) ∧
      ∀ i j, i ≠ j →
        ∀ δ : pullback
              (schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i)).1
              (schemeHomOverComp (genericFibreRestrict R K (f j) ((V j).ι ≫ f j) ⟨(V j).ι, rfl⟩) (e j)).1 ⟶
            pullback ((V i).ι ≫ f i) ((V j).ι ≫ f j),
          δ ≫ pullback.fst ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.fst _ _ ≫ pullback.fst ((V i).ι ≫ f i) (specGenericFibreInclusion R K) →
          δ ≫ pullback.snd ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.snd _ _ ≫ pullback.fst ((V j).ι ≫ f j) (specGenericFibreInclusion R K) →
          IsClosedImmersion δ := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension.solution
