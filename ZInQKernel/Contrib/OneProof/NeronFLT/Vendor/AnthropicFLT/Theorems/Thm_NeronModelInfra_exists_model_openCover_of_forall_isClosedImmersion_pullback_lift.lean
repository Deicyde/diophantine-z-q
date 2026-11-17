/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i, IsIso (e i).1)
    (hdiag : ∀ i j, i ≠ j → ∀ δ : pullback (e i).1 (e j).1 ⟶ pullback (f i) (f j),
      δ ≫ pullback.fst (f i) (f j) = pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K) →
      δ ≫ pullback.snd (f i) (f j) = pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) (specGenericFibreInclusion R K) →
      IsClosedImmersion δ) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (j : ∀ i, SchemeHomOver (f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g (f i) (j i)).1 ≫ eX.1 = (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift.solution
