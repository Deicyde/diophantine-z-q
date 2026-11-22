/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral.lean
  Source sha256  : 47ad53a6b3b3fd5711bd49ea48c7a8bcb948bab1d206cc2bcbbfa1cff519d5ae
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 9 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_hasDevissageStep
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsLocallyNoetherian IsProper LocallyOfFiniteType.isLocallyNoetherian QuasiCompact LocallyOfFiniteType Spec IsIntegral Scheme Scheme.IdealSheafData.vanishingIdeal QuasiCompact.compactSpace_of_compactSpace IsSeparated IsNoetherian Scheme.IdealSheafData OModulePresheaf.IdealAnnihilates OModulePresheaf.idealAnnihilates_idealPowQuot OModulePresheaf.pushforward OModulePresheaf.pushforwardUnit Scheme.OrderedAffineCover.isAffineOpen_inter Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.cechFinite_iff OModulePresheaf.hasDevissageStep OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot OModulePresheaf.isCoherent_idealPowQuot OModulePresheaf.isQuasicoherent_idealPowQuot OModulePresheaf.supportedIn_idealPowQuot OModulePresheaf.cechFinite_of_affSES_mid"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "IdealAnnihilates idealAnnihilates_idealPowQuot pushforward pushforwardUnit cochain CechFinite cechFinite_iff IsCoherent IsQuasicoherent SupportedIn hasDevissageStep cechFinite_pushforward_of_isIntegral_of_ih cechFinite_of_forall_cechFinite_idealPowQuot isCoherent_idealPowQuot isQuasicoherent_idealPowQuot supportedIn_idealPowQuot cechFinite_of_affSES_mid"
namespace Driver
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

theorem isNoetherian_of_isProper [IsNoetherianRing R] (π : V ⟶ Spec (.of R)) [IsProper π] : IsNoetherian V := by
  haveI : LocallyOfFiniteType π := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

theorem cechFinite_of_supportedIn_empty (π : V ⟶ Spec (.of R)) [IsSeparated π] (K : V.OrderedAffineCover)
    (F : OModulePresheaf π) {Y : Closeds V} (hY : (Y : Set V) = ∅) (hFs : F.SupportedIn Y) : F.CechFinite K := by
  have hCF : ∀ q, Subsingleton (F.cochain K q) := fun q =>
    ⟨fun a b => funext fun s => @Subsingleton.elim _
      (hFs ⟨_, Scheme.OrderedAffineCover.isAffineOpen_inter π K s⟩ (by rw [hY]; exact Set.inter_empty _)) _ _⟩
  rw [OModulePresheaf.cechFinite_iff]
  refine ⟨?_, fun i => ?_⟩
  · haveI := hCF 0; infer_instance
  · haveI := hCF (i + 1); infer_instance

end AlgebraicGeometry.OModulePresheaf.Driver

open AlgebraicGeometry.OModulePresheaf.Driver in
r2nos_open_dual "AlgebraicGeometry.OModulePresheaf.Driver" in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (K : V.OrderedAffineCover)
    (hInt : ∀ Z₀ : TopologicalSpace.Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
        G.CechFinite K) →
      (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).CechFinite K) :
    ∀ (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π),
      F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → F.CechFinite K := by
  haveI : IsSeparated π := inferInstance
  haveI : IsNoetherian V := isNoetherian_of_isProper π
  haveI : IsLocallyNoetherian V := inferInstance
  intro Y
  induction Y using WellFoundedLT.induction with
  | _ Y ihY =>
  intro F hFc hFq hFs
  by_cases hYne : (Y : Set V).Nonempty
  ·
    have hStep : ∀ F' : OModulePresheaf π, F'.IsCoherent → F'.IsQuasicoherent → F'.SupportedIn Y →
        OModulePresheaf.IdealAnnihilates π (Scheme.IdealSheafData.vanishingIdeal Y) F' → F'.CechFinite K := by
      intro F' hFc' hFq' hFs' hAnn'
      obtain ⟨S⟩ := AlgebraicGeometry.OModulePresheaf.hasDevissageStep π F' hFc' hFq' Y hYne hFs' hAnn'
      have hG₃ : S.G₃.CechFinite K := ihY S.Z₁ S.Z₁_lt S.G₃ S.isCoherent_G₃ S.isQuasicoherent_G₃ S.supportedIn_G₃
      have hCP : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal S.Z₀).subschemeι S.H).CechFinite K := by
        rcases lt_or_eq_of_le S.Z₀_le with hlt | heq
        · exact ihY S.Z₀ hlt _ S.isCoherent_pushforward S.isQuasicoherent_pushforward S.supportedIn_pushforward
        · have ih0 : ∀ Y' < S.Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
              G.CechFinite K := fun Y' hY' => ihY Y' (heq ▸ hY')
          exact AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih π K S.Z₀_nonempty
            S.isIntegral (hInt S.Z₀ S.Z₀_nonempty S.isIntegral ih0) ih0 S.H S.isCoherent_pushforward
            S.isQuasicoherent_pushforward
      exact AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_mid S.ses K hCP hG₃
    exact AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot π K Y F hFc hFq hFs fun k =>
      hStep _ (AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot π _ F k hFc)
        (AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPowQuot π _ F k hFq)
        (AlgebraicGeometry.OModulePresheaf.supportedIn_idealPowQuot π _ F k hFs)
        (AlgebraicGeometry.OModulePresheaf.idealAnnihilates_idealPowQuot π _ F k)
  · exact cechFinite_of_supportedIn_empty π K F (Set.not_nonempty_iff_eq_empty.mp hYne) hFs
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
