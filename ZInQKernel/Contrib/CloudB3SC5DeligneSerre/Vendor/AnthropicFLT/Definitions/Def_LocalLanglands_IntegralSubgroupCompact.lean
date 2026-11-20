/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_LocalLanglands_IntegralSubgroupCompact (git blob 4db854fbf64eb12b6824a6e2211c43a9d267c645, sha256 1e1a165960b770673a924763a9a3934b42df37ce7e86783deaf8f00c86ea9ef4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace FLT.SpectralSide

instance instCompactSpaceMatrix {m n R : Type*} [TopologicalSpace R] [CompactSpace R] :
    CompactSpace (Matrix m n R) :=
  inferInstanceAs <| CompactSpace (m → n → R)

theorem gl2_compactSpace (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R] :
    CompactSpace (GL (Fin 2) R) := inferInstance

theorem isCompact_coe_integralSubgroup (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R]
    (K : Type*) [Field K] [Algebra R K] [TopologicalSpace K]
    (hcont : Continuous (algebraMap R K)) :
    IsCompact ((LocalGL2.integralSubgroup R K : Set (GL (Fin 2) K))) := by
  haveI : CompactSpace (GL (Fin 2) R) := gl2_compactSpace R
  have hmapcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)) := by
    unfold Matrix.GeneralLinearGroup.map
    refine Continuous.units_map _ ?_
    exact continuous_matrix fun i j =>
      hcont.comp ((continuous_apply j).comp (continuous_apply i))
  have hr : IsCompact
      (Set.range ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))) :=
    isCompact_range hmapcont
  simpa [LocalGL2.integralSubgroup, MonoidHom.coe_range] using hr

theorem isCompact_coe_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    IsCompact ((LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] : Set (GL (Fin 2) ℚ_[p]))) :=
  isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val

theorem compactSpace_integralSubgroup_padic (p : ℕ) [Fact p.Prime] :
    CompactSpace (LocalGL2.integralSubgroup ℤ_[p] ℚ_[p]) :=
  isCompact_iff_compactSpace.mp (isCompact_coe_integralSubgroup_padic p)

end FLT.SpectralSide
