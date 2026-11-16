/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

-- [port] was: p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat"
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry hiding isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat

theorem AlgebraicGeometry.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
    {k : Type u} [CommRing k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type u) [CommRing A] [Algebra k A] [Module.FaithfullyFlat k A]
    (hA : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom) :
Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat.solution
