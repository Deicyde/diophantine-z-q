/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory

universe u

theorem RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]
    (s t : A →+* B)
    (hs : letI := s.toAlgebra; Module.Finite A B) (hs' : letI := s.toAlgebra; Module.Projective A B)
    (ht : letI := t.toAlgebra; Module.Finite A B) (ht' : letI := t.toAlgebra; Module.Projective A B)
    (hgen : s.range ⊔ t.range = ⊤)
    (hequiv : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : A →+* T => ∃ φ : B →+* T, φ.comp s = x ∧ φ.comp t = y)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀ a : A, s a = t a ↔ a ∈ Set.range (algebraMap C A)) :
    Module.Finite C A ∧ Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom s) (CommRingCat.ofHom t) := by p2m_exact_reverting @_root_.P2MW.S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.solution
