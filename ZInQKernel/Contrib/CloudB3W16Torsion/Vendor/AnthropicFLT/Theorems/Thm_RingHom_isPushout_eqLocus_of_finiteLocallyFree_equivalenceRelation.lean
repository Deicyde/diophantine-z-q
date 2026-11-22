/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation

set_option backward.isDefEq.respectTransparency false

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
