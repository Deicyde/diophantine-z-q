/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.lean
  Licence        : Apache License, Version 2.0 (see Contrib/CloudB3W12FiniteQuotient/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(port to Lean v4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-16).
The changes are mechanical only; the statement is unchanged:
  * `import P2M.Util` removed; `import P2M.Sol.S_…` retargeted to
    `ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_…`.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`
    (so the theorem is `ZInQ.Contrib.CloudW03NeronSurj.FLT.RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation`).
  * proof `by p2m_exact_reverting @_root_.P2MW.S_….solution` replaced by the direct term
    `P2MW.S_….solution s t hs hs' ht ht' hgen hequiv hinj hinv` (the solution in the port namespace).
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

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
        (CommRingCat.ofHom s) (CommRingCat.ofHom t) :=
  P2MW.S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.solution
    s t hs hs' ht ht' hgen hequiv hinj hinv

end ZInQ.Contrib.CloudW03NeronSurj.FLT
