/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis

universe u v w u'

open CategoryTheory Opposite TopologicalSpace

theorem solution {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G : TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ := by
  haveI := TopCat.Opens.coverDense_inducedFunctor hB
  haveI : IsIso (Functor.whiskerLeft (inducedFunctor B).op φ.1) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro i
    exact h i.unop
  exact Functor.IsCoverDense.iso_of_restrict_iso φ this
