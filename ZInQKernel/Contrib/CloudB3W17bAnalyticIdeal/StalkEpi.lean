import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Stalks send epimorphisms of sheaves of modules to surjections

A consequence of the canonical stalkwise exactness of short complexes of sheaves of modules.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace ZInQ.Contrib.CloudB3W17bAnalyticIdeal.Sh

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **Stalks (as abelian groups) send epimorphisms of sheaves of modules to surjections.** -/
theorem surjective_stalk_of_epi {M N : SheafOfModules.{u} R} (φ : M ⟶ N) [Epi φ] (x : X) :
    Function.Surjective ((SheafOfModules.stalkFunctorAddCommGrp x).map φ) := by
  let S := ShortComplex.mk φ (0 : N ⟶ N) (by simp)
  have hS : S.Exact := (S.exact_iff_epi rfl).mpr (inferInstanceAs (Epi φ))
  have h := SheafOfModules.stalk_exact_of_exact S hS x
  rw [ShortComplex.ab_exact_iff] at h
  intro t
  obtain ⟨t₁, ht₁⟩ := h t (by
    change (SheafOfModules.stalkFunctorAddCommGrp x).map (0 : N ⟶ N) t = 0
    rw [Functor.map_zero]
    rfl)
  exact ⟨t₁, ht₁⟩

end ZInQ.Contrib.CloudB3W17bAnalyticIdeal.Sh
