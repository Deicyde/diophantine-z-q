/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 small obligations: general Noetherian-space facts about maximal irreducible subsets of
a closed set (Mathlib only). SOURCE ONLY, UNCOMPILED. Native HELD. Default options.

* `exists_maximal_irreducible_of_subset`: in a Noetherian space every irreducible subset of a
  closed `S` lies in an irreducible subset of `S` that is maximal for inclusion.
* `finite_maximal_irreducible`: there are finitely many such maximal subsets.
Both from Mathlib `NoetherianSpace.exists_finite_set_isClosed_irreducible` (a closed set is a
finite union of irreducible closed sets) and `isIrreducible_iff_sUnion_isClosed`.
-/
import Mathlib

set_option autoImplicit false

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

open TopologicalSpace

variable {T : Type*} [TopologicalSpace T] [NoetherianSpace T]

/-- An irreducible subset of a finite union of closed sets lies in one of them. -/
theorem exists_mem_subset_of_isIrreducible {F : Set (Set T)} (hF : F.Finite)
    (hcl : ∀ t ∈ F, IsClosed t) {Y : Set T} (hY : IsIrreducible Y) (hYF : Y ⊆ ⋃₀ F) :
    ∃ t ∈ F, Y ⊆ t := by
  classical
  have hcov : Y ⊆ ⋃₀ ((hF.toFinset : Finset (Set T)) : Set (Set T)) := by
    rw [Set.Finite.coe_toFinset]
    exact hYF
  obtain ⟨t, ht, hYt⟩ := (isIrreducible_iff_sUnion_isClosed.1 hY) hF.toFinset
    (fun z hz => hcl z ((Set.Finite.mem_toFinset hF).1 hz)) hcov
  exact ⟨t, (Set.Finite.mem_toFinset hF).1 ht, hYt⟩

/-- Every irreducible subset of a closed set lies in a maximal irreducible subset of it. -/
theorem exists_maximal_irreducible_of_subset {S : Set T} (hS : IsClosed S) {E : Set T}
    (hES : E ⊆ S) (hE : IsIrreducible E) :
    ∃ G, Maximal (fun Y : Set T => Y ⊆ S ∧ IsIrreducible Y) G ∧ E ⊆ G := by
  obtain ⟨F, hFfin, hFcl, hFirr, hSF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have hmem : ∀ Y : Set T, IsIrreducible Y → Y ⊆ S → ∃ t ∈ F, Y ⊆ t := fun Y hY hYS =>
    exists_mem_subset_of_isIrreducible hFfin hFcl hY (hSF ▸ hYS)
  obtain ⟨t₀, ht₀F, hEt₀⟩ := hmem E hE hES
  let F' : Set (Set T) := {t | t ∈ F ∧ E ⊆ t}
  have hF'fin : F'.Finite := hFfin.subset fun t ht => ht.1
  obtain ⟨G, ht₀G, hGmax⟩ := hF'fin.exists_le_maximal (show t₀ ∈ F' from ⟨ht₀F, hEt₀⟩)
  have hGF : G ∈ F := hGmax.1.1
  have hGS : G ⊆ S := by
    rw [hSF]
    exact Set.subset_sUnion_of_mem hGF
  refine ⟨G, ⟨⟨hGS, hFirr G hGF⟩, fun Y hY hGY => ?_⟩, hEt₀.trans ht₀G⟩
  obtain ⟨t, htF, hYt⟩ := hmem Y hY.2 hY.1
  have htF' : t ∈ F' := ⟨htF, (hEt₀.trans ht₀G).trans (hGY.trans hYt)⟩
  exact hYt.trans (hGmax.2 htF' (hGY.trans hYt))

/-- There are finitely many maximal irreducible subsets of a closed set. -/
theorem finite_maximal_irreducible {S : Set T} (hS : IsClosed S) :
    {C : Set T | Maximal (fun Y : Set T => Y ⊆ S ∧ IsIrreducible Y) C}.Finite := by
  obtain ⟨F, hFfin, hFcl, hFirr, hSF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  refine hFfin.subset fun C hC => ?_
  obtain ⟨⟨hCS, hCirr⟩, hCmax⟩ := hC
  obtain ⟨t, htF, hCt⟩ := exists_mem_subset_of_isIrreducible hFfin hFcl hCirr (hSF ▸ hCS)
  have htS : t ⊆ S := by
    rw [hSF]
    exact Set.subset_sUnion_of_mem htF
  have htC : t ⊆ C := hCmax ⟨htS, hFirr t htF⟩ hCt
  rwa [show C = t from Set.Subset.antisymm hCt htC]

end ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small
