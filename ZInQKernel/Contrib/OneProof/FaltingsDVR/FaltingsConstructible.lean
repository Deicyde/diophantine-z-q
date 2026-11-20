import Mathlib.Topology.Constructible
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.NoetherianSpace

/-! Dense constructible subsets of nonempty Noetherian spaces contain nonempty opens. -/

open Set TopologicalSpace Topology

namespace ZInQ.FaltingsRestate

private lemma nowhereDense_of_locallyClosed_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsLocallyClosed s) (h : interior s = ∅) : IsNowhereDense s := by
  show interior (closure s) = ∅
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨y, hy, hys⟩ :=
    mem_closure_iff.mp (interior_subset hx) _ isOpen_interior hx
  obtain ⟨U, hU, heq⟩ := (isLocallyClosed_tfae s |>.out 1 5).mp hs
  have hyU : y ∈ U := (show y ∈ U ∩ closure s by rwa [← heq]).1
  have hm : U ∩ interior (closure s) ⊆ s := by
    intro z hz
    rw [heq]
    exact ⟨hz.1, interior_subset hz.2⟩
  have he : y ∈ interior s :=
    interior_maximal hm (hU.inter isOpen_interior) ⟨hyU, hy⟩
  rw [h] at he
  exact he

private theorem IsConstructible.nowhereDense_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] {s : Set X}
    (hs : IsConstructible s) (h : interior s = ∅) : IsNowhereDense s := by
  let b : Opens X → Set X := fun U => U
  have hb : IsTopologicalBasis (Set.range b) := by
    convert isTopologicalBasis_opens (α := X)
    exact Set.ext fun u => ⟨fun ⟨U, hu⟩ => hu ▸ U.2, fun hu => ⟨⟨u, hu⟩, rfl⟩⟩
  refine IsConstructible.induction_of_isTopologicalBasis
    (P := fun s _ => interior s = ∅ → IsNowhereDense s)
    b hb (fun U => NoetherianSpace.isCompact _) ?_ ?_ s hs h
  · intro V t _ huv
    apply nowhereDense_of_locallyClosed_of_interior_eq_empty _ huv
    exact ⟨b V, (⋃ j ∈ t, b j)ᶜ, V.2,
      (isOpen_biUnion fun U _ => U.2).isClosed_compl, rfl⟩
  · intro u _ v _ hu hv he
    refine (hu ?_).union (hv ?_)
    · exact Set.eq_empty_of_subset_empty (he ▸ interior_mono Set.subset_union_left)
    · exact Set.eq_empty_of_subset_empty (he ▸ interior_mono Set.subset_union_right)

/-- A dense constructible subset of a nonempty Noetherian space has nonempty interior. -/
theorem nonempty_interior_of_dense_constructible
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [Nonempty X]
    {s : Set X} (hs : IsConstructible s) (hd : Dense s) : (interior s).Nonempty := by
  by_contra h
  have hn := IsConstructible.nowhereDense_of_interior_eq_empty hs (Set.not_nonempty_iff_eq_empty.mp h)
  change interior (closure s) = ∅ at hn
  rw [hd.closure_eq, interior_univ] at hn
  exact Set.univ_nonempty.ne_empty hn

end ZInQ.FaltingsRestate
