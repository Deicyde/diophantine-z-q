import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Compactness.Compact

/-!
# Finite images cyclic implies procyclic

In a compact topological group whose open normal subgroups form a basis of neighbourhoods of
`1`, if every quotient by an open normal subgroup is cyclic then some element generates a
dense subgroup. For each open normal `N` the set of elements generating `H ⧸ N` is a nonempty
union of cosets of `N`, hence clopen; these sets are directed, so by compactness they have a
common point.
-/

noncomputable section
set_option autoImplicit false

namespace WildTameCharacter

open Topology

variable {H : Type*} [Group H]

/-- Elements whose powers meet every coset of `N`. -/
def GenMod (N : Subgroup H) : Set H := {g | ∀ x : H, ∃ k : ℤ, x⁻¹ * g ^ k ∈ N}

theorem genMod_mul_mem {N : Subgroup H} [N.Normal] {g n : H} (hn : n ∈ N) (hg : g ∈ GenMod N) :
    g * n ∈ GenMod N := by
  intro x
  obtain ⟨k, hk⟩ := hg x
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk (g * n) : H ⧸ N) = QuotientGroup.mk g := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, mul_one]
  have h2 : (QuotientGroup.mk (x⁻¹ * (g * n) ^ k) : H ⧸ N) = QuotientGroup.mk (x⁻¹ * g ^ k) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, h1]
  have h3 : (QuotientGroup.mk (x⁻¹ * g ^ k) : H ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).2 hk
  rw [h3] at h2
  exact (QuotientGroup.eq_one_iff _).1 h2

theorem isClosed_genMod [TopologicalSpace H] [IsTopologicalGroup H] (N : Subgroup H) [N.Normal]
    (hN : IsOpen (N : Set H)) :
    IsClosed (GenMod N) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro g hg
  have hopen : IsOpen ((fun y => g⁻¹ * y) ⁻¹' (N : Set H)) := hN.preimage (continuous_const.mul continuous_id)
  have hmem : g ∈ (fun y => g⁻¹ * y) ⁻¹' (N : Set H) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact N.one_mem
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  intro y hy hyC
  apply hg
  have hy' : g⁻¹ * y ∈ N := hy
  have e : y * (g⁻¹ * y)⁻¹ = g := by group
  rw [← e]
  exact genMod_mul_mem (N.inv_mem hy') hyC

theorem genMod_nonempty (N : Subgroup H) [N.Normal] (hc : IsCyclic (H ⧸ N)) :
    (GenMod N).Nonempty := by
  obtain ⟨a, ha⟩ := hc.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  refine ⟨g, fun x => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha (QuotientGroup.mk x))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_zpow] at hk
  exact QuotientGroup.eq.mp hk.symm

theorem genMod_anti {N M : Subgroup H} (h : N ≤ M) : GenMod N ⊆ GenMod M := by
  intro g hg x
  obtain ⟨k, hk⟩ := hg x
  exact ⟨k, h hk⟩

/-- **Finite images cyclic ⇒ procyclic.** -/
theorem exists_dense_zpowers [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (hbasis : ∀ U ∈ 𝓝 (1 : H), ∃ N : Subgroup H, N.Normal ∧ IsOpen (N : Set H) ∧ (N : Set H) ⊆ U)
    (hcyc : ∀ (N : Subgroup H) [N.Normal], IsOpen (N : Set H) → IsCyclic (H ⧸ N)) :
    ∃ g : H, Dense (Subgroup.zpowers g : Set H) := by
  let ι := {N : Subgroup H // N.Normal ∧ IsOpen (N : Set H)}
  have : Nonempty ι := ⟨⟨⊤, Subgroup.normal_top, by simp⟩⟩
  let t : ι → Set H := fun N => @GenMod H _ N.1
  have htd : Directed (· ⊇ ·) t := by
    intro N M
    have := N.2.1
    have := M.2.1
    refine ⟨⟨N.1 ⊓ M.1, Subgroup.normal_inf_normal N.1 M.1, ?_⟩, ?_, ?_⟩
    · rw [Subgroup.coe_inf]
      exact N.2.2.inter M.2.2
    · exact genMod_anti inf_le_left
    · exact genMod_anti inf_le_right
  have htn : ∀ N : ι, (t N).Nonempty := fun N => by
    have := N.2.1
    exact genMod_nonempty N.1 (hcyc N.1 N.2.2)
  have htcl : ∀ N : ι, IsClosed (t N) := fun N => by
    have := N.2.1
    exact isClosed_genMod N.1 N.2.2
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun N => (htcl N).isCompact) htcl
  refine ⟨g, fun x => ?_⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  have hU1 : (fun y => x * y) ⁻¹' U ∈ 𝓝 (1 : H) :=
    ((continuous_const.mul continuous_id).continuousAt (x := (1 : H))).preimage_mem_nhds
      (by simpa using hU)
  obtain ⟨N, hNn, hNo, hNU⟩ := hbasis _ hU1
  have hgN : g ∈ t ⟨N, hNn, hNo⟩ := Set.mem_iInter.mp hg ⟨N, hNn, hNo⟩
  obtain ⟨k, hk⟩ := hgN x
  refine ⟨g ^ k, ?_, Subgroup.zpow_mem_zpowers g k⟩
  have h1 := hNU hk
  simp only [Set.mem_preimage, mul_inv_cancel_left] at h1
  exact h1

end WildTameCharacter
