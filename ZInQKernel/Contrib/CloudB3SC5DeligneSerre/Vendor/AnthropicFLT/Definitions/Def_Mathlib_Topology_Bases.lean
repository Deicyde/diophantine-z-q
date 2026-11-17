/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Mathlib_Topology_Bases (git blob 0a0f162c947cce45653a7762a500392803c0bb36, sha256 1e44281c9989d7177e768c262095fe976ed86cc6c49710c409f0c2b278cede65).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

section

lemma TopologicalSpace.secondCountableTopology_of_countable_cover' {α : Type*}
    [TopologicalSpace α] {ι : Sort*} [Countable ι] {U : ι → Type*} [∀ i, TopologicalSpace (U i)]
    [∀ (i : ι), SecondCountableTopology (U i)]
    (f : ∀ i, U i → α) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hc : ∀ a, ∃ (i : ι) (u : U i), f i u = a) : SecondCountableTopology α :=
  let V i := Set.range (f i)
  have (i : ι) : SecondCountableTopology (V i) :=
    (hf i).toHomeomorph.symm.secondCountableTopology
  have Vo (i : ι) : IsOpen (V i) := (hf i).isOpen_range
  have hV : ⋃ i, V i = Set.univ := Set.eq_univ_of_forall fun a =>
    (hc a).elim fun i hi => Set.mem_iUnion_of_mem i (Set.mem_range.2 hi)
  secondCountableTopology_of_countable_cover Vo hV
