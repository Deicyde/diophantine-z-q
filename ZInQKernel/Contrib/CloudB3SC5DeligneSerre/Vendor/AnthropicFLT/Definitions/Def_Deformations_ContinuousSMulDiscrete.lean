/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Deformations_ContinuousSMulDiscrete (git blob 8c8d8589606ca3e861ede7508386c856102425f8, sha256 ae224798676c5da436764017e1eaa8c2075d09aa2c4e50491f10a01f6599d7ad).
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

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }

lemma continuousSMulDiscrete_iff [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMulDiscrete G M ↔ ContinuousSMul G M := by
  refine ⟨fun H ↦ ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  · convert_to IsOpen (⋃ x, { g : G | g • x = y } ×ˢ {x})
    · ext; simp
    · exact isOpen_iUnion fun _ ↦
        .prod (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _) (isOpen_discrete _)
  · exact ((isOpen_discrete {y}).preimage continuous_smul).preimage (Continuous.prodMk_left x)

instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]

lemma ContinuousSMulDiscrete.of_continuousSMul [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul G M] : ContinuousSMulDiscrete G M := by
  rwa [continuousSMulDiscrete_iff]

lemma continuousSMulDiscrete_iff_isOpen_stabilizer {G M : Type*} [TopologicalSpace G]
    [Group G] [ContinuousMul G] [MulAction G M] :
    ContinuousSMulDiscrete G M ↔ ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun H x ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ _ _, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain h | ⟨g, rfl⟩ := Set.eq_empty_or_nonempty {g : G | g • x = y}
  · exact h ▸ isOpen_empty
  · convert (H x).preimage (Homeomorph.mulLeft g⁻¹).continuous using 1
    ext g'
    simp [mul_smul, inv_smul_eq_iff]

lemma ContinuousSMulDiscrete.isOpen_stabilizer (G : Type*) {M : Type*} [TopologicalSpace G]
    [Group G] [MulAction G M] [ContinuousSMulDiscrete G M] (x : M) :
      IsOpen (MulAction.stabilizer G x : Set G) := ContinuousSMulDiscrete.isOpen_smul_eq _ _ _

end
