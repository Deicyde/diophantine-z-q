/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_smul_mem_of_transcendental_residue (git blob 9049bb9956f57d742aee5a972db4cf79de47845d, sha256 5d1d3e3e207752be4265d901c38c50dd22ec9db8a5e867efab6ac1c8fa94f76c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_smul_mem_of_transcendental_residue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_smul_mem_of_transcendental_residue
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (O : ValuationSubring F) (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (ρ : O →+* Fbar) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ a : A, ρ ⟨algebraMap L F a, (hO a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
    (f : F) (hf : f ∈ O)
    (htr : Transcendental (IsLocalRing.ResidueField A) (ρ ⟨f, hf⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (h : F) (hh : h ≠ 0) :
    ∃ c : L, ∃ hc : c • h ∈ O, ρ ⟨c • h, hc⟩ ≠ 0 := by
  revert L A F O hO Fbar ρ hker hρ f hf htr h hh
  exact @_root_.P2MW.S_ValuationSubring_exists_smul_mem_of_transcendental_residue.solution
