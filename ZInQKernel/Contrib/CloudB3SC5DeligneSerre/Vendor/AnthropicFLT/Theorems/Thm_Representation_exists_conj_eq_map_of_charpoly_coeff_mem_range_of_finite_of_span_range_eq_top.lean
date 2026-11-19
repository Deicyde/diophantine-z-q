/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top (git blob aa8462b0d9531d1441ba67981ecde05dc951d486, sha256 bcbc13d777bb94dd094b5766447dac21b82e4ffdde20f4fa56d860fec7557313).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v
theorem Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top
    {K : Type v} [Field K] {L : Type u} [Field L] [Algebra K L] [Finite L]
    {n : Type} [DecidableEq n] [Fintype n] [Nonempty n] {G : Type u} [Group G]
    (φ : G →* GL n L)
    (hspan : Submodule.span L (Set.range fun g => (φ g : Matrix n n L)) = ⊤)
    (hcoeff : ∀ g i, (φ g : Matrix n n L).charpoly.coeff i ∈ (algebraMap K L).range) :
    ∃ ρ : G →* GL n ((algebraMap K L).range), ∃ Q : GL n L,
      ∀ g, (Q⁻¹ * φ g * Q : Matrix n n L)
        = (ρ g : Matrix n n ((algebraMap K L).range)).map ((algebraMap K L).range.subtype) := by
  revert K L n G φ hspan hcoeff
  exact @_root_.P2MW.S_Representation_exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top.solution
