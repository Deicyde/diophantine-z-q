/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add (git blob 430df0ffe491e9a5476a8423d5cdb89dddc0eafb, sha256 3f3f47df8cac8429ba312f1ce426112bb73e8dd7c21f9d10658134c11e9198a5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add
    {R : Type*} [CommRing R] [IsLocalRing R]
    {P P' P'' : Type*} [CommRing P] [CommRing P'] [CommRing P'']
    [Algebra R P] [Algebra R P'] [Algebra R P'']
    (u : P →ₐ[R] P'') (u' : P' →ₐ[R] P'')
    (h0 : ∀ (x : P) (x' : P'), u x = u' x' →
      ∃ r : R, x = algebraMap R P r ∧ x' = algebraMap R P' r)
    (a π : R) (hπ : π ∈ maximalIdeal R)
    (hnil : ∀ c ∈ maximalIdeal R, ∃ n : ℕ, a * π ∣ c ^ n)
    (htor : ∀ y : P'', (∃ (p : P) (p' : P'), (a * π) • y = u p + u' p') →
      ∃ (p : P) (p' : P'), a • y = u p + u' p')
    (e : P) (e' : P')
    (he : e * e - e ∈ (maximalIdeal R).map (algebraMap R P))
    (he' : e' * e' - e' ∈ (maximalIdeal R).map (algebraMap R P'))
    (hu : u e - u' e' ∈ (maximalIdeal R).map (algebraMap R P'')) :
    ∃ r : R, e - algebraMap R P r ∈ (maximalIdeal R).map (algebraMap R P) ∧
      e' - algebraMap R P' r ∈ (maximalIdeal R).map (algebraMap R P') := by
  revert R P P' P'' u u' h0 a π hπ hnil htor e e' he he' hu
  exact @_root_.P2MW.S_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add.solution
