/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd (git blob 6184fd95782b90c01349d7d24f118a3f5cf18561, sha256 0ba3250103866714cfd6d653fc71a44c050ec08c4e23c10637b2285bd59f47e3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd

set_option autoImplicit false
open scoped nonZeroDivisors

theorem solution
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Finite (ClassGroup R)] :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum R), ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰,
      ClassGroup.mk0 I = c ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S := by
  classical
  choose I hI using (ClassGroup.mk0_surjective (R := R))
  have hfin : (⋃ c : ClassGroup R, {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ (I c : Ideal R)}).Finite :=
    Set.finite_iUnion fun c => Ideal.finite_factors (nonZeroDivisors.coe_ne_zero (I c))
  refine ⟨hfin.toFinset, fun c => ⟨I c, hI c, fun v hv => ?_⟩⟩
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_iUnion.2 ⟨c, hv⟩
