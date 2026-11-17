/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd (git blob 21fc76854d17650111d1e181967c2423ab2fd16c, sha256 00b3a1c1ca8630f242df151b9f290b905ee7d368ec218bd3f90081f535b1ae77).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open scoped nonZeroDivisors
theorem ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Finite (ClassGroup R)] :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum R), ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰,
      ClassGroup.mk0 I = c ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S := by
  revert R
  exact @_root_.P2MW.S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.solution
