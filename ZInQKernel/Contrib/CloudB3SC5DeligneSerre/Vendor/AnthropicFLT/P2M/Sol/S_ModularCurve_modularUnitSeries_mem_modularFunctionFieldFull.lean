/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull (git blob fc185fc5cda9413f010a6a2314197388435ecb94, sha256 786c5f97a4445bd0118add42a16224af69140de63b09c1679cbe2e1c97e0f73c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ModularUnit
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull

set_option autoImplicit false

theorem solution (N : ℕ) [NeZero N] : ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionFieldFull N := by
  suffices H : ∀ n : ℕ, ∀ _ : NeZero n,
      ModularCurve.modularUnitSeries n ∈ ModularCurve.modularFunctionFieldFull n from
    H N ‹NeZero N›
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hNZ
    haveI := hNZ
    have hn : n ≠ 0 := NeZero.ne n
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [ModularCurve.modularUnitSeries_one]
      exact one_mem _
    · obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨M, rfl⟩ := hdvd
      have hM : M ≠ 0 := by rintro rfl; exact hn (mul_zero p)
      have hp0 : p ≠ 0 := hp.ne_zero
      haveI : NeZero p := ⟨hp0⟩
      haveI : NeZero M := ⟨hM⟩
      haveI : NeZero (p * M) := ⟨mul_ne_zero hp0 hM⟩
      haveI : Fact p.Prime := ⟨hp⟩
      rw [ModularCurve.modularUnitSeries_mul p M]
      refine mul_mem ?_ ?_
      · exact ModularCurve.full_degeneracy_le (dvd_mul_right p M)
          (ModularCurve.modularFunctionField_le_full p
            (ModularCurve.modularUnitSeries_mem_modularFunctionField p))
      · have hMlt : M < p * M :=
          (lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hM)).mpr hp.one_lt
        have hmem := ih M hMlt ⟨hM⟩
        have h2 : ModularCurve.qExpandₐ p (ModularCurve.modularUnitSeries M)
            ∈ (ModularCurve.modularFunctionFieldFull M).map (ModularCurve.qExpandₐ p) :=
          ⟨_, hmem, rfl⟩
        have h3 := ModularCurve.full_degeneracy_map_le M p h2
        rw [ModularCurve.qExpandₐ_apply] at h3
        exact ModularCurve.full_degeneracy_le (dvd_of_eq (mul_comm M p)) h3
