/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite (git blob f9bf05c1d473e6f8af464c95c42329dd7d7d0aea, sha256 55765e40bc99545b2a968bd3375554f26aefd74b4a64b909ab48ae82006933fe).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite

open Submodule

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : M, (∃ c : R, c ≠ 0 ∧ c • m = 0) → a • m = 0 := by
  classical

  set T : Submodule R M := torsion R M with hT
  haveI : Module.Finite R (M ⧸ T) := inferInstance
  haveI : Module.Flat R (M ⧸ T) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (Submodule.QuotientTorsion.torsion_eq_bot)
  haveI : Module.Free R (M ⧸ T) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Projective R (M ⧸ T) := Module.Projective.of_free

  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ (LinearMap.id : M ⧸ T →ₗ[R] M ⧸ T)
    (Submodule.mkQ_surjective T)

  set φ : M →ₗ[R] M := LinearMap.id - s ∘ₗ T.mkQ with hφ
  have hrange : LinearMap.range φ = T := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      have : T.mkQ (φ m) = 0 := by
        have h1 : T.mkQ (s (T.mkQ m)) = T.mkQ m := by
          have := LinearMap.congr_fun hs (T.mkQ m)
          simpa using this
        simp only [Submodule.mkQ_apply] at h1
        simp only [hφ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_sub, h1, sub_self]
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this
    · intro t ht
      refine ⟨t, ?_⟩
      have : T.mkQ t = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ht
      simp [hφ, this]
  haveI hTfin : Module.Finite R T := by
    rw [← hrange]
    exact Module.Finite.range φ

  have hTtors : Module.IsTorsion R T := by
    intro t
    obtain ⟨c, hc⟩ := (mem_torsion_iff (t : M)).mp t.2
    exact ⟨c, Subtype.ext (by simpa using hc)⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hTtors
  refine ⟨a, nonZeroDivisors.ne_zero ha0, fun m hm => ?_⟩
  obtain ⟨c, hc0, hcm⟩ := hm
  have hmT : m ∈ T := (mem_torsion_iff m).mpr ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩, hcm⟩
  have := Submodule.mem_annihilator.mp ha ⟨m, hmT⟩ Submodule.mem_top
  simpa using congrArg Subtype.val this
