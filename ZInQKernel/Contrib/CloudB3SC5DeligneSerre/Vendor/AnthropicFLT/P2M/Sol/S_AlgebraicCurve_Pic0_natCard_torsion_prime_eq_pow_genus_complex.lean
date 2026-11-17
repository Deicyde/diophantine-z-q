/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus_complex (git blob 9ada7e041e911564de73ea4c0d1f5fbd073c1669, sha256 8b50d3206d53e770bab9b38e690ca5fb5a88b12778ebfb89049478b142034821).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus_complex

open AlgebraicCurve

theorem solution (F : Type*) [Field F]
    [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧ FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    (p : ℕ) [Fact p.Prime] :
    Nat.card (Pic0.torsion ℂ F p) = p ^ (2 * genus ℂ F) := by

  obtain ⟨L, hLfree, hLfin, hLrank, ⟨e⟩⟩ :=
    AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_complex F hfg
  haveI : Module.Free ℤ L := hLfree
  haveI : Module.Finite ℤ L := hLfin
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  have hcount : Nat.card (Submodule.torsionBy ℤ ((Fin (genus ℂ F) → ℂ) ⧸ L) (p : ℤ))
      = p ^ (2 * genus ℂ F) := by
    rw [Submodule.natCard_torsionBy_quotient_eq_pow_finrank (K := ℂ) L p hp, hLrank]

  have htors : ∀ x : Pic0 ℂ F, (p : ℤ) • x = 0 ↔ (p : ℤ) • e x = 0 := by
    intro x
    constructor
    · intro h; rw [← map_zsmul, h, map_zero]
    · intro h
      have := e.injective (a₁ := (p : ℤ) • x) (a₂ := 0)
      simp only [map_zsmul, map_zero] at this
      exact this h

  have hequiv : Nat.card (Pic0.torsion ℂ F p)
      = Nat.card (Submodule.torsionBy ℤ ((Fin (genus ℂ F) → ℂ) ⧸ L) (p : ℤ)) := by
    apply Nat.card_eq_of_bijective
      (f := fun x => ⟨e x.1, by
        have := x.2
        rw [Pic0.mem_torsion] at this
        simpa [Submodule.mem_torsionBy_iff] using (htors x.1).mp this⟩)
    constructor
    · intro a b hab
      ext
      exact e.injective (Subtype.ext_iff.mp hab)
    · intro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := e.surjective y
      refine ⟨⟨x, ?_⟩, ?_⟩
      · rw [Pic0.mem_torsion]
        exact (htors x).mpr (by simpa [Submodule.mem_torsionBy_iff, hx] using hy)
      · simp [hx]
  rw [hequiv, hcount]
