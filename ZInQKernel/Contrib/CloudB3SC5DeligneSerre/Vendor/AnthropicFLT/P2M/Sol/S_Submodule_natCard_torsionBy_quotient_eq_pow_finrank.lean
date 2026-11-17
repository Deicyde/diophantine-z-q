/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank (git blob 0c8326b3f6e40ca9a6b400b25f8f9fd797fa7128, sha256 4ec5149f5080ada861c87561869f9e974c5e04d8f60bc7d2b1105b67c540b21d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Submodule
end Submodule
namespace P2MW.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.Submodule
end P2MW.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.Submodule

namespace P2MW.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank

namespace Submodule
export _root_.Submodule (quotEquivOfEq coe_smul mk torsion Quotient.mk map_smul' Quotient.mk_surjective map Quotient.mk_eq_zero torsionBy Quotient.mk_add module mk_eq_zero coe_add ext mem_torsionBy_iff)
namespace LatticeQuotientTorsion
open _root_.Submodule

open _root_.Submodule
open _root_.P2MW.S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank.Submodule

universe u v

variable {K : Type u} [DivisionRing K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

noncomputable def divN (n : ℕ) : V →+ V :=
  DistribSMul.toAddMonoidHom V ((n : K)⁻¹)

theorem natCast_smul_divN {n : ℕ} (hn : n ≠ 0) (v : V) :
    (n : ℤ) • divN (K := K) n v = v := by
  have hK : (n : K) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hK, one_smul]

theorem divN_natCast_smul {n : ℕ} (hn : n ≠ 0) (v : V) :
    divN (K := K) n ((n : ℤ) • v) = v := by
  have hK : (n : K) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hK, one_smul]

variable (L : Submodule ℤ V)

noncomputable def latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    L →ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) where
  toFun w := ⟨Submodule.Quotient.mk (divN (K := K) n (w : V)), by
    rw [mem_torsionBy_iff]
    change (Submodule.Quotient.mk ((n : ℤ) • divN (K := K) n (w : V)) : V ⧸ L) = 0
    rw [natCast_smul_divN (K := K) hn]
    exact (Submodule.Quotient.mk_eq_zero L).mpr w.2⟩
  map_add' a b := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN (K := K) n ((a + b : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (divN (K := K) n (a : V))
        + Submodule.Quotient.mk (divN (K := K) n (b : V))
    rw [Submodule.coe_add, map_add, Submodule.Quotient.mk_add]
  map_smul' m a := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN (K := K) n ((m • a : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (m • divN (K := K) n (a : V))
    rw [Submodule.coe_smul, map_zsmul]

theorem coe_latticeDivQuot {n : ℕ} (hn : n ≠ 0) (w : L) :
    ((latticeDivQuot (K := K) L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) : V ⧸ L)
      = Submodule.Quotient.mk (divN (K := K) n (w : V)) := rfl

theorem latticeDivQuot_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (latticeDivQuot (K := K) L hn) := by
  rintro ⟨x, hx⟩
  rw [mem_torsionBy_iff] at hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  have hvL : (n : ℤ) • v ∈ L := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨⟨(n : ℤ) • v, hvL⟩, Subtype.ext ?_⟩
  rw [coe_latticeDivQuot]
  change (Submodule.Quotient.mk (divN (K := K) n ((n : ℤ) • v)) : V ⧸ L)
      = Submodule.Quotient.mk v
  rw [divN_natCast_smul (K := K) hn]

theorem ker_latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    LinearMap.ker (latticeDivQuot (K := K) L hn)
      = LinearMap.range (LinearMap.lsmul ℤ L (n : ℤ)) := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hker
    have hcoe : ((latticeDivQuot (K := K) L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) : V ⧸ L)
        = 0 := by
      rw [hker]; rfl
    rw [coe_latticeDivQuot, Submodule.Quotient.mk_eq_zero] at hcoe
    refine ⟨⟨divN (K := K) n (w : V), hcoe⟩, ?_⟩
    apply Subtype.ext
    change (n : ℤ) • divN (K := K) n (w : V) = (w : V)
    exact natCast_smul_divN (K := K) hn (w : V)
  · rintro ⟨μ, rfl⟩
    apply Subtype.ext
    rw [coe_latticeDivQuot, LinearMap.lsmul_apply]
    change (Submodule.Quotient.mk (divN (K := K) n ((n : ℤ) • (μ : V))) : V ⧸ L) = 0
    rw [divN_natCast_smul (K := K) hn, Submodule.Quotient.mk_eq_zero]
    exact μ.2

noncomputable def latticeQuotTorsionEquiv {n : ℕ} (hn : n ≠ 0) :
    ModN L n ≃ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (ker_latticeDivQuot (K := K) L hn).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (latticeDivQuot_surjective (K := K) L hn))

end Submodule.LatticeQuotientTorsion

theorem solution
    {K : Type*} [DivisionRing K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L := by
  haveI : NeZero n := ⟨hn⟩
  rw [← Nat.card_congr
    (Submodule.LatticeQuotientTorsion.latticeQuotTorsionEquiv (K := K) L hn).toEquiv,
    ModN.natCard_eq]
