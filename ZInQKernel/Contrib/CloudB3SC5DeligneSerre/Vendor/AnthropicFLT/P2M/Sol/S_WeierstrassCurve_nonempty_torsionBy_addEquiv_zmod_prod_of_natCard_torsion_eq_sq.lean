/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq (git blob af6bfc2abbad1788bff08a390fb9262479fe8379, sha256 d693e155b9f42f43bcce64c7e07ab17191f54bed3d7918ae87a1dcfb10fb5093).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace P2MKcTors

variable {k Ω : Type*} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω] (E : WeierstrassCurve k)
  [E.IsElliptic] (N : ℕ) [NeZero N]

def torsionEquiv (A : Type*) [AddCommGroup A] (N : ℕ) :
    {P : A // N • P = 0} ≃ Submodule.torsionBy ℤ A N where
  toFun P := ⟨P.1, by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact P.2⟩
  invFun P := ⟨P.1, by have h := P.2; rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at h; exact h⟩
  left_inv P := rfl
  right_inv P := rfl

theorem main (hN : (N : k) ≠ 0)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) := by
  classical
  let Ωb := AlgebraicClosure Ω
  have hNb : (N : Ωb) ≠ 0 := fun h => hN ((algebraMap k Ωb).injective (by
    rw [map_natCast, map_zero]; exact h))
  obtain ⟨e₀⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (K := Ωb) E hNb

  let ι : Ω →ₐ[k] Ωb := IsScalarTower.toAlgHom k Ω Ωb
  let f : (E.baseChange Ω).toAffine.Point →+ (E.baseChange Ωb).toAffine.Point := Point.map ι
  have hf : Function.Injective f := Point.map_injective ι
  let T := Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N
  let Tb := Submodule.torsionBy ℤ (E.baseChange Ωb).toAffine.Point N
  have hmem : ∀ P : T, f P.1 ∈ Tb := fun P => by
    have h := P.2
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at h ⊢
    rw [← map_nsmul, h, map_zero]
  let g : T →+ Tb :=
    { toFun := fun P => ⟨f P.1, hmem P⟩
      map_zero' := by ext1; exact map_zero f
      map_add' := fun P Q => by ext1; exact map_add f P.1 Q.1 }
  have hg : Function.Injective g := fun P Q h => Subtype.ext (hf (congrArg Subtype.val h))

  have hT : Nat.card T = N ^ 2 := by rw [← hfull]; exact (Nat.card_congr (torsionEquiv _ N)).symm
  have hTb : Nat.card Tb = N ^ 2 := by
    rw [← Nat.card_congr e₀.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  haveI : Finite Tb := Nat.finite_of_card_ne_zero (by rw [hTb]; exact pow_ne_zero 2 (NeZero.ne N))
  haveI : Finite T := Finite.of_injective g hg
  have hbij : Function.Bijective g := hg.bijective_of_nat_card_le (by rw [hT, hTb])
  exact ⟨e₀.trans (AddEquiv.ofBijective g hbij).symm⟩

end P2MKcTors

end

open WeierstrassCurve in

theorem solution
    {k Ω : Type*} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω] (E : WeierstrassCurve k)
    [E.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) :=
  P2MKcTors.main E N hN hfull
