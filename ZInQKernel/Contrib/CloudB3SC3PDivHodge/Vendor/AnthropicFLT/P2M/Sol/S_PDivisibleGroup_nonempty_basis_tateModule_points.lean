/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PDivisibleGroup_nonempty_basis_tateModule_points
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Points
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PDivisibleGroup_nonempty_basis_tateModule_points

set_option autoImplicit false

open PDivisibleGroup

namespace PDivTateRank

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable {L : Type} [CommRing L] [Algebra R L]

theorem nsmul_eq_zero_iff (n : ℕ) (z : G.Points L) :
    (p ^ n) • z = 0 ↔ ∃ x : G.Point L n, G.pointsMkAdd L n (Additive.ofMul x) = z := by
  constructor
  · intro hz
    obtain ⟨m, y, rfl⟩ := Points.exists_mkAdd G z

    set w := max m n with hw
    have hy : G.pointsMkAdd L w (Additive.ofMul (G.pointInclLE L (le_max_left m n) y)) =
        G.pointsMkAdd L m (Additive.ofMul y) := G.pointsMkAdd_pointInclLE _ y
    rw [← hy] at hz ⊢
    set y' := G.pointInclLE L (le_max_left m n) y with hy'

    have hpow : y' ^ (p ^ n) = 1 := by
      apply G.pointsMkAdd_injective w
      change G.pointsMkAdd L w (Additive.ofMul (y' ^ p ^ n)) = G.pointsMkAdd L w (Additive.ofMul 1)
      rw [ofMul_pow, map_nsmul, hz, ofMul_one, map_zero]

    obtain ⟨x, hx⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_right m n) y' hpow
    exact ⟨x, by rw [← hx, pointsMkAdd_pointInclLE]⟩
  · rintro ⟨x, rfl⟩
    exact G.nsmul_pointsMkAdd_eq_zero n x

private theorem _root_.PDivTateRank.mem_torsionBy_iff (n : ℕ) (z : G.Points L) :
    z ∈ Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ) ↔
      ∃ x : G.Point L n, G.pointsMkAdd L n (Additive.ofMul x) = z := by
  rw [Submodule.mem_torsionBy_iff, ← nsmul_eq_zero_iff G n z, natCast_zsmul]

-- [port T6] export of private `PDivTateRank` names replaced by qualified uses below: mem_torsionBy_iff

noncomputable def pointEquivTorsionBy (n : ℕ) :
    G.Point L n ≃ Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ) :=
  Equiv.ofBijective (fun x => ⟨G.pointsMkAdd L n (Additive.ofMul x), (PDivTateRank.mem_torsionBy_iff G n _).2 ⟨x, rfl⟩⟩)
    ⟨fun x y hxy => G.pointsMkAdd_injective n (congrArg Subtype.val hxy),
     fun z => by
      obtain ⟨x, hx⟩ := (PDivTateRank.mem_torsionBy_iff G n z.1).1 z.2
      exact ⟨x, Subtype.ext hx⟩⟩

section Count

variable (K : Type) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]

theorem natCard_point (n : ℕ) : Nat.card (G.Point K n) = p ^ (n * h) := by
  rw [← G.finrank_level n]
  change Nat.card (WithConv (G.level n →ₐ[R] K)) = _
  rw [Nat.card_congr (WithConv.equiv (G.level n →ₐ[R] K))]
  exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R (G.level n) K

theorem natCard_torsionBy (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (G.Points K) ((p ^ n : ℕ) : ℤ)) = p ^ (n * h) := by
  rw [← natCard_point G K n]
  exact (Nat.card_congr (pointEquivTorsionBy G n)).symm

end Count

end PDivTateRank

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L] :
    Nonempty (Module.Basis (Fin h) ℤ_[p] (TateModule p (G.Points L))) :=
  TateModule.nonempty_basis_of_card_torsionBy p h fun n => by
    rw [PDivTateRank.natCard_torsionBy G L n, pow_mul]
