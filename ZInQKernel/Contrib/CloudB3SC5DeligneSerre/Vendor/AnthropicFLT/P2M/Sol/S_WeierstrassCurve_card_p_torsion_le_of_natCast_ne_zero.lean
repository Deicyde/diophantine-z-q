/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero (git blob a20c8df12d17a84e2303cb38b5a1cedfc7ac87d7, sha256 29699781860030e85cdbbc6bc6b5bf141d835e2942a76e0f37ddddb80037d33d).
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

namespace P2MW.S_WeierstrassCurve_card_p_torsion_le_of_natCast_ne_zero

open WeierstrassCurve WeierstrassCurve.Affine

theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ} [W.IsElliptic]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : (p : F) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) ≤ p ^ 2 := by
  classical
  let K := AlgebraicClosure F
  have hpK : (p : K) ≠ 0 := by
    intro h
    apply hpF
    have h1 : algebraMap F K (p : F) = algebraMap F K 0 := by rw [map_natCast, map_zero, h]
    exact (algebraMap F K).injective h1
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) W hpK
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (Submodule.torsionBy ℤ (W⁄K).toAffine.Point p) := Finite.of_equiv _ e.toEquiv
  have hcardK : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point p) = p ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod]
    ring

  let f : W.toAffine.Point →+ (W⁄K).toAffine.Point := Point.map (W' := W) (Algebra.ofId F K)
  have hmem : ∀ P : Submodule.torsionBy ℤ W.toAffine.Point p,
      f P ∈ Submodule.torsionBy ℤ (W⁄K).toAffine.Point p := by
    intro P
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    rw [← map_zsmul f, hP, map_zero]
  let ι : Submodule.torsionBy ℤ W.toAffine.Point p → Submodule.torsionBy ℤ (W⁄K).toAffine.Point p :=
    fun P => ⟨f P, hmem P⟩
  have hι : Function.Injective ι := by
    intro P Q h
    apply Subtype.ext
    exact Point.map_injective (Algebra.ofId F K) (congrArg Subtype.val h)
  calc Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p)
      ≤ Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point p) := Nat.card_le_card_of_injective ι hι
    _ = p ^ 2 := hcardK
