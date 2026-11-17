import ZInQKernel.Contrib.OneProof.HfxProof.Lemma25

/-!
# hfx-proof: the local order `R_p = ℤ_p + ℤ_p ω + 4O_{B,p}` for a general `ω`

Task hfx-proof. Generalizes t21-proof's `InR`/`Loc2OK` (written for `ω² = ω − 1`) to any Hurwitz `ω`
with `ω² = Tω − N` and `ω̄ = T − ω` (`T, N ∈ ℤ_p`): `R_p` is closed under products and conjugation,
and `ℚ_p^× R_p^×` is a group. For a uniformizer-type `ϖ` (Hurwitz, commuting with `ω`, norm of
valuation one) conjugation by `ϖ` preserves `ℚ_p^× R_p^×` at `p = 2`, so `ℚ_2^× R_2^× ∪ ℚ_2^× R_2^× ϖ⁻¹` is a group
(`P2`), which contains `K_2^× = ℚ_2(ω)^×` when `K_2` is ramified.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.T21Proof
open scoped Quaternion

variable {p : ℕ} [Fact p.Prime]

section R

variable {ω : ℍ[ℚ_[p]]} {T N : ℚ_[p]}

theorem InR.mul' (hω : IsHur (Zp p) ω) (hT : T ∈ Zp p) (hN : N ∈ Zp p)
    (hω2 : ω * ω = T • ω - N • 1) {u u' : ℍ[ℚ_[p]]}
    (hu : InR ω u) (hu' : InR ω u') (hhu' : IsHur (Zp p) u') : InR ω (u * u') := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  obtain ⟨x', z', hx', hz', a', ha', rfl⟩ := hu'
  have mx := mem_Zp.mpr hx
  have mz := mem_Zp.mpr hz
  have mx' := mem_Zp.mpr hx'
  have mz' := mem_Zp.mpr hz'
  have hxz : IsHur (Zp p) (x • (1 : ℍ[ℚ_[p]]) + z • ω) :=
    (isHur_one.smul mx).add (hω.smul mz)
  refine ⟨x * x' - N * (z * z'), x * z' + z * x' + T * (z * z'), ?_, ?_,
    (x • (1 : ℍ[ℚ_[p]]) + z • ω) * a' + a * (x' • 1 + z' • ω + (4 : ℚ_[p]) • a'),
    (hxz.mul ha').add (ha.mul hhu'), ?_⟩
  · exact (Zp p).sub_mem ((Zp p).mul_mem mx mx') ((Zp p).mul_mem hN ((Zp p).mul_mem mz mz'))
  · exact (Zp p).add_mem ((Zp p).add_mem ((Zp p).mul_mem mx mz') ((Zp p).mul_mem mz mx'))
      ((Zp p).mul_mem hT ((Zp p).mul_mem mz mz'))
  · have e1 : (x • (1 : ℍ[ℚ_[p]]) + z • ω) * (x' • 1 + z' • ω) =
        (x * x' - N * (z * z')) • 1 + (x * z' + z * x' + T * (z * z')) • ω := by
      simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hω2]
      module
    rw [smul_add, mul_add, add_mul, mul_add, add_mul, ← e1]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, mul_add, add_mul]
    module

theorem InR.star' (hT : T ∈ Zp p) (hstar : star ω = T • 1 - ω) {u : ℍ[ℚ_[p]]} (hu : InR ω u) :
    InR ω (star u) := by
  obtain ⟨x, z, hx, hz, a, ha, rfl⟩ := hu
  refine ⟨x + T * z, -z, mem_Zp.mp ((Zp p).add_mem (mem_Zp.mpr hx) ((Zp p).mul_mem hT (mem_Zp.mpr hz))),
    by rwa [norm_neg], Star.star a, ha.star, ?_⟩
  simp only [star_add, Quaternion.star_smul, star_one, hstar]
  module

theorem Loc2OK.mul' (hω : IsHur (Zp p) ω) (hT : T ∈ Zp p) (hN : N ∈ Zp p)
    (hω2 : ω * ω = T • ω - N • 1) {y z : ℍ[ℚ_[p]]}
    (hy : Loc2OK ω y) (hz : Loc2OK ω z) : Loc2OK ω (y * z) := by
  obtain ⟨c, hc, u, rfl, hu, hn, hR⟩ := hy
  obtain ⟨c', hc', u', rfl, hu', hn', hR'⟩ := hz
  refine ⟨c * c', mul_ne_zero hc hc', u * u', ?_, hu.mul hu', ?_, InR.mul' hω hT hN hω2 hR hR' hu'⟩
  · rw [smul_mul_smul]
  · rw [map_mul, norm_mul, hn, hn', one_mul]

theorem Loc2OK.of_mul_eq_one' (hT : T ∈ Zp p) (hstar : star ω = T • 1 - ω) {y z : ℍ[ℚ_[p]]}
    (hy : Loc2OK ω y) (h : y * z = 1) : Loc2OK ω z := by
  obtain ⟨c, hc, u, rfl, hu, hn, hR⟩ := hy
  refine ⟨c⁻¹, inv_ne_zero hc, _, eq_of_mul_eq_one hc (normSq_ne_zero_of hn) h,
    isHur_inv_star hu hn, normSq_inv_star hn, InR.smul (by rw [norm_inv, hn, inv_one])
      (InR.star' hT hstar hR)⟩

theorem Loc2OK.smul_left {c : ℚ_[p]} (hc : c ≠ 0) {y : ℍ[ℚ_[p]]} (hy : Loc2OK ω y) :
    Loc2OK ω (c • y) := by
  obtain ⟨c', hc', u, rfl, hu, hn, hR⟩ := hy
  exact ⟨c * c', mul_ne_zero hc hc', u, by rw [smul_smul], hu, hn, hR⟩

end R

end ZInQ.Contrib.HfxProof
