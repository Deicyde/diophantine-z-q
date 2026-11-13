import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.RingClassGenus

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section SquaresFix

open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp.CurveA

variable {n : ℕ} [NeZero n]

/-- **Squares of `Pic(O_{n,4})` fix every square root of an element of `K_n` lying in `H_{n,4}`**
(`Gal(K(√q)/K)` has exponent 2). With `adjI_le_H4`, `adjSqrt_two_le_H4` and
`adjSqrt_le_hilbertField`: `2Cl'_n` fixes `i`, `√2` and `√p` (`p ∣ n`), as TYZ use ("`t ∈ Φ₀ ⊂ 2Cl′_n`
fixes `i ∈ L_n`", `rv-tyz-inputs.md` §1.5). -/
theorem artin4_sq_apply_of_sq {x : SeparableClosure (QNeg n)} (hx : x ∈ H4 n)
    (hsq : ∃ q : QNeg n, x ^ 2 = algebraMap (QNeg n) _ q) (b : Pic (O4 n)) :
    ((artin4 n (b ^ 2) ⟨x, hx⟩ : H4 n) : SeparableClosure (QNeg n)) = x := by
  obtain ⟨q, hq⟩ := hsq
  set g := artin4 n b
  have hy : (⟨x, hx⟩ : H4 n) ^ 2 = algebraMap (QNeg n) (H4 n) q := Subtype.ext (by simpa using hq)
  have hg : g ⟨x, hx⟩ = ⟨x, hx⟩ ∨ g ⟨x, hx⟩ = -⟨x, hx⟩ := by
    have : g ⟨x, hx⟩ ^ 2 = (⟨x, hx⟩ : H4 n) ^ 2 := by rw [← map_pow, hy, AlgEquiv.commutes]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  rw [map_pow, pow_two, AlgEquiv.mul_apply]
  rcases hg with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

end SquaresFix

end ZInQ.Contrib.TYZGenus.RingClass

namespace ZInQ.Contrib.TYZGenus.RingClassBridge

open ZInQ.Contrib.TYZGenus.RingClass ZInQ.Contrib.TYZGenus.Package ZInQ.Contrib.TYZDecomp.CurveA
  ZInQ.RouteK.Rank5b

/-- **`ρ` acting on `H_{n,4}` as an element of `Pic(O_{n,4})²` fixes `i`.** -/
theorem fixes_iQ_of_actsAsArtin4_sq {n : ℕ} [NeZero n] {ρ : ZInQ.Contrib.TYZGenus.CM.GalQ} {b : Pic (O4 n)}
    (hρ : ActsAsArtin4 ρ n (b ^ 2)) : ρ iQ = iQ := by
  have hx : jK (QNeg n) ∈ H4 n := jK_mem_H4
  have hfix := hρ ⟨jK (QNeg n), hx⟩
  rw [artin4_sq_apply_of_sq hx ⟨-1, by rw [jK_sq, map_neg, map_one]⟩] at hfix
  have hs2 : (embed n (jK (QNeg n))) ^ 2 = iQ ^ 2 := by
    rw [← map_pow, jK_sq, map_neg, map_one, iQ_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs2 with h | h
  · rw [← h]; exact hfix
  · have : iQ = -embed n (jK (QNeg n)) := by rw [h, neg_neg]
    rw [this, map_neg, hfix]

end ZInQ.Contrib.TYZGenus.RingClassBridge
