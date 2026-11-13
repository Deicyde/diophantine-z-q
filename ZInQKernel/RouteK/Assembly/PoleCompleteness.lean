import ZInQKernel.Hypotheses.CertifiedRank
import ZInQKernel.RouteK.Assembly.DL
import ZInQKernel.RouteK.Assembly.Points

/-!
# Route K: pole completeness from CR₃

`docs/research/slot-k.md` §4.2, the chain `L1, L2, L3 ⇒ configurations; L4, L5 ⇒ certificates (DL);
CR₃ ⇒ points; L6 ⇒ PoleSoluble`. For an admissible `B`, DL gives `m` and `n` such that `C_{|n|}`
and `C_{|nθ|}` carry certificates of Selmer type for the class `β`; CR₃ turns them into rational
points with abscissas in `βℚ*²`, and L6 into a zero of the Route K pole polynomial.
-/

namespace ZInQ

open RouteK

theorem natAbs_cast_sq (k : ℤ) : ((k.natAbs : ℕ) : ℚ) ^ 2 = (k : ℚ) ^ 2 := by
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- **PC from CR₃**: under the certified-rank hypothesis, every admissible `B` satisfies `Φ(B)` for
the Route K pole polynomial. -/
theorem poleCompleteness_of_certifiedRank (hCR : CertifiedRank) : PoleCompleteness := by
  rw [poleCompleteness_iff_admissible]
  intro B hB
  obtain ⟨m, n, hm, hβn, hn5, hβ7, hnsq, hnθsq, hnθ5, ⟨hd₁, hc₁, hσ₁⟩, ⟨hd₂, hc₂, hσ₂⟩⟩ :=
    descent_lemma hB
  have hβ0 : betaOf B m ≠ 0 := by intro h; rw [h] at hβ7; norm_num at hβ7
  have hmB : (m : ℚ) * B ≠ 0 := by
    intro h; exact hβ0 (by rw [betaOf, h, sqf_zero])
  have hβsq : Squarefree (betaOf B m) := sqf_squarefree hmB
  have hmB' : (m : ℚ) ≠ B := by
    intro h
    have h1 : (0 : ℚ) < m := h ▸ hB.2.1
    have h2 : (m : ℚ) < 1 := by linarith [hB.2.2.1, h ▸ le_refl (m : ℚ)]
    have : (0 : ℤ) < m := by exact_mod_cast h1
    have : m < 1 := by exact_mod_cast h2
    omega
  obtain ⟨x₁, y₁, h₁, hx₁, hs₁⟩ := hCR n.natAbs (betaOf B m) hn5
    (Int.squarefree_natAbs.mpr hnsq) hβsq (Int.dvd_natAbs.mpr hβn) hβ7 hc₁ hσ₁
  obtain ⟨x₂, y₂, h₂, hx₂, hs₂⟩ := hCR (n * thetaOf B m).natAbs (betaOf B m) hnθ5
    (Int.squarefree_natAbs.mpr hnθsq) hβsq (Int.dvd_natAbs.mpr (dvd_mul_of_dvd_left hβn _)) hβ7
    hc₂ hσ₂
  have hn0 : (n.natAbs : ℚ) ≠ 0 := by
    have : n.natAbs ≠ 0 := by omega
    exact_mod_cast this
  refine poleSoluble_of_points (y₂ := y₂) hB.ne_zero hm hmB' hn0 h₁ hx₁ hs₁ ?_ hx₂ hs₂
  rw [h₂, natAbs_cast_sq, mul_pow, natAbs_cast_sq]
  push_cast
  ring

end ZInQ
