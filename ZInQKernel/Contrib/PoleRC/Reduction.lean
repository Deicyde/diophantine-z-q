import ZInQKernel.Contrib.PoleRC.Bookkeeping
import ZInQKernel.Contrib.PoleRC.Rescale

/-!
# Theorem 5.2 from `CR_M` and the simultaneous construction

`poleCompleteness_of_crm`: `CRM → SimultaneousConstruction → Manuscript.PoleCompleteness`,
following `diophantine_zq.tex` lines 1019–1121: the squareclass bookkeeping
(`bookkeeping`), the simultaneous construction of `n, nθ` (`SimultaneousConstruction`, a named
hypothesis), `CR_M` at `n` and at `nθ`, and the rescaling (`witnesses_of_points`).
-/

namespace ZInQ.Manuscript.PoleRC

theorem not_isSquare_of_mod_three {β : ℕ} (h : β % 3 = 2) : ¬ IsSquare ((β : ℤ) : ℚ) := by
  rw [Int.cast_natCast, Rat.isSquare_natCast_iff]
  rintro ⟨r, rfl⟩
  have : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rw [Nat.mul_mod] at h
  rcases this with h' | h' | h' <;> rw [h'] at h <;> norm_num at h

/-- **Theorem 5.2 from `CR_M` and the simultaneous construction** (lines 1019–1121). -/
theorem poleCompleteness_of_crm (hCR : CRM) (hSC : SimultaneousConstruction) :
    Manuscript.PoleCompleteness := by
  intro B hden hpos hlt hS0
  obtain ⟨b, β, θ, s, c, hb, hs, hc, hβsf, hθsf, hβ24, hθ24, hcop, hβsq, hθsq, hA⟩ :=
    bookkeeping B hden hpos hlt hS0
  obtain ⟨n, hn, hnθ, hn12, h8n, hβn, h8nθ, hβnθ⟩ :=
    hSC β θ hβsf hθsf hβ24 hθ24 hcop hβsq hθsq
  have hnsf : Squarefree n := Squarefree.of_mul_left hnθ
  have hθpos : 0 < θ := by omega
  have hnθ12 : n * θ % 12 = 11 := by
    rw [Nat.mul_mod, hn12, show θ % 12 = 1 by omega]
  have h1 := hCR n hn hnsf hn12 h8n β hβn
  have h2 := hCR (n * θ) (Nat.mul_pos hn hθpos) hnθ hnθ12 h8nθ β hβnθ
  have hβnsq := not_isSquare_of_mod_three (β := β) (by omega)
  obtain ⟨t₁, y₁, ht₁, hy₁⟩ := point_of_locM (by exact_mod_cast hn) hβnsq h1
  obtain ⟨t₂, y₂, ht₂, hy₂⟩ :=
    point_of_locM (by exact_mod_cast Nat.mul_pos hn hθpos) hβnsq h2
  push_cast at hy₁ hy₂
  set A := (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
    (1 + 12 * b 5) * B with hAdef
  obtain ⟨hAβ, hHθ⟩ := hA A rfl
  have hβ0 : (β : ℚ) ≠ 0 := by have : 0 < β := by omega
                               exact_mod_cast this.ne'
  obtain ⟨e, z, r₁, r₂, w, he, hr₁, hr₂⟩ := witnesses_of_points (A := A) (H := A * (A - B ^ 2))
    hs hc (by exact_mod_cast hn.ne') (by exact_mod_cast hθpos.ne') hβ0 hAβ hHθ ht₁ ht₂ hy₁ hy₂
  refine ⟨b, e, z, r₁, r₂, w, polePoly_eq_zero_of B b e z r₁ r₂ w hb ?_⟩
  intro A' H' hA' hH'
  subst hA' hH'
  exact ⟨he, hr₁, hr₂⟩

end ZInQ.Manuscript.PoleRC
