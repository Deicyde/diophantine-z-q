import ZInQKernel.Contrib.OneProof.EichlerBound.Embed

/-! eichler-bound, part B2: bad primes, the unit criterion `J𝒪 = 𝒪` (class number one of `𝒪`), and the
injectivity step (equal lattice classes give `𝒪^×`-conjugate embeddings). No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6

theorem qinv_mul_cancel_left {c : B} (hc : c ≠ 0) (y : B) : qinv c * (c * y) = y := by
  rw [← mul_assoc, qinv_mul hc, one_mul]

theorem mul_qinv_cancel_left {c : B} (hc : c ≠ 0) (y : B) : c * (qinv c * y) = y := by
  rw [← mul_assoc, mul_qinv hc, one_mul]

theorem smul_mem_O {x : B} (hx : x ∈ LeafQM.O) (z : ℤ) : (z : ℚ) • x ∈ LeafQM.O := by
  rw [← coe_mul_eq_smul]; exact LeafQM.O.mul_mem (intCast_mem z) hx

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

/-- `ℓ` is bad for `(Ψ, Φ)`: `c̄ d ∈ ℓ𝒪` for all `c, d ∈ J(Ψ, Φ) ∩ 𝒪`. -/
def Bad (Ψ Φ : OptEmb k R) (ℓ : ℤ) : Prop := ∀ c ∈ Jo Ψ Φ, ∀ d ∈ Jo Ψ Φ, LO ℓ (star c * d)

/-- The other side: `c d̄ ∈ ℓ𝒪`. -/
def Bad' (Ψ Φ : OptEmb k R) (ℓ : ℤ) : Prop := ∀ c ∈ Jo Ψ Φ, ∀ d ∈ Jo Ψ Φ, LO ℓ (c * star d)

theorem star_J_mul {Ψ : OptEmb k R} {c0 : B} (a b : k) :
    star (c0 * Ψ.1 a) * (c0 * Ψ.1 b) = nrd c0 • Ψ.1 (sk Ψ a * b) := by
  calc star (c0 * Ψ.1 a) * (c0 * Ψ.1 b) = star (Ψ.1 a) * (star c0 * c0) * Ψ.1 b := by
        rw [star_mul]; simp only [mul_assoc]
    _ = star (Ψ.1 a) * ((nrd c0 : ℚ) : B) * Ψ.1 b := by rw [star_mul_self']
    _ = ((nrd c0 : ℚ) : B) * (star (Ψ.1 a) * Ψ.1 b) := by rw [← coe_comm]; simp only [mul_assoc]
    _ = nrd c0 • Ψ.1 (sk Ψ a * b) := by rw [map_mul, emb_sk, coe_mul_eq_smul]

theorem J_mul_star {Ψ Φ : OptEmb k R} {c0 : B} (hc0 : c0 ∈ J Ψ Φ) (a b : k) :
    (c0 * Ψ.1 a) * star (c0 * Ψ.1 b) = nrd c0 • Φ.1 (a * sk Ψ b) := by
  calc (c0 * Ψ.1 a) * star (c0 * Ψ.1 b) = c0 * (Ψ.1 a * star (Ψ.1 b)) * star c0 := by
        rw [star_mul]; simp only [mul_assoc]
    _ = c0 * Ψ.1 (a * sk Ψ b) * star c0 := by rw [map_mul, emb_sk]
    _ = Φ.1 (a * sk Ψ b) * (c0 * star c0) := by rw [hc0 (a * sk Ψ b)]; simp only [mul_assoc]
    _ = nrd c0 • Φ.1 (a * sk Ψ b) := by rw [mul_star_self', mul_coe_eq_smul]

include Bs in
/-- **The conjugation trick**: `c̄d ∈ ℓ𝒪 ∀ c, d` implies `cd̄ ∈ ℓ𝒪 ∀ c, d` (both embeddings are optimal and `R`
is stable under the conjugation of `k`). -/
theorem bad'_of_bad (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {ℓ : ℤ} (hℓ : ℓ ≠ 0)
    (h : Bad Ψ Φ ℓ) : Bad' Ψ Φ ℓ := by
  obtain ⟨c0, hc0, hne⟩ := exists_Jo Bs hk Ψ Φ
  intro c hc d hd
  obtain ⟨x, hx⟩ := J_param Bs hc0.2 hne hc.2
  obtain ⟨y, hy⟩ := J_param Bs hc0.2 hne hd.2
  have h1 := h _ hc _ hd
  rw [hx, hy, star_J_mul] at h1
  rw [hx, hy, J_mul_star hc0.2]
  set q : ℚ := (ℓ : ℚ)⁻¹ * nrd c0 with hq
  have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
  have hwR : (q : k) * (sk Ψ x * y) ∈ R := by
    rw [← optEmb_mem Ψ, map_mul, emb_ratCast, coe_mul_eq_smul, hq, mul_smul]
    exact LO_div hℓ h1
  have hsw := sk_mem Ψ hwR
  rw [sk_ratCast_mul, sk_mul, sk_sk] at hsw
  rw [LO_iff_smul ℓ hℓ]
  refine ⟨_, (optEmb_mem Φ _).2 hsw, ?_⟩
  rw [show Φ.1 ((q : k) * (x * sk Ψ y)) = q • Φ.1 (x * sk Ψ y) by rw [map_mul, emb_ratCast, coe_mul_eq_smul],
    smul_smul, hq, ← mul_assoc, mul_inv_cancel₀ hℓq, one_mul]

end Emb

end EichlerBound
