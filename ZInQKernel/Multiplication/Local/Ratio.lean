import ZInQKernel.Multiplication.Local.FormalLogarithm
import ZInQKernel.Multiplication.Local.Nonvanishing

/-!
# Full-logarithm ratios of multiples of `P₀`

Blueprint: `multiplication/local/logarithm-ratio.md`.

Let `p` be an odd prime, `π ∣ p` a prime of `ℤ[s]` and `λ` the formal logarithm of `E` over the
completion `K_π`. If `h ≠ 0` and `[h]P₀`, `[u]P₀` lie in `E₁(K_π)`, then `λ([h]P₀) ≠ 0` and
`λ([u]P₀) = (u/h) λ([h]P₀)`.

The article assumes the Mordell–Weil hypothesis, for "`P₀` has infinite order"; this holds
unconditionally by the torsion theorem of `Model/Descent` (see `genP0_not_isOfFinAddOrder`), so
the statement has no hypothesis.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

theorem algebraMap_neg_genD_sq (π : Zs) (hπ : Prime π) :
    algebraMap K0 ((primeSpec π hπ).adicCompletion K0) (-genD ^ 2) = -genDAt π hπ ^ 2 := by
  simp

/-- A point of `E(K₀)` as a point of `E(K_π)`. -/
noncomputable def mapE (π : Zs) (hπ : Prime π) :
    genCurve.toAffine.Point → (shortCurve (-genDAt π hπ ^ 2)).toAffine.Point :=
  mapPt (A := -genD ^ 2) (algebraMap K0 _) (algebraMap_neg_genD_sq π hπ)

open Classical in
theorem mapE_zsmul (π : Zs) (hπ : Prime π) (n : ℤ) (P : genCurve.toAffine.Point) :
    mapE π hπ (n • P) = n • mapE π hπ P :=
  map_zsmul (mapPtHom (A := -genD ^ 2) (algebraMap K0 ((primeSpec π hπ).adicCompletion K0))
    (algebraMap_neg_genD_sq π hπ)) n P

open Classical in
/-- **Full-logarithm ratios.** For an odd prime `p`, a prime `π ∣ p` of `ℤ[s]`, and `h, u ∈ ℤ`
with `h ≠ 0` such that `[h]P₀` and `[u]P₀` lie in `E₁(K_π)`: `λ([h]P₀) ≠ 0` and
`λ([u]P₀) = (u/h) λ([h]P₀)`. -/
theorem ellLog_ratio {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π)
    (hπp : π ∣ (p : Zs)) {h u : ℤ} (hh : h ≠ 0)
    (hH : mapE π hπ (h • genP0) ∈ W1 (vComp π hπ) (-genDAt π hπ ^ 2))
    (hU : mapE π hπ (u • genP0) ∈ W1 (vComp π hπ) (-genDAt π hπ ^ 2)) :
    ellLog (mapE π hπ (h • genP0)) ≠ 0 ∧
      ellLog (mapE π hπ (u • genP0)) = (u / h) * ellLog (mapE π hπ (h • genP0)) := by
  have hres := residueChar_completion (p := p) hp2 hπ hπp
  have hA := vComp_neg_genDAt_sq_nonneg hπ
  obtain ⟨hinj, -, -⟩ := ellLog_unramified hres hp2 hA
  -- `[h]P₀ ≠ O`, so its image is not `O`
  have hH0 : mapE π hπ (h • genP0) ≠ 0 := by
    have hne := zsmul_genP0_ne_zero hh
    generalize h • genP0 = Q at hne ⊢
    rcases Q with _ | ⟨x, y, hxy⟩
    · exact absurd rfl hne
    · exact Point.some_ne_zero _
  have hl0 : ellLog (mapE π hπ (h • genP0)) ≠ 0 := by
    intro h0
    exact hH0 (hinj hH (zero_mem_W1 _) (by rw [h0, ellLog_zero]))
  refine ⟨hl0, ?_⟩
  -- `[u]H = [h]U = image of [uh]P₀`
  have e1 : u • mapE π hπ (h • genP0) = h • mapE π hπ (u • genP0) := by
    rw [← mapE_zsmul, ← mapE_zsmul, smul_smul, smul_smul, mul_comm]
  have l1 := ellLog_zsmul hres hA hH u
  have l2 := ellLog_zsmul hres hA hU h
  rw [e1, l2] at l1
  have hh' : (h : (primeSpec π hπ).adicCompletion K0) ≠ 0 := Int.cast_ne_zero.mpr hh
  field_simp
  linear_combination l1

end ZInQ.Mult
