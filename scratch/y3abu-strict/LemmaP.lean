import ZInQKernel.HDecomp.QM.Polar

/-! # y3abu-strict: Lemma P, lattice form, in one statement

rv-qm-polar compiled the pieces (`eq_smul_E0`, `eq_pm_E0_of_principal`, `riemann_sign`, `lemmaP_lattice`) but
not "the identification of `E0R` with `E₀ ⊗ ℝ`" nor "the combination with `eq_smul_E0`". Both are done here:
`realExt_eq` and `lemmaP_lattice_unique`. -/

set_option linter.all false

noncomputable section

namespace Y3ABUStrict.LemmaP

open RvQMPolar
open LeafQM (B)

/-- The standard basis `1, i, j, k` of `B`. -/
def stdB : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The real coordinates of `x ∈ B_ℝ` in the basis `1, i, j, k`. -/
def crdR (x : BR) : Fin 4 → ℝ := ![x.re, x.imI, x.imJ, x.imK]

/-- **The real extension `E ⊗ ℝ` of a `ℚ`-bilinear form `E` on `B`** (`H₁(A, ℚ) ⊗ ℝ = B_ℝ`), in coordinates. -/
def realExt (E : LinearMap.BilinForm ℚ B) (x y : BR) : ℝ :=
  ∑ r : Fin 4, ∑ s : Fin 4, crdR x r * crdR y s * (E (stdB r) (stdB s) : ℝ)

/-- **`E₀ ⊗ ℝ = E0R`**, and more generally the real extension of `c E₀` is `c E0R`. -/
theorem realExt_eq (E : LinearMap.BilinForm ℚ B) (c : ℚ) (hE : ∀ x y, E x y = c * E0 x y) (x y : BR) :
    realExt E x y = (c : ℝ) * E0R x y := by
  simp only [realExt, hE, Fin.sum_univ_four, crdR, stdB, E0, trd, muInv, E0R, muInvR]
  simp
  ring

/-- **Lemma P, lattice form.** For every complex structure `j` on `B_ℝ = H₁(A, ℝ)` commuting with `𝒪`
(`j² = −1`, acting by right multiplication), there is **exactly one** `ℚ`-bilinear form `E` on `B = H₁(A, ℚ)`
that is alternating, has Rosati involution `x ↦ x† = μ⁻¹x̄μ` on `B ⊇ 𝒪` (type `μ`), is unimodular on `𝒪`
(Gram determinant 1 on the basis `(1, i, (1+j)/2, (i+k)/2)`: principal), and is positive for `j`
(`E_ℝ(xj, x) > 0` for `x ≠ 0`: a Riemann form). It is `E₀` or `−E₀`, according to the sign of `imJ(j)`. -/
theorem lemmaP_lattice_unique (j : BR) (hj : j * j = -1) :
    ∃! E : LinearMap.BilinForm ℚ B, (∀ x, E x x = 0) ∧ (∀ a x y, E (a * x) y = E x (dag a * y)) ∧
      (Matrix.of fun r s => E (oBasis r) (oBasis s)).det = 1 ∧
      ∀ x : BR, x ≠ 0 → 0 < realExt E (x * j) x := by
  have hgram : (Matrix.of fun r s => E0bil (oBasis r) (oBasis s)) = gram := by
    ext r s; simp [E0bil_apply, E0_gram]
  have one_ne : (1 : BR) ≠ 0 := one_ne_zero
  rcases riemann_sign j hj with ⟨-, hpos⟩ | ⟨-, hneg⟩
  · refine ⟨E0bil, ⟨fun x => E0_alt x, fun a x y => E0_rosati a x y, by rw [hgram, gram_det], fun x hx => ?_⟩, ?_⟩
    · rw [realExt_eq E0bil 1 (fun x y => by rw [E0bil_apply, one_mul])]; simpa using hpos x hx
    · rintro E ⟨halt, hros, hdet, hE⟩
      rcases eq_pm_E0_of_principal E halt hros hdet with h | h
      · exact LinearMap.ext₂ fun x y => by rw [h, E0bil_apply]
      · exfalso
        have h1 := hE 1 one_ne
        rw [realExt_eq E (-1) (fun x y => by rw [h]; ring)] at h1
        have h2 := hpos 1 one_ne
        push_cast at h1
        linarith
  · refine ⟨-E0bil, ⟨fun x => by simp [E0bil_apply, E0_alt x], fun a x y => by simp [E0bil_apply, E0_rosati a x y],
      ?_, fun x hx => ?_⟩, ?_⟩
    · have : (Matrix.of fun r s => (-E0bil) (oBasis r) (oBasis s)) = (-1 : ℚ) • gram := by
        ext r s; simp [E0bil_apply, E0_gram]
      rw [this, Matrix.det_smul, gram_det]; norm_num
    · rw [realExt_eq (-E0bil) (-1) (fun x y => by simp [E0bil_apply])]
      have := hneg x hx
      push_cast; linarith
    · rintro E ⟨halt, hros, hdet, hE⟩
      rcases eq_pm_E0_of_principal E halt hros hdet with h | h
      · exfalso
        have h1 := hE 1 one_ne
        rw [realExt_eq E 1 (fun x y => by rw [h, one_mul])] at h1
        have h2 := hneg 1 one_ne
        push_cast at h1
        linarith
      · exact LinearMap.ext₂ fun x y => by simp [h, E0bil_apply]

end Y3ABUStrict.LemmaP
