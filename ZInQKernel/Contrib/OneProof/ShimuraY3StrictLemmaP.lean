import ZInQKernel.HDecomp.QM.Polar
import ZInQKernel.HDecomp.Analytic.QMLattice

/-! # y3abu-strict (helper of `ShimuraY3Strict.lean`): Lemma P, lattice form, in one statement

rv-qm-polar compiled the pieces (`eq_smul_E0`, `eq_pm_E0_of_principal`, `riemann_sign`, `lemmaP_lattice`) but
not "the identification of `E0R` with `E₀ ⊗ ℝ`", "the combination with `eq_smul_E0`" nor "the transport to
`Λ = 𝒪v`". These are done here for the QM tori `ℂ²/Λ_τ`, `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, of the kernel (`qmLattice`):
`realExt_eq`, `lemmaP_lattice_unique`, the complex structure `j_τ` (`iotaC_mul_jτ`), and `lemmaP_qmTorus`.
Also `eq_smul_E0K`: over every field of characteristic 0 (e.g. `ℚ_ℓ`), every alternating form with adjoint `†`
is a multiple of `E₀`, so an `𝒪`-linear level structure automatically respects the pairings up to a scalar.

What is **not** here (and cannot be stated today): the passage from Riemann forms on `H₁(A, ℤ)` to polarizations
`λ : A → A^∨` of the abelian variety (Riemann's theorem; no dual abelian variety in Mathlib), and anything over a
base scheme (the relative Lemma P). -/

set_option linter.all false

noncomputable section

namespace Y3ABUStrict.LemmaP

open RvQMPolar Matrix
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
  have hgram : (Matrix.of fun r s => E0bil (oBasis r) (oBasis s)) = RvQMPolar.gram := by
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
    · have : (Matrix.of fun r s => (-E0bil) (oBasis r) (oBasis s)) = (-1 : ℚ) • RvQMPolar.gram := by
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

/-- The real embedding `ι_ℝ : B_ℝ → M₂(ℝ)` (the extension of `BPAnalytic.QM.iota`). -/
def iotaR (y : BR) : Matrix (Fin 2) (Fin 2) ℝ :=
  y.re • 1 + y.imI • BPAnalytic.QM.Mi + y.imJ • BPAnalytic.QM.Mj + y.imK • (BPAnalytic.QM.Mi * BPAnalytic.QM.Mj)

theorem iotaR_mul (x y : BR) : iotaR (x * y) = iotaR x * iotaR y := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [iotaR, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp only [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)] <;> ring

/-- `ι_ℝ` extends N5's `ι` (`BPAnalytic.QM.iota`) on `B ⊆ B_ℝ`. -/
theorem iotaR_ofB (x : LeafQM.B) :
    iotaR ⟨(x.re : ℝ), (x.imI : ℝ), (x.imJ : ℝ), (x.imK : ℝ)⟩ = BPAnalytic.QM.iota x := by
  simp [iotaR, BPAnalytic.QM.iota]

/-- **The complex structure of `ℂ²/Λ_τ` on `H₁ ⊗ ℝ = B_ℝ`**: for `τ = s + it`,
`j_τ = (s√2/(2t)) i + ((3 + |τ|²)/(6t)) j + ((|τ|² − 3)√2/(12t)) k`, so that `ι(j_τ)(τ, 1)ᵀ = i (τ, 1)ᵀ`. -/
def jτ (τ : UpperHalfPlane) : BR :=
  ⟨0, τ.re * √2 / (2 * τ.im), (3 + τ.re ^ 2 + τ.im ^ 2) / (6 * τ.im),
    (τ.re ^ 2 + τ.im ^ 2 - 3) * √2 / (12 * τ.im)⟩

theorem jτ_sq (τ : UpperHalfPlane) : jτ τ * jτ τ = -1 := by
  have ht : τ.im ≠ 0 := τ.im_pos.ne'
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext <;> simp [jτ] <;> field_simp <;> ring_nf <;> simp only [h2] <;> ring

theorem jτ_imJ_pos (τ : UpperHalfPlane) : 0 < (jτ τ).imJ := by
  simp only [jτ]
  have := τ.im_pos
  positivity

/-- `v_τ = (τ, 1)ᵀ`. -/
def vτ (τ : UpperHalfPlane) : Fin 2 → ℂ := ![(τ : ℂ), 1]

/-- `ι_ℝ` as complex matrices. -/
def iotaC (y : BR) : Matrix (Fin 2) (Fin 2) ℂ := (iotaR y).map Complex.ofRealHom

theorem iotaR_jτ (τ : UpperHalfPlane) : iotaR (jτ τ) =
    !![τ.re / τ.im, -(τ.re ^ 2 + τ.im ^ 2) / τ.im; 1 / τ.im, -τ.re / τ.im] := by
  have ht : τ.im ≠ 0 := τ.im_pos.ne'
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [iotaR, jτ, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> (try simp only [h2]) <;> ring

theorem iotaC_jτ (τ : UpperHalfPlane) : iotaC (jτ τ) *ᵥ vτ τ = Complex.I • vτ τ := by
  have ht : τ.im ≠ 0 := τ.im_pos.ne'
  rw [iotaC, iotaR_jτ]
  ext k
  fin_cases k <;> simp [vτ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> field_simp <;> ring

/-- **Right multiplication by `j_τ` on `B_ℝ` is multiplication by `i` on `ℂ²`** under `x ↦ ι(x)(τ, 1)ᵀ`
(the `ℝ`-linear isomorphism `B_ℝ ≅ ℂ²` carrying `B ⊇ 𝒪` onto `ℚΛ_τ ⊇ Λ_τ`). -/
theorem iotaC_mul_jτ (τ : UpperHalfPlane) (x : BR) :
    iotaC (x * jτ τ) *ᵥ vτ τ = Complex.I • (iotaC x *ᵥ vτ τ) := by
  rw [iotaC, iotaR_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec]
  change iotaC x *ᵥ (iotaC (jτ τ) *ᵥ vτ τ) = _
  rw [iotaC_jτ, Matrix.mulVec_smul]

/-- **Lemma P for the QM torus `ℂ²/Λ_τ`, `τ ∈ ℍ`, in lattice coordinates.** Identify `H₁(ℂ²/Λ_τ, ℚ) = ℚΛ_τ` with
`B` by `x ↦ ι(x)(τ, 1)ᵀ` (so `Λ_τ ↔ 𝒪`, `ι(a)` acts by left multiplication). Then multiplication by `i` on `ℂ²`
is right multiplication by `j_τ` on `B_ℝ` (first clause), and there is exactly one alternating `ℚ`-bilinear form on
`B` with Rosati involution `†` (type `μ`), unimodular on `𝒪` (principal), and positive for this complex structure
(a Riemann form): a unique principal polarization of type `μ` on the torus, read as a Riemann form. -/
theorem lemmaP_qmTorus (τ : UpperHalfPlane) :
    (∀ x : BR, iotaC (x * jτ τ) *ᵥ vτ τ = Complex.I • (iotaC x *ᵥ vτ τ)) ∧
    ∃! E : LinearMap.BilinForm ℚ B, (∀ x, E x x = 0) ∧ (∀ a x y, E (a * x) y = E x (dag a * y)) ∧
      (Matrix.of fun r s => E (oBasis r) (oBasis s)).det = 1 ∧
      ∀ x : BR, x ≠ 0 → 0 < realExt E (x * jτ τ) x :=
  ⟨iotaC_mul_jτ τ, lemmaP_lattice_unique (jτ τ) (jτ_sq τ)⟩

/-- **The unique form is `E₀ = trd(μ⁻¹ x ȳ)`, for every `τ ∈ ℍ`** (`imJ(j_τ) = (3 + |τ|²)/(6 Im τ) > 0`). -/
theorem lemmaP_qmTorus_eq (τ : UpperHalfPlane) (E : LinearMap.BilinForm ℚ B) (halt : ∀ x, E x x = 0)
    (hros : ∀ a x y, E (a * x) y = E x (dag a * y))
    (hdet : (Matrix.of fun r s => E (oBasis r) (oBasis s)).det = 1)
    (hpos : ∀ x : BR, x ≠ 0 → 0 < realExt E (x * jτ τ) x) : E = E0bil := by
  have hE0 : ∀ x : BR, x ≠ 0 → 0 < realExt E0bil (x * jτ τ) x := by
    intro x hx
    rw [realExt_eq E0bil 1 (fun x y => by rw [E0bil_apply, one_mul])]
    rcases riemann_sign (jτ τ) (jτ_sq τ) with ⟨-, h⟩ | ⟨h, -⟩
    · simpa using h x hx
    · exact absurd h (not_lt.2 (jτ_imJ_pos τ).le)
  have hgram : (Matrix.of fun r s => E0bil (oBasis r) (oBasis s)) = RvQMPolar.gram := by
    ext r s; simp [E0bil_apply, E0_gram]
  exact ((lemmaP_qmTorus τ).2.unique ⟨halt, hros, hdet, hpos⟩
    ⟨fun x => E0_alt x, fun a x y => E0_rosati a x y, by rw [hgram, gram_det], hE0⟩)


/-! ## Level compatibility (the PEL condition on level structures is automatic) -/

section LevelCompat

variable {K : Type} [Field K] [CharZero K]

/-- `B ⊗ K` for `B = (2, −3 | ℚ)` (Mathlib's `QuaternionAlgebra K 2 0 (−3)`). -/
abbrev BK (K : Type) [Field K] := QuaternionAlgebra K 2 0 (-3)

/-- `μ = 2j + k` and `μ⁻¹ = −μ/6` in `B ⊗ K`. -/
def muK : BK K := ⟨0, 0, 2, 1⟩
def muInvK : BK K := ⟨0, 0, -1/3, -1/6⟩

/-- The Rosati involution of type `μ`, `x† = μ⁻¹ x̄ μ`, on `B ⊗ K`. -/
def dagK (x : BK K) : BK K := muInvK * star x * muK

/-- `E₀ ⊗ K = trd(μ⁻¹ x ȳ)` on `B ⊗ K` (the PEL datum's symplectic form `ψ`). -/
def E0K (x y : BK K) : K := 2 * (muInvK * x * star y).re

theorem decompK (z : BK K) :
    z = z.re • (1 : BK K) + z.imI • (⟨0, 1, 0, 0⟩ : BK K) + z.imJ • (⟨0, 0, 1, 0⟩ : BK K) +
      z.imK • (⟨0, 0, 0, 1⟩ : BK K) := by
  ext <;> simp

/-- **Level compatibility is automatic (over any field `K` of characteristic 0, e.g. `ℚ_ℓ`).** Every alternating
`K`-bilinear form on `B ⊗ K` for which `B ⊗ K` acts with adjoint `†` (type `μ`) is a scalar multiple of
`ψ = E₀ ⊗ K`. Applied to `η^* e^λ` for an `𝒪`-linear level structure `η : B ⊗ ℚ_ℓ ≅ V_ℓ(A)` (the Weil pairing
of the type-`μ` polarization has adjoint `†` on `ι(B)`): every `𝒪`-linear level structure respects the pairings
up to a scalar, which is the PEL condition. (rv-qm-polar's `eq_smul_E0` over `ℚ`, generalized; same proof.) -/
theorem eq_smul_E0K (E : LinearMap.BilinForm K (BK K)) (halt : ∀ x, E x x = 0)
    (hros : ∀ a x y, E (a * x) y = E x (dagK a * y)) :
    ∃ c : K, ∀ x y, E x y = c * E0K x y := by
  set f : BK K →ₗ[K] K := E 1 with hf
  have hE : ∀ x y, E x y = f (dagK x * y) := by
    intro x y; rw [hf, ← hros x 1 y, mul_one]
  have hf0 : ∀ x, f (dagK x * x) = 0 := fun x => by rw [← hE]; exact halt x
  have d1 : dagK (1 : BK K) * 1 = 1 := by
    simp only [dagK, muInvK, muK]; ext <;> simp <;> norm_num
  have r1 : f 1 = 0 := by simpa [d1] using hf0 1
  have e2 : dagK (⟨1, 1, 0, 0⟩ : BK K) * ⟨1, 1, 0, 0⟩ = (3 : K) • (1 : BK K) + (2 : K) • ⟨0, 1, 0, 0⟩ := by
    simp only [dagK, muInvK, muK]; ext <;> simp <;> norm_num
  have e3 : dagK (⟨1, 0, 1, 0⟩ : BK K) * ⟨1, 0, 1, 0⟩ = (10 : K) • (1 : BK K) + (6 : K) • ⟨0, 1, 0, 0⟩
      + (-2 : K) • (⟨0, 0, 1, 0⟩ + ⟨0, 0, 0, 1⟩) := by
    simp only [dagK, muInvK, muK]; ext <;> simp <;> norm_num
  have r2 : f ⟨0, 1, 0, 0⟩ = 0 := by
    have := hf0 ⟨1, 1, 0, 0⟩
    rw [e2, map_add, map_smul, map_smul, r1] at this
    simp at this
    exact this
  have r3 : f ⟨0, 0, 0, 1⟩ = - f ⟨0, 0, 1, 0⟩ := by
    have := hf0 ⟨1, 0, 1, 0⟩
    rw [e3, map_add, map_add, map_smul, map_smul, map_smul, map_add, r1, r2] at this
    simp at this
    linear_combination this
  refine ⟨-(f ⟨0, 0, 1, 0⟩) / 2, fun x y => ?_⟩
  rw [hE, decompK (dagK x * y)]
  simp only [map_add, map_smul, r1, r2, r3, smul_eq_mul]
  simp only [E0K, dagK, muInvK, muK]
  simp
  ring

end LevelCompat

end Y3ABUStrict.LemmaP
