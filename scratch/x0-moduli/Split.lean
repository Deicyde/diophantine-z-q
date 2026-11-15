import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.TYZChain.ModFn

noncomputable section

namespace X0Moduli

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM Complex T5Glue
open ZInQ.Contrib.TYZGenus.Shimura (IsRatModFn)
open ZInQ.Contrib.TYZGenus.ShimuraModFnTask (jInv scaleH evalJ IsIsolated RatX0Rep)

/-! ## `j(τ) = j(ℂ/⟨1, τ⟩)` -/

theorem ppD_eq_pp (τ : UpperHalfPlane) : ppD τ = pp τ := rfl

/-- Klein's `j = E₄³/Δ` is the `j`-invariant `1728 g₂³/(g₂³ − 27 g₃²)` of `ℂ/⟨1, τ⟩`. -/
theorem jInv_eq_jL (τ : UpperHalfPlane) : jInv τ = jL (pp τ) := by
  have h4 := G_eq_E (k := 4) (by norm_num) τ
  have h6 := G_eq_E (k := 6) (by norm_num) τ
  have hz4 : riemannZeta ((4 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 4 / 90 := by
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num]; exact riemannZeta_four
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
    rw [show ((6 : ℕ) : ℂ) = 6 by norm_num]; exact riemannZeta_six
  rw [hz4] at h4
  rw [hz6] at h6
  have hΔ := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hne := ModularForm.discriminant_ne_zero τ
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : (ppD τ).g₂ ^ 3 - 27 * (ppD τ).g₃ ^ 2 =
      64 * (Real.pi : ℂ) ^ 12 / 27 * 1728 * ModularForm.discriminant τ := by
    rw [PeriodPair.g₂, PeriodPair.g₃, h4, h6, hΔ]
    simp only [ModularForm.E₄, ModularForm.E₆]
    ring
  have hg2 : (ppD τ).g₂ = 4 / 3 * (Real.pi : ℂ) ^ 4 * ModularForm.E₄ τ := by
    rw [PeriodPair.g₂, h4]; simp only [ModularForm.E₄]; ring
  rw [← ppD_eq_pp, jL, discL, key, hg2, jInv]
  field_simp
  ring

/-- `σ(j(τ)) = j(τ')` when `σ(E_τ) ≅ E_{τ'}`. -/
theorem jInv_conj {σ : ℂ →+* ℂ} {τ τ' : UpperHalfPlane} {μ : ℂ}
    (h : IsConjModel σ (pp τ) (pp τ') μ) : σ (jInv τ) = jInv τ' := by
  rw [jInv_eq_jL, jInv_eq_jL, h.jL]

/-! ## The split -/

/-- **GLUE JN-CONJ (`σ` carries `j(E/C)` to `j(E^σ/C^σ)`).** Under the hypotheses of
`T5Glue.X0ModuliGalois` (`σ(E_τ) ≅ E_{τ'}` through `μ`, carrying `σ(1/N)` to `k/N`),
`σ(j(Nτ)) = j(Nτ')`. Content: `ℂ/⟨1/N, τ⟩ = E_τ/⟨1/N⟩ ≅ ℂ/⟨1, Nτ⟩`; Vélu's formulas express
`g₂, g₃` of `⟨1/N, τ⟩` as polynomials over `ℚ` in `g₂(τ), g₃(τ)` and `℘_τ(m/N)`, `1 ≤ m < N`; the
addition law of `℘` gives `σ(℘_τ(m/N)) = μ²℘_{τ'}(mk/N)` and `(k, N) = 1`. Glue: proved from the
textbook leaves `WeierstrassGroupLaw` and `VeluAnalytic` (see `JNConj.lean`) or open. -/
def JNConj : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      σ (jInv (scaleH N τ)) = jInv (scaleH N τ')

/-- **X0-MODULI at the non-isolated points (consequence; the same sources as
`T5Glue.X0ModuliGalois`).** `T5Glue.X0ModuliGalois` restricted to points `τ` that are not
isolated on the plane model `(j, j_N)` of `X₀(N)` (`ShimuraModFnTask.IsIsolated`: two of the
`ψ(N)` cyclic `N`-isogenies of `E_τ` have isomorphic targets). Such `E_τ` has complex
multiplication (a non-scalar endomorphism `E_τ → E_τ/C ≅ E_τ/C' → E_τ` of degree `N²`), so there
are finitely many such points on `Y₀(N)`, all CM points. -/
def X0ModuliGaloisNonIsolated : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      (∀ i < N, ∃ a : Qbar, ιC a = modCoord N τ i) →
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      ¬ IsIsolated N τ →
      σ (g τ) = g τ'

/-- `σ` commutes with evaluation at `(j, j_N)` once it carries `j(τ), j(Nτ)` to `j(τ'), j(Nτ')`. -/
theorem evalJ_conj (σ : ℂ →+* ℂ) {N : ℕ} {τ τ' : UpperHalfPlane} (h0 : σ (jInv τ) = jInv τ')
    (h1 : σ (jInv (scaleH N τ)) = jInv (scaleH N τ')) (P : MvPolynomial (Fin 2) ℚ) :
    σ (evalJ N P τ) = evalJ N P τ' := by
  have := MvPolynomial.comp_aeval_apply (f := ![jInv τ, jInv (scaleH N τ)]) σ.toRatAlgHom P
  simp only [RingHom.toRatAlgHom_apply] at this
  rw [evalJ, this, evalJ]
  congr 2
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- **X0-MODULI at isolated points** from `RatX0Rep` and `JNConj`. -/
theorem x0ModuliGalois_isolated (hR : RatX0Rep) (hJ : JNConj) :
    ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      IsIsolated N τ →
      σ (g τ) = g τ' := by
  intro N hN g hg σ τ τ' μ hμ hk hiso
  obtain ⟨A, B, hrep, hB⟩ := hR N hN g hg
  have hB0 := hB τ hiso
  have h0 : (σ : ℂ →+* ℂ) (jInv τ) = jInv τ' := jInv_conj hμ
  have h1 : (σ : ℂ →+* ℂ) (jInv (scaleH N τ)) = jInv (scaleH N τ') := hJ N hN σ τ τ' μ hμ hk
  have eB := evalJ_conj (σ : ℂ →+* ℂ) h0 h1 B
  have eA := evalJ_conj (σ : ℂ →+* ℂ) h0 h1 A
  have hB0' : evalJ N B τ' ≠ 0 := by
    rw [← eB]; intro h; exact hB0 ((map_eq_zero_iff _ (σ : ℂ →+* ℂ).injective).1 h)
  have hg1 : g τ = evalJ N A τ / evalJ N B τ := by
    rw [← hrep τ]; field_simp
  have hg2 : g τ' = evalJ N A τ' / evalJ N B τ' := by
    rw [← hrep τ']; field_simp
  have : (σ : ℂ →+* ℂ) (g τ) = g τ' := by
    rw [hg1, map_div₀, eA, eB, hg2]
  exact this

/-- **The split:** `X0ModuliGalois ⇐ RatX0Rep ∧ JNConj ∧ X0ModuliGaloisNonIsolated`. -/
theorem x0ModuliGalois_of_split (hR : RatX0Rep) (hJ : JNConj)
    (hS : X0ModuliGaloisNonIsolated) : T5Glue.X0ModuliGalois := by
  intro N hN g hg σ τ τ' μ halg hμ hk
  by_cases hiso : IsIsolated N τ
  · exact x0ModuliGalois_isolated hR hJ N hN g hg σ τ τ' μ hμ hk hiso
  · exact hS N hN g hg σ τ τ' μ halg hμ hk hiso

end X0Moduli

#print axioms X0Moduli.x0ModuliGalois_of_split
