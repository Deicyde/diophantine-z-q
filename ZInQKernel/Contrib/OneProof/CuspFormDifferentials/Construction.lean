import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Regularity

/-! K13: for a weight-two cusp form `f` on `Γ₀(N)`, P1 applied to `f / j′` gives `A`, `B`
in `ℂ ⊗[ℚ] ℚ(X₀(N))` with `f / j′ = A / B` on every germ, and the rational differential
`Ψ f = (A / B) · dj` is regular at every closed point of `curveC N`, hence (K12) a global
differential. The analytic verifications (the order arithmetic at arc points and the
vanishing at cusps) are proved here; P1, K10, K11 and K12 enter as hypotheses. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane ModularCurve ShimuraPointDict
open scoped Topology TensorProduct MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open X0Model

variable (N : ℕ) [NeZero N]

/-- The germ of `f` is the germ of `(A / B) · j′` whenever `f / j′` has the germ of `A / B`. -/
theorem germ_eq_ratGerm_mul_jDeriv (f : CuspFormN N) (A B : FieldC N) (τ : ℍ)
    (h : (quotientByJDeriv N f : PuncturedGerm (τ : ℂ)) =
      meromorphicIncl (τ : ℂ) (ratGerm N τ A B)) :
    ((fun z => f (ofComplex z)) : PuncturedGerm (τ : ℂ)) =
      meromorphicIncl (τ : ℂ) (ratGerm N τ A B * jDerivGerm τ) := by
  have hne : ∀ᶠ z in 𝓝[≠] (τ : ℂ), jDeriv z ≠ 0 :=
    (analyticAt_jDeriv τ).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 =>
      jDeriv_not_eventually_zero τ (h0.filter_mono nhdsWithin_le_nhds)
  rw [map_mul, ← h]
  change ((fun z => f (ofComplex z)) : PuncturedGerm (τ : ℂ)) =
    ((fun z => quotientByJDeriv N f z * jDeriv z : ℂ → ℂ) : PuncturedGerm (τ : ℂ))
  exact Germ.coe_eq.mpr (hne.mono fun z hz => by
    simp only [quotientByJDeriv]
    rw [div_mul_cancel₀ _ hz])

/-- The order arithmetic at an arc point: if `e ∣ n + 1` and `n ≥ 0` then `n ≥ e - 1`. -/
theorem order_ge_of_dvd {e : ℕ} {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z)
    (hdvd : ∀ n : ℤ, meromorphicOrderAt F z = n → (e : ℤ) ∣ n + 1) :
    ((((e : ℤ) - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F z) := by
  cases hn : meromorphicOrderAt F z with
  | top => exact le_top
  | coe n =>
    have h0 : (0 : WithTop ℤ) ≤ (n : WithTop ℤ) := hn ▸ hF.meromorphicOrderAt_nonneg
    have h0' : 0 ≤ n := by exact_mod_cast h0
    have hle : (e : ℤ) ≤ n + 1 := Int.le_of_dvd (by omega) (hdvd n hn)
    exact_mod_cast (show (e : ℤ) - 1 ≤ n by omega)

/-- **K13, regularity at every closed point.** If `f / j′` has the germ of `A / B` at every
point of `ℍ` (with `B` nonzero there), then `(A / B) · dj` is regular at every closed point,
given K10 and K11. -/
theorem diffRegularAt_of_cuspForm (h10 : K10 N) (h11a : K11Arc N) (h11c : K11Cusp N)
    (f : CuspFormN N) (A B : FieldC N)
    (hAB : ∀ τ : ℍ, fieldGermC N τ B ≠ 0 ∧
      (quotientByJDeriv N f : PuncturedGerm (τ : ℂ)) = meromorphicIncl (τ : ℂ) (ratGerm N τ A B))
    (x : (curveC N).left) (hx : IsClosed ({x} : Set (curveC N).left)) :
    DiffRegularAt N x A B := by
  have hgerm (τ : ℍ) := germ_eq_ratGerm_mul_jDeriv N f A B τ (hAB τ).2
  rcases h10 x hx with ⟨τ, rfl⟩ | ⟨σ, p, rfl, hp⟩
  · obtain ⟨e, -, hk⟩ := h11a τ
    have hF := cuspForm_analyticAt N f τ
    obtain ⟨hdvd, hreg⟩ := hk A B (fun z => f (ofComplex z)) (hAB τ).1 hF.meromorphicAt (hgerm τ)
    exact hreg (order_ge_of_dvd hF hdvd)
  · refine h11c σ p hp A B (f : ℍ → ℂ) (fun τ => (hAB τ).1) hgerm ?_
      (CuspFormClass.zero_at_infty_slash f σ)
    exact Eventually.of_forall fun τ => (cuspForm_analyticAt N f (σ • τ)).differentiableAt

/-- **K13, construction.** Given P1, K10, K11 and K12, every weight-two cusp form `f` on
`Γ₀(N)` determines `A`, `B` with `f / j′ = A / B` on every germ of `ℍ`, and a global
differential representing `(A / B) · dj`. -/
theorem exists_psi (hP1 : P1 N) (h10 : K10 N) (h11a : K11Arc N) (h11c : K11Cusp N)
    (h12 : K12 N) (f : CuspFormN N) :
    ∃ (A B : FieldC N) (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)),
      (∀ τ : ℍ, fieldGermC N τ B ≠ 0 ∧
        (quotientByJDeriv N f : PuncturedGerm (τ : ℂ)) =
          meromorphicIncl (τ : ℂ) (ratGerm N τ A B)) ∧
      (∀ x : (curveC N).left, IsClosed ({x} : Set (curveC N).left) → DiffRegularAt N x A B) ∧
      RepresentsDiffOn N ⊤ ω A B := by
  obtain ⟨A, B, hAB⟩ := hP1 _ (isX0Function_quotientByJDeriv N f)
  have hreg := diffRegularAt_of_cuspForm N h10 h11a h11c f A B hAB
  obtain ⟨ω, hω⟩ := h12 A B hreg
  exact ⟨A, B, ω, hAB, hreg, hω⟩

/-- The hypotheses used for the construction of `Ψ`. -/
structure PsiHypotheses : Prop where
  p1 : P1 N
  k10 : K10 N
  k11Arc : K11Arc N
  k11Cusp : K11Cusp N
  k12 : K12 N

/-- **K13.** `Ψ f = (A / B) · dj` with `A / B` from P1 applied to `f / j′`, as a global
differential. -/
def psi (H : PsiHypotheses N) (f : CuspFormN N) : Γ((curveC N).hom.relativeDifferentials, ⊤) :=
  (exists_psi N H.p1 H.k10 H.k11Arc H.k11Cusp H.k12 f).choose_spec.choose_spec.choose

/-- The numerator of `Ψ f`. -/
def psiNum (H : PsiHypotheses N) (f : CuspFormN N) : FieldC N :=
  (exists_psi N H.p1 H.k10 H.k11Arc H.k11Cusp H.k12 f).choose

/-- The denominator of `Ψ f`. -/
def psiDen (H : PsiHypotheses N) (f : CuspFormN N) : FieldC N :=
  (exists_psi N H.p1 H.k10 H.k11Arc H.k11Cusp H.k12 f).choose_spec.choose

theorem psi_spec (H : PsiHypotheses N) (f : CuspFormN N) :
    (∀ τ : ℍ, fieldGermC N τ (psiDen N H f) ≠ 0 ∧
      (quotientByJDeriv N f : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (ratGerm N τ (psiNum N H f) (psiDen N H f))) ∧
    (∀ x : (curveC N).left, IsClosed ({x} : Set (curveC N).left) →
      DiffRegularAt N x (psiNum N H f) (psiDen N H f)) ∧
    RepresentsDiffOn N ⊤ (psi N H f) (psiNum N H f) (psiDen N H f) :=
  (exists_psi N H.p1 H.k10 H.k11Arc H.k11Cusp H.k12 f).choose_spec.choose_spec.choose_spec

end ZInQ.Manuscript.RC.CuspFormDifferentials
