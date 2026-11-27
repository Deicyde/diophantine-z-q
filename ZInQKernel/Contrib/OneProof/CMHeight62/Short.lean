import ZInQKernel.Contrib.OneProof.CMHeight62.ShortModel
import ZInQKernel.Contrib.OneProof.CMHeight62.Discriminant
import ZInQKernel.Contrib.OneProof.CMHeight62.Eval

/-! # cmheight62-p1, step 4 (first bullet): the short coordinates along a period of `E`

For a uniformization `Φ_E` of `E` at `σ|_K` with lattice `c(ℤ + τℤ)` and a short datum `D`
(`x, y` of `abVar_shortSections_of_genusOne`): there is `u ≠ 0` with `x(Φ_E(cw)) = u² ℘(w)`,
`y(Φ_E(cw)) = u³ ℘'(w)/2` off the lattice (the tree's genus-one comparison, JDescent2/JDescent5,
re-run with `D`'s coordinates kept), and `σ(Δ_W) = u¹² Δ(ℤτ + ℤ) = u¹² discAn τ`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped UpperHalfPlane _root_.PeriodPair
open _root_.ZInQ.LeafPush2 (CPts cDom cEvalAt IsUniformization)
open HDec.CMBranch.CMjBridges

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

theorem cEvalAt_sectionConst {F : Type} [Field F] {A : PkgI3.AbVar F}
    {σ : F →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (a : F)
    (s : Γ(A.X.left, U)) :
    cEvalAt p U (abVarSectionConst A U a * s) = σ a * cEvalAt p U s ∧
      cEvalAt p U (abVarSectionConst A U a) = σ a := by
  have hc : cEvalAt p U (abVarSectionConst A U a) = σ a := by
    let q : Spec (CommRingCat.of ℂ) ⟶ A.X.left := p.left
    let f := Spec.map (CommRingCat.ofHom σ)
    have h := Scheme.Hom.appLE_comp_appLE_assoc q A.X.hom ⊤ U ⊤ (by simp) hp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    have hw : q ≫ A.X.hom = f := Over.w p
    rw [hw] at h
    have hTop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    rw [hTop, Scheme.ΓSpecIso_naturality] at h
    apply_fun (fun g : Γ(Spec (CommRingCat.of F), ⊤) ⟶ CommRingCat.of ℂ =>
      g ((Scheme.ΓSpecIso (CommRingCat.of F)).inv a)) at h
    unfold cEvalAt
    rw [dite_eq_left hp]
    exact h.trans (by simp)
  refine ⟨?_, hc⟩
  change ev p.left U _ = σ a * ev p.left U s
  rw [ev_mul _ _ hp]
  exact congrArg (· * ev p.left U s) hc

variable {K : Type} [Field K] [NumberField K] {E : PkgI3.AbVar K}

/-- **The short coordinates along a period of `E`** (the tree's genus-one comparison with `D`'s
coordinates kept). -/
theorem short_comparison (hdim : E.dim = 1) (D : ShortData E) {σ : K →+* ℂ} {τ : ℍ}
    {Λ : Submodule ℤ (Fin 1 → ℂ)} {Φ : (Fin 1 → ℂ) → CPts E σ} {s : ℂ}
    (hΦ : IsUniformization σ Λ Φ) (hs : s ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ))) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ z ∉ (PeriodPair.ofTau τ).lattice,
      ⊤ ≤ (Φ (fun _ => s * z)).left ⁻¹ᵁ abVarPunctured E ∧
      cEvalAt (Φ (fun _ => s * z)) (abVarPunctured E) D.x =
        u ^ 2 * ℘[PeriodPair.ofTau τ] z ∧
      cEvalAt (Φ (fun _ => s * z)) (abVarPunctured E) D.y =
        u ^ 3 * (℘'[PeriodPair.ofTau τ] z / 2) := by
  let P := PeriodPair.ofTau τ
  let U := abVarPunctured E
  have hU : ∀ z ∉ P.lattice, ⊤ ≤ (Φ (fun _ => s * z)).left ⁻¹ᵁ U :=
    fun z hz => abVar_period_mem_punctured hΦ hs hΛ hz
  have hEven := abVar_period_abscissa_even abVarFunctionFieldGenusOne E hdim hΦ hs hΛ D.P D.hp
    D.x D.y D.a D.b D.hx D.hy D.hreg D.heq
  have hPole := abVar_evaluatedPole_of_order E hΦ hs hΛ D.P D.hp D.x D.hx
  let v : ℂ → (Fin 1 → ℂ) := fun z _ => s * z
  let ev' (f : Γ(E.X.left, U)) (z : ℂ) := cEvalAt (Φ (v z)) U f
  have han (f : Γ(E.X.left, U)) : AnalyticOnNhd ℂ (ev' f) P.latticeᶜ := by
    apply DifferentiableOn.analyticOnNhd _ P.isClosed_lattice.isOpen_compl
    have hv : Differentiable ℂ v := by
      apply differentiable_pi.mpr
      intro i
      change Differentiable ℂ (fun z : ℂ => s * z)
      fun_prop
    exact (hΦ.2.2.2.2 U f).comp hv.differentiableOn (fun z hz => hU z hz)
  have hPer (l : P.lattice) : Function.Periodic (ev' D.x) l := by
    intro z
    have hvl : v l ∈ Λ := by
      obtain ⟨n, m, hm⟩ := PeriodPair.mem_lattice.mp l.2
      apply (hΛ _).mpr
      refine ⟨m, n, ?_⟩
      have h' : (n : ℂ) * (τ : ℂ) + m = (l : ℂ) := by simpa [P] using hm
      change s * (l : ℂ) = _
      rw [← h']
      ring
    have hadd : v (z + l) = v z + v l := funext fun i => by simp [v, mul_add]
    change cEvalAt (Φ (v (z + l))) U D.x = cEvalAt (Φ (v z)) U D.x
    have hUnit : Φ (v z) * (1 : CPts E σ) = Φ (v z) := mul_one _
    rw [hadd, hΦ.1, (hΦ.2.1 _).mpr hvl, hUnit]
  have hCubic (z : ℂ) (hz : z ∉ P.lattice) :
      ev' D.y z ^ 2 = ev' D.x z ^ 3 + σ D.a * ev' D.x z + σ D.b := by
    have hp : ⊤ ≤ (Φ (v z)).left ⁻¹ᵁ U := hU z hz
    have hq := congrArg (evHom (Φ (v z)).left U hp) D.heq
    simp only [map_pow, map_add, map_mul] at hq
    have hA : evHom (Φ (v z)).left U hp (abVarSectionConst E U D.a) = σ D.a := by
      exact (ev_eq_evHom _ _ hp _).symm.trans (cEvalAt_sectionConst (Φ (v z)) U hp D.a D.x).2
    have hB : evHom (Φ (v z)).left U hp (abVarSectionConst E U D.b) = σ D.b := by
      exact (ev_eq_evHom _ _ hp _).symm.trans (cEvalAt_sectionConst (Φ (v z)) U hp D.b D.x).2
    rw [hA, hB] at hq
    have ex : ev' D.x z = evHom (Φ (v z)).left U hp D.x := ev_eq_evHom _ _ hp _
    have ey : ev' D.y z = evHom (Φ (v z)).left U hp D.y := ev_eq_evHom _ _ hp _
    rw [ex, ey]
    exact hq
  have hSimple (r : ℂ) (hr : r ^ 3 + σ D.a * r + σ D.b = 0) : 3 * r ^ 2 + σ D.a ≠ 0 := by
    let W : WeierstrassCurve K := ⟨0, 0, 0, D.a, D.b⟩
    have hW : (W.map σ).Δ ≠ 0 := by
      rw [WeierstrassCurve.map_Δ]; exact (map_ne_zero σ).mpr D.hΔ
    have he : (W.map σ).toAffine.Equation r 0 := by
      rw [WeierstrassCurve.Affine.equation_iff]
      simpa [W, WeierstrassCurve.map] using hr.symm
    have hn := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hW).mp he
    have h := (WeierstrassCurve.Affine.nonsingular_iff' r 0).mp hn
    intro hz
    rcases h.2 with h₁ | h₂
    · apply h₁
      change σ (0 : K) * 0 - (3 * r ^ 2 + 2 * σ 0 * r + σ D.a) = 0
      simp [hz]
    · apply h₂
      change 2 * 0 + σ (0 : K) * r + σ 0 = 0
      simp
  obtain ⟨u, hu, hCoords⟩ := shortCubic_coordinates_of_doublePole P (han D.x) (han D.y) hPer
    hEven hPole hCubic hSimple
  exact ⟨u, hu, fun z hz => ⟨hU z hz, hCoords z hz⟩⟩

theorem exists_weierstrassP_eq' (P : PeriodPair) (x : ℂ) :
    ∃ z ∉ P.lattice, ℘[P] z = x := by
  let h := P.discriminant_ne_zero
  let W := P.weierstrassCurve
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq
    (x ^ 3 + W.a₄ * x + W.a₆) (by decide : 0 < 2)
  have he : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simpa [W] using hy
  have hQ := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    h.weierstrassCurve_Δ_ne_zero).mp he
  let Q := WeierstrassCurve.Affine.Point.some x y hQ
  obtain ⟨z, hz⟩ := (P.isUniformization_toPoint h).2.1 Q
  have hnot : z ∉ P.lattice := by
    intro hm
    rw [P.toPoint_of_mem h hm] at hz
    exact WeierstrassCurve.Affine.Point.some_ne_zero hQ hz.symm
  rw [P.toPoint_of_notMem h hnot] at hz
  exact ⟨z, hnot, (WeierstrassCurve.Affine.Point.some.inj hz).1⟩

/-- **Step 4, first bullet.** `σ(Δ_W) = u¹² · discAn τ`. -/
theorem sigma_W_Δ (D : ShortData E) {σ : K →+* ℂ} {τ : ℍ}
    {Φ : (Fin 1 → ℂ) → CPts E σ} {s : ℂ} {u : ℂ} (hu0 : u ≠ 0)
    (hu : ∀ z ∉ (PeriodPair.ofTau τ).lattice,
      ⊤ ≤ (Φ (fun _ => s * z)).left ⁻¹ᵁ abVarPunctured E ∧
      cEvalAt (Φ (fun _ => s * z)) (abVarPunctured E) D.x =
        u ^ 2 * ℘[PeriodPair.ofTau τ] z ∧
      cEvalAt (Φ (fun _ => s * z)) (abVarPunctured E) D.y =
        u ^ 3 * (℘'[PeriodPair.ofTau τ] z / 2)) :
    σ D.W.Δ = u ^ 12 * CMBranch.discAn (τ : ℂ) := by
  let P := PeriodPair.ofTau τ
  let U := abVarPunctured E
  have heval : ∀ z ∉ P.lattice, σ D.a * (u ^ 2 * ℘[P] z) + σ D.b =
      u ^ 6 * (P.weierstrassCurve.a₄ * ℘[P] z + P.weierstrassCurve.a₆) := by
    intro z hz
    obtain ⟨hp, hx, hy⟩ := hu z hz
    let p := Φ (fun _ => s * z)
    have aux := congrArg (evHom p.left U hp) D.heq
    simp only [map_pow, map_add, map_mul] at aux
    have hA : evHom p.left U hp (abVarSectionConst E U D.a) = σ D.a :=
      (ev_eq_evHom _ _ hp _).symm.trans (cEvalAt_sectionConst p U hp D.a D.x).2
    have hB : evHom p.left U hp (abVarSectionConst E U D.b) = σ D.b :=
      (ev_eq_evHom _ _ hp _).symm.trans (cEvalAt_sectionConst p U hp D.b D.x).2
    have ex : evHom p.left U hp D.x = u ^ 2 * ℘[P] z := (ev_eq_evHom _ _ hp _).symm.trans hx
    have ey : evHom p.left U hp D.y = u ^ 3 * (℘'[P] z / 2) :=
      (ev_eq_evHom _ _ hp _).symm.trans hy
    rw [hA, hB, ex, ey] at aux
    have hl := (WeierstrassCurve.Affine.equation_iff _ _).mp (P.equation_weierstrassP hz)
    simp only [WeierstrassCurve.toAffine, PeriodPair.weierstrassCurve_a₁,
      PeriodPair.weierstrassCurve_a₂, PeriodPair.weierstrassCurve_a₃, zero_mul, add_zero] at hl
    linear_combination -aux + u ^ 6 * hl
  obtain ⟨z₀, hz₀, h0⟩ := exists_weierstrassP_eq' P 0
  obtain ⟨z₁, hz₁, h1⟩ := exists_weierstrassP_eq' P 1
  have hb : σ D.b = u ^ 6 * P.weierstrassCurve.a₆ := by
    simpa only [h0, mul_zero, zero_add] using heval z₀ hz₀
  have ha : σ D.a * u ^ 2 = u ^ 6 * P.weierstrassCurve.a₄ := by
    have hh := heval z₁ hz₁
    simp only [h1, hb] at hh
    linear_combination hh
  have ha' : σ D.a = u ^ 4 * P.weierstrassCurve.a₄ :=
    mul_right_cancel₀ (pow_ne_zero 2 hu0) (by linear_combination ha)
  rw [← weierstrassCurve_ofTau_Δ, D.W_Δ]
  simp only [map_mul, map_add, map_neg, map_pow, map_ofNat]
  rw [ha', hb]
  change _ = u ^ 12 * P.weierstrassCurve.Δ
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
    PeriodPair.weierstrassCurve_a₃]
  ring

end ZInQ.Contrib.CMHeight62
