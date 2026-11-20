import ZInQKernel.Contrib.OneProof.JDescent
import ZInQKernel.Contrib.OneProof.JDescent2Analytic

/-! The remaining scheme-to-pole comparison for CM period descent. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped UpperHalfPlane _root_.PeriodPair
open _root_.ZInQ.LeafPush2 (CPts cDom cEvalAt IsUniformization)

private noncomputable def modelConst {L : Type} [Field L] (A : PkgI3.AbVar L)
    (U : A.X.left.Opens) (a : L) : Γ(A.X.left, U) :=
  A.X.hom.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a)

private noncomputable def modelEval {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) :
    Γ(A.X.left, U) →+* ℂ :=
  ((p.left.appLE U ⊤ hp) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

private theorem modelEval_const {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (a : L) :
    modelEval p U hp (modelConst A U a) = σ a := by
  let q : Spec (CommRingCat.of ℂ) ⟶ A.X.left := p.left
  let f := Spec.map (CommRingCat.ofHom σ)
  have h := Scheme.Hom.appLE_comp_appLE_assoc q A.X.hom ⊤ U ⊤ (by simp) hp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
  have hw : q ≫ A.X.hom = f := Over.w p
  rw [hw] at h
  have hTop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
  rw [hTop, Scheme.ΓSpecIso_naturality] at h
  apply_fun (fun g : Γ(Spec (CommRingCat.of L), ⊤) ⟶ CommRingCat.of ℂ =>
    g ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a)) at h
  exact h.trans (by simp)

/-- The short cubic and one pole on the actual curve. No comparison with
the lattice coordinates is required in this statement. -/
def HasShortCoordinatesWithDoublePole {L : Type} [Field L] (A : PkgI3.AbVar L)
    (σ : L →+* ℂ) (τ : ℍ) (s : ℂ) (Φ : (Fin 1 → ℂ) → CPts A σ) : Prop :=
  ∃ (U : A.X.left.Opens) (x y : Γ(A.X.left, U)) (a b : L),
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve L).Δ ≠ 0 ∧
    y ^ 2 = x ^ 3 + modelConst A U a * x + modelConst A U b ∧
    (∀ z ∉ (PeriodPair.ofTau τ).lattice, ⊤ ≤ (Φ (fun _ => s * z)).left ⁻¹ᵁ U) ∧
    (∀ z, cEvalAt (Φ (fun _ => s * (-z))) U x = cEvalAt (Φ (fun _ => s * z)) U x) ∧
    HasDoublePoleAtZero (fun z => cEvalAt (Φ (fun _ => s * z)) U x)

/-- The remaining glue on the CM curves of the live row. It is a section and
local-parameter problem over the field of definition; the lattice coordinate
normalization is supplied by the theorem below. -/
def CMPeriodShortCoordinatesDoublePole : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k),
      IsImagQuadOrder k R → IsCMBy E k R →
      ∀ (σ : L →+* ℂ) (τ : ℍ), IsPeriodAt (LeafAdopt.abVarEquiv L E) σ τ →
        let A := LeafAdopt.abVarEquiv L E
        ∃ (Λ : Submodule ℤ (Fin 1 → ℂ)) (Φ : (Fin 1 → ℂ) → CPts A σ),
          IsUniformization σ Λ Φ ∧
          ∃ s : ℂ, s ≠ 0 ∧ (∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ))) ∧
            HasShortCoordinatesWithDoublePole A σ τ s Φ

/-- Only the even x-coordinate needs its pole certified. Holomorphy on the
punctured plane and the equation force both evaluations, on the same period
map and with the same scale. -/
theorem shortWeierstrassComparison_of_doublePole {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} {τ : ℍ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {Φ : (Fin 1 → ℂ) → CPts A σ} {s : ℂ}
    (hΦ : IsUniformization σ Λ Φ)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    (h : HasShortCoordinatesWithDoublePole A σ τ s Φ) :
    HasShortWeierstrassComparison A σ τ s Φ := by
  obtain ⟨U, x, y, a, b, hΔ, heq, hU, hEven, hPole⟩ := h
  let P := PeriodPair.ofTau τ
  let v : ℂ → (Fin 1 → ℂ) := fun z _ => s * z
  let ev (f : Γ(A.X.left, U)) (z : ℂ) := cEvalAt (Φ (v z)) U f
  have han (f : Γ(A.X.left, U)) : AnalyticOnNhd ℂ (ev f) P.latticeᶜ := by
    apply DifferentiableOn.analyticOnNhd _ P.isClosed_lattice.isOpen_compl
    have hv : Differentiable ℂ v := by
      apply differentiable_pi.mpr
      intro i
      change Differentiable ℂ (fun z : ℂ => s * z)
      fun_prop
    exact (hΦ.2.2.2.2 U f).comp hv.differentiableOn (fun z hz => hU z hz)
  have hPer (l : P.lattice) : Function.Periodic (ev x) l := by
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
    change cEvalAt (Φ (v (z + l))) U x = cEvalAt (Φ (v z)) U x
    have hUnit : Φ (v z) * (1 : CPts A σ) = Φ (v z) := mul_one _
    rw [hadd, hΦ.1, (hΦ.2.1 _).mpr hvl, hUnit]
  have hCubic (z : ℂ) (hz : z ∉ P.lattice) :
      ev y z ^ 2 = ev x z ^ 3 + σ a * ev x z + σ b := by
    have hp : ⊤ ≤ (Φ (v z)).left ⁻¹ᵁ U := hU z hz
    have hq := congrArg (modelEval (Φ (v z)) U hp) heq
    simp only [map_pow, map_add, map_mul, modelEval_const] at hq
    simp only [ev, cEvalAt, dite_eq_left hp]
    exact hq
  have hSimple (r : ℂ) (hr : r ^ 3 + σ a * r + σ b = 0) : 3 * r ^ 2 + σ a ≠ 0 := by
    let W : WeierstrassCurve L := ⟨0, 0, 0, a, b⟩
    have hW : (W.map σ).Δ ≠ 0 := by rw [WeierstrassCurve.map_Δ]; exact (map_ne_zero σ).mpr hΔ
    have he : (W.map σ).toAffine.Equation r 0 := by
      rw [WeierstrassCurve.Affine.equation_iff]
      simpa [W, WeierstrassCurve.map] using hr.symm
    have hn := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hW).mp he
    have h := (WeierstrassCurve.Affine.nonsingular_iff' r 0).mp hn
    intro hz
    rcases h.2 with h₁ | h₂
    · apply h₁
      change σ (0 : L) * 0 - (3 * r ^ 2 + 2 * σ 0 * r + σ a) = 0
      simp [hz]
    · apply h₂
      change 2 * 0 + σ (0 : L) * r + σ 0 = 0
      simp
  obtain ⟨u, hu, hCoords⟩ := shortCubic_coordinates_of_doublePole P (han x) (han y) hPer
    hEven hPole hCubic hSimple
  refine ⟨U, x, y, a, b, u, hu, heq, fun z hz => ?_⟩
  exact ⟨hU z hz, hCoords z hz⟩

/-- The local pole comparison implies the original comparison for the CM row. -/
theorem cmPeriodShortWeierstrassComparison_of_doublePole (h : CMPeriodShortCoordinatesDoublePole) :
    CMPeriodShortWeierstrassComparison := by
  intro L _ _ E hE k _ _ R hR hCM σ τ hτ
  obtain ⟨Λ, Φ, hΦ, s, hs, hΛ, hcoords⟩ := h L E hE k R hR hCM σ τ hτ
  exact ⟨Λ, Φ, hΦ, s, hs, hΛ, shortWeierstrassComparison_of_doublePole hΦ hΛ hcoords⟩

/-- The live row follows from Fowler's printed equality and the remaining
section and pole comparison. -/
theorem cmjDegree_of_print_of_doublePole (h : CMPeriodShortCoordinatesDoublePole) :
    CMjDegreePrint → CMjDegree :=
  cmjDegree_of_print_of_shortWeierstrassComparison
    (cmPeriodShortWeierstrassComparison_of_doublePole h)

#print axioms modelEval_const
#print axioms shortWeierstrassComparison_of_doublePole
#print axioms cmPeriodShortWeierstrassComparison_of_doublePole
#print axioms cmjDegree_of_print_of_doublePole

end HDec.CMBranch.CMjBridges
