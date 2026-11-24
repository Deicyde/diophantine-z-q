import ZInQKernel.Contrib.OneProof.CMjBridges
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry
open scoped UpperHalfPlane _root_.PeriodPair
open _root_.ZInQ.LeafPush2 (CPts cEvalAt IsUniformization)

private noncomputable def sectionConst {L : Type} [Field L] (A : PkgI3.AbVar L)
    (U : A.X.left.Opens) (a : L) : Γ(A.X.left, U) :=
  A.X.hom.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a)

private noncomputable def sectionEval {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) :
    Γ(A.X.left, U) →+* ℂ :=
  ((p.left.appLE U ⊤ hp) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

private theorem sectionEval_const {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (a : L) :
    sectionEval p U hp (sectionConst A U a) = σ a := by
  let q : Spec (CommRingCat.of ℂ) ⟶ A.X.left := p.left
  let f := Spec.map (CommRingCat.ofHom σ)
  have h := Scheme.Hom.appLE_comp_appLE_assoc q A.X.hom ⊤ U ⊤ (by simp) hp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
  have hw : q ≫ A.X.hom = f := Over.w p
  rw [hw] at h
  have hTop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
  rw [hTop, Scheme.ΓSpecIso_naturality] at h
  apply_fun (fun f : Γ(Spec (CommRingCat.of L), ⊤) ⟶ CommRingCat.of ℂ =>
    f ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a)) at h
  exact h.trans (by simp)

/-- Short equation coordinates on the actual scheme, compared along the specified
period map. The parameter `z` is normalized to the lattice `ℤ + τℤ`; the
original period map takes `s * z`. The independent scale `u` is the change of
normalization of the short Weierstrass coordinates. -/
def HasShortWeierstrassComparison {L : Type} [Field L] (A : PkgI3.AbVar L)
    (σ : L →+* ℂ) (τ : ℍ) (s : ℂ) (Φ : (Fin 1 → ℂ) → CPts A σ) : Prop :=
  let P := PeriodPair.ofTau τ
  ∃ (U : A.X.left.Opens) (x y : Γ(A.X.left, U)) (a b : L) (u : ℂ), u ≠ 0 ∧
    y ^ 2 = x ^ 3 + sectionConst A U a * x + sectionConst A U b ∧
    ∀ z ∉ P.lattice,
      let p := Φ (fun _ => s * z)
      (⊤ ≤ p.left ⁻¹ᵁ U) ∧
        cEvalAt p U x = u ^ 2 * ℘[P] z ∧
        cEvalAt p U y = u ^ 3 * (℘'[P] z / 2)

/-- The remaining glue, restricted to the CM curves of the row. For any period
in the question, find a witness to that very period whose complex point map
identifies two regular functions over the field of definition with the
short equation coordinates of the normalized lattice. -/
def CMPeriodShortWeierstrassComparison : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k),
      IsImagQuadOrder k R → IsCMBy E k R →
      ∀ (σ : L →+* ℂ) (τ : ℍ), IsPeriodAt (LeafAdopt.abVarEquiv L E) σ τ →
        let A := LeafAdopt.abVarEquiv L E
        ∃ (Λ : Submodule ℤ (Fin 1 → ℂ)) (Φ : (Fin 1 → ℂ) → CPts A σ),
          IsUniformization σ Λ Φ ∧
          ∃ s : ℂ, s ≠ 0 ∧ (∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ))) ∧
            HasShortWeierstrassComparison A σ τ s Φ

private theorem exists_weierstrassP_eq (P : PeriodPair) (x : ℂ) :
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

/-- The section equation determines both complex coefficients after evaluation
on the actual lattice parametrization. Substituting them into the Weierstrass
formula cancels the coordinate scale from j. -/
theorem modularJ_mem_range_of_shortCoordinates {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} {τ : ℍ} {s : ℂ} {Φ : (Fin 1 → ℂ) → CPts A σ}
    (h : HasShortWeierstrassComparison A σ τ s Φ) : modularJ τ ∈ Set.range σ := by
  obtain ⟨U, x, y, a, b, u, hu, hEq, hcoords⟩ := h
  let P := PeriodPair.ofTau τ
  have heval : ∀ z ∉ P.lattice, σ a * (u ^ 2 * ℘[P] z) + σ b =
      u ^ 6 * (P.weierstrassCurve.a₄ * ℘[P] z + P.weierstrassCurve.a₆) := by
    intro z hz
    obtain ⟨hp, hx, hy⟩ := hcoords z hz
    let p := Φ (fun _ => s * z)
    have aux := congrArg (sectionEval p U hp) hEq
    simp only [map_pow, map_add, map_mul, sectionEval_const] at aux
    change cEvalAt p U x = _ at hx
    change cEvalAt p U y = _ at hy
    rw [cEvalAt, dite_eq_left hp] at hx hy
    change sectionEval p U hp x = _ at hx
    change sectionEval p U hp y = _ at hy
    rw [hx, hy] at aux
    have hl := (WeierstrassCurve.Affine.equation_iff _ _).mp (P.equation_weierstrassP hz)
    simp only [WeierstrassCurve.toAffine, PeriodPair.weierstrassCurve_a₁,
      PeriodPair.weierstrassCurve_a₂, PeriodPair.weierstrassCurve_a₃, zero_mul, add_zero] at hl
    linear_combination -aux + u ^ 6 * hl
  obtain ⟨z₀, hz₀, h0⟩ := exists_weierstrassP_eq P 0
  obtain ⟨z₁, hz₁, h1⟩ := exists_weierstrassP_eq P 1
  have hb : σ b = u ^ 6 * P.weierstrassCurve.a₆ := by
    simpa only [h0, mul_zero, zero_add] using heval z₀ hz₀
  have ha : σ a = u ^ 4 * P.weierstrassCurve.a₄ := by
    have hh := heval z₁ hz₁
    simp only [h1, mul_one, hb] at hh
    apply mul_right_cancel₀ (pow_ne_zero 2 hu)
    linear_combination hh
  let W : WeierstrassCurve L := ⟨0, 0, 0, a, b⟩
  have hMap : W.map σ = (⟨(Units.mk0 u hu)⁻¹, 0, 0, 0⟩ :
      WeierstrassCurve.VariableChange ℂ) • P.weierstrassCurve := by
    ext <;> simp [W, WeierstrassCurve.map, ha, hb, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆]
  let : P.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr P.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  let : (W.map σ).IsElliptic := hMap ▸ (inferInstance :
    ((⟨(Units.mk0 u hu)⁻¹, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ℂ) •
      P.weierstrassCurve).IsElliptic)
  let : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr fun hW => (W.map σ).Δ'.ne_zero (by
    rw [WeierstrassCurve.coe_Δ', WeierstrassCurve.map_Δ, hW, map_zero])⟩
  refine ⟨W.j, (weierstrass_j_map W σ).trans ?_⟩
  let C : WeierstrassCurve.VariableChange ℂ := ⟨(Units.mk0 u hu)⁻¹, 0, 0, 0⟩
  calc
    (W.map σ).j = (C • P.weierstrassCurve).j := by
      simp only [WeierstrassCurve.j_eq, hMap, C]
    _ = P.weierstrassCurve.j := P.weierstrassCurve.variableChange_j C
    _ = modularJ τ := by
      rw [WeierstrassCurve.j_eq, ← div_eq_inv_mul]
      exact P.jLattice_eq_c₄_pow_three_div_Δ.symm

/-- A comparison on the same scheme and at the given period suffices for j descent. -/
theorem cmPeriodJDescends_of_shortWeierstrassComparison (h : CMPeriodShortWeierstrassComparison) :
    CMPeriodJDescends := by
  intro L _ _ E hE k _ _ R hR hCM σ τ hτ
  obtain ⟨_, _, _, _, _, _, hc⟩ := h L E hE k R hR hCM σ τ hτ
  exact modularJ_mem_range_of_shortCoordinates hc

/-- Fowler's equality supplies the live row once the coordinate comparison is proved. -/
theorem cmjDegree_of_print_of_shortWeierstrassComparison (h : CMPeriodShortWeierstrassComparison) :
    CMjDegreePrint → CMjDegree :=
  cmjDegree_of_print_of_periodJDescends (cmPeriodJDescends_of_shortWeierstrassComparison h)

#print axioms sectionEval_const
#print axioms exists_weierstrassP_eq
#print axioms modularJ_mem_range_of_shortCoordinates
#print axioms cmPeriodJDescends_of_shortWeierstrassComparison
#print axioms cmjDegree_of_print_of_shortWeierstrassComparison

end HDec.CMBranch.CMjBridges
