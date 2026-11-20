import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAdditionFormula
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-! Addition triples in the original Weierstrass coordinates, with the
usual group law on field points. On the spot (c), tex 1785–1787. -/

noncomputable section

open scoped Classical

open WeierstrassCurve
open scoped WeierstrassCurve.Projective

namespace ZInQ.Manuscript.RC.J0Cusps

private def additionShortChange (E : WeierstrassCurve ℚ) : VariableChange ℚ :=
  ⟨1, -E.b₂ / 12, -E.a₁ / 2, -(E.a₃ + (-E.b₂ / 12) * E.a₁) / 2⟩

private theorem additionShortChange_short (E : WeierstrassCurve ℚ) :
    let W := additionShortChange E • E
    W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := by
  dsimp
  constructor
  · simp [additionShortChange, variableChange_a₁]
    ring
  constructor
  · simp [additionShortChange, variableChange_a₂, b₂]
    ring
  · simp [additionShortChange, variableChange_a₃]
    ring

private def linearCoordinates {R : Type*} [CommRing R] (C : VariableChange R)
    (P : Fin 3 → R) : Fin 3 → R :=
  ![(C.u : R) ^ 2 * P 0 + C.r * P 2,
    (C.u : R) ^ 3 * P 1 + (C.u : R) ^ 2 * C.s * P 0 + C.t * P 2, P 2]

private theorem linearCoordinates_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (C : VariableChange R) (P : Fin 3 → R) :
    g ∘ linearCoordinates C P = linearCoordinates (C.map g) (g ∘ P) := by
  funext i
  fin_cases i <;> simp [linearCoordinates, VariableChange.map]

private theorem linearCoordinates_smul {R : Type*} [CommRing R] (C : VariableChange R)
    (P : Fin 3 → R) (c : R) : linearCoordinates C (c • P) = c • linearCoordinates C P := by
  funext i
  fin_cases i <;> simp [linearCoordinates, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem linearCoordinates_equiv {F : Type*} [Field F] (C : VariableChange F)
    {P Q : Fin 3 → F} (h : P ≈ Q) : linearCoordinates C P ≈ linearCoordinates C Q := by
  obtain ⟨c, e⟩ := h
  change c • Q = P at e
  refine ⟨c, ?_⟩
  change c • linearCoordinates C Q = linearCoordinates C P
  rw [← e, Units.smul_def, Units.smul_def, linearCoordinates_smul]

private theorem linearCoordinates_ne_zero {F : Type*} [Field F] (C : VariableChange F)
    {P : Fin 3 → F} (hP : P ≠ 0) : linearCoordinates C P ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  simp [linearCoordinates] at h0 h1 h2
  rw [h2, mul_zero, add_zero] at h0
  have hx := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ C.u.ne_zero)
  rw [hx, h2, mul_zero, mul_zero, add_zero, add_zero] at h1
  have hy := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ C.u.ne_zero)
  exact hP (funext (fun i => by fin_cases i <;> assumption))

private theorem linearCoordinates_equation {F : Type*} [Field F] (W : WeierstrassCurve F)
    (C : VariableChange F) (P : Fin 3 → F) :
    W.toProjective.Equation (linearCoordinates C P) ↔ (C • W).toProjective.Equation P := by
  by_cases h : P 2 = 0
  · rw [Projective.equation_of_Z_eq_zero (show linearCoordinates C P 2 = 0 from h),
      Projective.equation_of_Z_eq_zero h]
    simp [linearCoordinates, h, mul_eq_zero, C.u.ne_zero]
  · rw [Projective.equation_of_Z_ne_zero (show linearCoordinates C P 2 ≠ 0 from h),
      Projective.equation_of_Z_ne_zero h]
    have hx : linearCoordinates C P 0 / P 2 =
        (C.u : F) ^ 2 * (P 0 / P 2) + C.r := by
      simp [linearCoordinates]
      field_simp
    have hy : linearCoordinates C P 1 / P 2 =
        (C.u : F) ^ 3 * (P 1 / P 2) + (C.u : F) ^ 2 * C.s * (P 0 / P 2) + C.t := by
      simp [linearCoordinates]
      field_simp
    change W.toAffine.Equation (linearCoordinates C P 0 / P 2) (linearCoordinates C P 1 / P 2) ↔ _
    rw [hx, hy, Affine.variableChange_equation W C]

theorem nonsingular_of_equation_ne_zero {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] {P : Fin 3 → F} (hP : W.toProjective.Equation P) (hn : P ≠ 0) :
    W.toProjective.Nonsingular P := by
  by_cases hz : P 2 = 0
  · have hx := Projective.X_eq_zero_of_Z_eq_zero hP hz
    have hy : P 1 ≠ 0 := fun h => hn (funext fun i => by fin_cases i <;> assumption)
    have he : P ≈ (![0, 1, 0] : Fin 3 → F) := by
      let u : Fˣ := (isUnit_iff_ne_zero.mpr hy).unit
      have hu : (u : F) = P 1 := IsUnit.unit_spec _
      refine ⟨u, ?_⟩
      change u • _ = P
      rw [Units.smul_def, hu]
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hx, hz]
    exact (Projective.nonsingular_of_equiv he).2 Projective.nonsingular_zero
  · rw [Projective.nonsingular_of_Z_ne_zero hz]
    exact Affine.equation_iff_nonsingular.mp ((Projective.equation_of_Z_ne_zero hz).mp hP)

private theorem linearCoordinates_toAffine {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (C : VariableChange F) {P : Fin 3 → F}
    (hP : (C • W).toProjective.Nonsingular P)
    (hQ : W.toProjective.Nonsingular (linearCoordinates C P)) :
    Projective.Point.toAffine W.toProjective (linearCoordinates C P) =
      Affine.Point.addEquivVariableChange W C (Projective.Point.toAffine (C • W).toProjective P) := by
  by_cases h : P 2 = 0
  · rw [Projective.Point.toAffine_of_Z_eq_zero (show linearCoordinates C P 2 = 0 from h),
      Projective.Point.toAffine_of_Z_eq_zero h, map_zero]
  · rw [Projective.Point.toAffine_of_Z_ne_zero hQ (show linearCoordinates C P 2 ≠ 0 from h),
      Projective.Point.toAffine_of_Z_ne_zero hP h, Affine.Point.coe_addEquivVariableChange,
      Affine.Point.equivVariableChange_some, Affine.Point.some.injEq]
    constructor <;> simp [linearCoordinates] <;> field_simp <;> ring

/-- The two formulas for multiplication, written with coefficients in the
original rational model. The second is computed in short coordinates and
then changed back to the fixed equation. -/
def additionCoordinates (E : WeierstrassCurve ℚ) {R : Type*} [CommRing R] [Algebra ℚ R]
    (b : Bool) (P Q : Fin 3 → R) : Fin 3 → R :=
  if b then
    let C := (additionShortChange E).map (algebraMap ℚ R)
    let W := ((additionShortChange E • E).baseChange R).toProjective
    linearCoordinates C (symmetricAddition W.a₄ W.a₆
      (linearCoordinates C⁻¹ P) (linearCoordinates C⁻¹ Q))
  else (E.baseChange R).toProjective.addXYZ P Q

set_option maxHeartbeats 1000000 in
/-- Every nonsingular pair lies in the domain of at least one of the two
polynomial triples. Each nonzero value satisfies the original projective
equation and computes the usual group sum. -/
theorem additionCoordinates_fields (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {F : Type*} [Field F] [Algebra ℚ F] {P Q : Fin 3 → F}
    (hP : (E.baseChange F).toProjective.Nonsingular P)
    (hQ : (E.baseChange F).toProjective.Nonsingular Q) :
    (∃ b : Bool, additionCoordinates E b P Q ≠ 0) ∧
      ∀ b : Bool, additionCoordinates E b P Q ≠ 0 →
        (E.baseChange F).toProjective.Equation (additionCoordinates E b P Q) ∧
          Projective.Point.toAffine (E.baseChange F).toProjective (additionCoordinates E b P Q) =
            Projective.Point.toAffine (E.baseChange F).toProjective P +
            Projective.Point.toAffine (E.baseChange F).toProjective Q := by
  classical
  let C := (additionShortChange E).map (algebraMap ℚ F)
  let V := E.baseChange F
  let U := C • V
  have hU : U = (additionShortChange E • E).baseChange F :=
    map_variableChange _ _ _
  let P' := linearCoordinates C⁻¹ P
  let Q' := linearCoordinates C⁻¹ Q
  have hp : U.toProjective.Nonsingular P' := by
    apply nonsingular_of_equation_ne_zero U _ (linearCoordinates_ne_zero _ (projectiveNonsingular_ne_zero hP))
    exact (linearCoordinates_equation U C⁻¹ P).2 (by simpa only [U, inv_smul_smul] using hP.1)
  have hq : U.toProjective.Nonsingular Q' := by
    apply nonsingular_of_equation_ne_zero U _ (linearCoordinates_ne_zero _ (projectiveNonsingular_ne_zero hQ))
    exact (linearCoordinates_equation U C⁻¹ Q).2 (by simpa only [U, inv_smul_smul] using hQ.1)
  have ⟨h₁, h₂, h₃⟩ := additionShortChange_short E
  have h₁' : U.a₁ = 0 := by
    rw [hU]
    simpa using congrArg (algebraMap ℚ F) h₁
  have h₂' : U.a₂ = 0 := by
    rw [hU]
    simpa using congrArg (algebraMap ℚ F) h₂
  have h₃' : U.a₃ = 0 := by
    rw [hU]
    simpa using congrArg (algebraMap ℚ F) h₃
  let S := symmetricAddition U.a₄ U.a₆ P' Q'
  have htrue : additionCoordinates E true P Q = linearCoordinates C S := by
    simp only [additionCoordinates, ite_true, hU, C, S, P', Q']
  have hfalse : additionCoordinates E false P Q = V.toProjective.addXYZ P Q := rfl
  have hsec {A B : Fin 3 → F} {W : Projective F} (h : A ≈ B) : W.addXYZ A B = 0 := by
    obtain ⟨u, e⟩ := h
    change u • B = A at e
    rw [← e, Units.smul_def,
      ← congrArg (fun t => W.addXYZ ((u : F) • B) t) (one_smul F B),
      Projective.addXYZ_smul, Projective.addXYZ_self]
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  have hcomp (R : Fin 3 → F) (hR : V.toProjective.Nonsingular R)
      (hR' : U.toProjective.Nonsingular (linearCoordinates C⁻¹ R)) :
      Affine.Point.addEquivVariableChange V C
        (Projective.Point.toAffine U.toProjective (linearCoordinates C⁻¹ R)) =
          Projective.Point.toAffine V.toProjective R := by
    have hInv : linearCoordinates C (linearCoordinates C⁻¹ R) = R := by
      have hc : C.u = 1 := by simp [C, additionShortChange, VariableChange.map]
      funext i
      fin_cases i <;> simp [linearCoordinates, VariableChange.inv_def, hc] <;> ring
    have hf : V.toProjective.Nonsingular (linearCoordinates C (linearCoordinates C⁻¹ R)) :=
      Eq.mpr (congrArg V.toProjective.Nonsingular hInv) hR
    calc
      _ = Projective.Point.toAffine V.toProjective (linearCoordinates C (linearCoordinates C⁻¹ R)) :=
        (linearCoordinates_toAffine V C hR' hf).symm
      _ = _ := congrArg (Projective.Point.toAffine V.toProjective) hInv
  constructor
  · by_cases h : P ≈ Q
    · refine ⟨true, ?_⟩
      rw [htrue]
      apply linearCoordinates_ne_zero
      exact (projectiveAddition_cover U.toProjective h₁' h₂' h₃' hp hq).resolve_left
        (not_not_intro (hsec (linearCoordinates_equiv C⁻¹ h)))
    · refine ⟨false, ?_⟩
      rw [hfalse, ← Projective.add_of_not_equiv h]
      exact projectiveNonsingular_ne_zero (V.toProjective.nonsingular_add hP hQ)
  · rintro (_ | _) hn
    · rw [hfalse] at hn ⊢
      have h : ¬P ≈ Q := fun h => hn (hsec h)
      rw [← Projective.add_of_not_equiv h]
      exact ⟨(V.toProjective.nonsingular_add hP hQ).1, Projective.Point.toAffine_add hP hQ⟩
    · rw [htrue] at hn ⊢
      obtain ⟨c, hc⟩ := symmetricAddition_eq_smul_add U.toProjective h₁' h₂' h₃' hp hq
      change S = c • U.toProjective.add P' Q' at hc
      have hcn : c ≠ 0 := by
        intro h
        apply hn
        rw [hc, h, zero_smul]
        funext i
        fin_cases i <;> simp [linearCoordinates]
      have hs : U.toProjective.Nonsingular S := hc ▸
        (Projective.nonsingular_smul _ (isUnit_iff_ne_zero.mpr hcn)).2 (U.toProjective.nonsingular_add hp hq)
      have he := (linearCoordinates_equation V C S).2 hs.1
      have hf := nonsingular_of_equation_ne_zero V he hn
      refine ⟨he, ?_⟩
      rw [linearCoordinates_toAffine V C hs hf]
      have ht : Projective.Point.toAffine U.toProjective S =
          Projective.Point.toAffine U.toProjective P' + Projective.Point.toAffine U.toProjective Q' := by
        rw [hc, Projective.Point.toAffine_smul _ (isUnit_iff_ne_zero.mpr hcn), Projective.Point.toAffine_add hp hq]
      rw [ht, map_add, hcomp P hP hp, hcomp Q hQ hq]


/-- The formulas commute with coefficient maps, including quotient and
localization maps on the scheme charts. -/
theorem additionCoordinates_map (E : WeierstrassCurve ℚ) {R S : Type*}
    [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    (g : R →+* S) (b : Bool) (P Q : Fin 3 → R) :
    g ∘ additionCoordinates E b P Q = additionCoordinates E b (g ∘ P) (g ∘ Q) := by
  have hr : g.comp (algebraMap ℚ R) = algebraMap ℚ S := Subsingleton.elim _ _
  have hw (V : WeierstrassCurve ℚ) : (V.baseChange R).map g = V.baseChange S := by
    change (V.map (algebraMap ℚ R)).map g = V.map (algebraMap ℚ S)
    rw [V.map_map, hr]
  have hc : ((additionShortChange E).map (algebraMap ℚ R)).map g =
      (additionShortChange E).map (algebraMap ℚ S) := by
    rw [VariableChange.map_map, hr]
  have hi : (((additionShortChange E).map (algebraMap ℚ R))⁻¹).map g =
      (((additionShortChange E).map (algebraMap ℚ S)))⁻¹ := by
    change (VariableChange.mapHom g) _ = _
    rw [map_inv]
    exact congrArg Inv.inv hc
  cases b
  · simpa only [additionCoordinates, Bool.false_eq_true, ite_false, hw E] using
      (Projective.map_addXYZ (W' := (E.baseChange R).toProjective) g P Q).symm
  · simp only [additionCoordinates, ite_true, linearCoordinates_map,
      symmetricAddition_map, hc, hi]
    rw [← show ((additionShortChange E • E).baseChange R).map g =
      (additionShortChange E • E).baseChange S from hw _]
    rfl



end ZInQ.Manuscript.RC.J0Cusps
