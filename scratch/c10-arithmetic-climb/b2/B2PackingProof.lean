/-
GIVEN ACTUAL B2 PACKING — PROOF SOURCE v1, UNCOMPILED.

Frozen target source7a88710e...; independent typed-only ACK52a0fa55...
was read before this proof source. The theorem below repeats the complete
OLD-frozen target. All new declarations have selected axiom reports in the
separate check source. Executor is sole ParentA, not this source-author child.

No accepted source/target changes, Finite GQ, assumed finite-range Fact,
normalized replacement, new coefficient value/place or topology constructor.
The quadratic-fibre route and existing FCF/Units/MulChar/LC suppliers are reused.
-/

import B2PackingTarget

noncomputable section

namespace ClimbB2CoefficientPacking

open Polynomial in
/-- Existing finite roots of the nonzero fixed quadratic, including c=0. -/
theorem finite_square_fibre (c : Qbar) : {z : Qbar | z ^ 2 = c}.Finite := by
  have hp : (X ^ 2 - C c : Qbar[X]) ≠ 0 :=
    X_pow_sub_C_ne_zero (by decide : 0 < 2) c
  refine (finite_setOfPred_isRoot hp).subset ?_
  intro z (hz : z ^ 2 = c)
  show IsRoot (X ^ 2 - C c) z
  rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, hz, sub_self]

/-- Only the original modular domain is finite, using its actual NeZero. -/
theorem characterValues_finite {N : ℕ} [NeZero N]
    (χ₀ : DirichletCharacter Qbar N) : (characterValues χ₀).Finite :=
  Set.finite_range _

/-- The original unit-square equation at every actual GQ element. -/
theorem beta_sq_eq {N : ℕ} [NeZero N]
    (χ₀ : DirichletCharacter Qbar N) (β₀ : GQ → Qbarˣ)
    (hβsq : ∀ g, β₀ g ^ 2 = ClimbBetaExpected.galCharacter χ₀ g) (g : GQ) :
    (β₀ g : Qbar) ^ 2 = χ₀ (GlueDescent.B2Q.cyc N g : ZMod N) := by
  rw [← Units.val_pow_eq_pow_val, hβsq g]
  exact MulChar.coe_toUnitHom χ₀ (GlueDescent.B2Q.cyc N g)

/-- Bound ALL supplied beta values by finite fibres, not a finite GQ sample. -/
theorem betaValues_finite {N : ℕ} [NeZero N]
    (χ₀ : DirichletCharacter Qbar N) (β₀ : GQ → Qbarˣ)
    (hβsq : ∀ g, β₀ g ^ 2 = ClimbBetaExpected.galCharacter χ₀ g) :
    (betaValues β₀).Finite := by
  refine ((characterValues_finite χ₀).biUnion fun c _ => finite_square_fibre c).subset ?_
  rintro _ ⟨g, rfl⟩
  exact Set.mem_iUnion₂_of_mem
    (i := χ₀ (GlueDescent.B2Q.cyc N g : ZMod N)) ⟨_, rfl⟩
    (beta_sq_eq χ₀ β₀ hβsq g)

/-- Bound ALL supplied sign values at all pairs by the nonzero X²−1. -/
theorem epsilonValues_finite (ε₀ : GQ → GQ → Qbarˣ)
    (hε : GlueDescent.B2.IsSignCocycle ε₀) : (epsilonValues ε₀).Finite := by
  obtain ⟨_, hsq, _⟩ := hε
  refine (finite_square_fibre 1).subset ?_
  rintro _ ⟨p, rfl⟩
  show (ε₀ p.1 p.2 : Qbar) ^ 2 = 1
  rw [← Units.val_pow_eq_pow_val, hsq p.1 p.2, Units.val_one]

/-- Unit coercion is injective; the index type is not assumed finite. -/
theorem range_units_finite {α : Type*} {f : α → Qbarˣ}
    (h : (Set.range fun a => (f a : Qbar)).Finite) : (Set.range f).Finite := by
  refine (h.preimage Units.val_injective.injOn).subset ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨a, rfl⟩

/-- Complete frozen GIVEN-B2 target, not a new self-defined goal predicate. -/
theorem packGivenActualB2 :
  (∀ (N : ℕ) [NeZero N] (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ)
    (_hε : GlueDescent.B2.IsSignCocycle ε₀)
    (_hβlc : IsLocallyConstant β₀)
    (_hβsq : ∀ g : GQ, β₀ g ^ 2 = ClimbBetaExpected.galCharacter χ₀ g)
    (_hβco : ∀ g h : GQ, β₀ g * β₀ h = ε₀ g h * β₀ (g * h))
    (ρ : Qbar →ₐ[ℚ] ℂ),
    let S : Set Qbar := coefficients χ₀ ε₀ β₀
    let E : IntermediateField ℚ Qbar := coefficientField χ₀ ε₀ β₀
    let ιE : E →ₐ[ℚ] Qbar := fieldInclusion χ₀ ε₀ β₀
    let ρE : E →ₐ[ℚ] ℂ := restrictedComplexPlace χ₀ ε₀ β₀ ρ
    let uι : Eˣ →* Qbarˣ := unitInclusion χ₀ ε₀ β₀
    let uρ : Eˣ →* ℂˣ := unitComplexPlace χ₀ ε₀ β₀ ρ
    (characterValues χ₀).Finite ∧
    (betaValues β₀).Finite ∧ (Set.range β₀).Finite ∧
    (epsilonValues ε₀).Finite ∧ (Set.range (Function.uncurry ε₀)).Finite ∧
    S.Finite ∧
    FiniteDimensional ℚ E ∧ NumberField E ∧
    (S ⊆ (E : Set Qbar)) ∧
    (∀ F : IntermediateField ℚ Qbar, S ⊆ (F : Set Qbar) → E ≤ F) ∧
    (ρE = ρ.comp ιE) ∧ (∀ x : E, ρE x = ρ (ιE x)) ∧
    (uρ = (ClimbBetaExpected.unitPlace ρ).comp uι) ∧
    (ρE.fieldRange = E.map ρ) ∧
    (Set.range (fun x : E => ρE x) = ρ '' (E : Set Qbar)) ∧
    ∃ (χE : DirichletCharacter E N) (βE : GQ → Eˣ) (εE : GQ → GQ → Eˣ),
      (∀ a : ZMod N,
        χE a = characterLift χ₀ ε₀ β₀ a ∧
        ιE (χE a) = χ₀ a ∧ ρE (χE a) = ρ (χ₀ a)) ∧
      (∀ g : GQ,
        (βE g : E) = betaLift χ₀ ε₀ β₀ g ∧
        uι (βE g) = β₀ g ∧ ιE (βE g : E) = (β₀ g : Qbar) ∧
        uρ (βE g) = ClimbBetaExpected.unitPlace ρ (β₀ g) ∧
        ρE (βE g : E) = ρ (β₀ g : Qbar)) ∧
      (∀ g h : GQ,
        (εE g h : E) = epsilonLift χ₀ ε₀ β₀ g h ∧
        uι (εE g h) = ε₀ g h ∧ ιE (εE g h : E) = (ε₀ g h : Qbar) ∧
        uρ (εE g h) = ClimbBetaExpected.unitPlace ρ (ε₀ g h) ∧
        ρE (εE g h : E) = ρ (ε₀ g h : Qbar)) ∧
      (χE.ringHomComp ιE.toRingHom = χ₀) ∧
      (χE.ringHomComp ρE.toRingHom = χ₀.ringHomComp ρ.toRingHom) ∧
      (orderOf χE = orderOf χ₀) ∧
      (∀ a : ZMod N, ¬ IsUnit a → χE a = 0) ∧
      (Set.range (fun a : ZMod N => ρE (χE a)) =
        Set.range (fun a : ZMod N => ρ (χ₀ a))) ∧
      (Set.range (fun g : GQ => uρ (βE g)) =
        Set.range (fun g : GQ => ClimbBetaExpected.unitPlace ρ (β₀ g))) ∧
      (Set.range (fun p : GQ × GQ => uρ (εE p.1 p.2)) =
        Set.range (fun p : GQ × GQ => ClimbBetaExpected.unitPlace ρ (ε₀ p.1 p.2))) ∧
      (Set.range (fun g : GQ => ρE (βE g : E)) =
        Set.range (fun g : GQ => ρ (β₀ g : Qbar))) ∧
      (Set.range (fun p : GQ × GQ => ρE (εE p.1 p.2 : E)) =
        Set.range (fun p : GQ × GQ => ρ (ε₀ p.1 p.2 : Qbar))) ∧
      (∀ g : GQ, βE g ^ 2 = χE.toUnitHom (GlueDescent.B2Q.cyc N g)) ∧
      (∀ g h : GQ, βE g * βE h = εE g h * βE (g * h)) ∧
      (∀ g h : GQ, εE g h ^ 2 = 1) ∧
      (∀ x y z : GQ, εE (x * y) z * εE x y = εE y z * εE x (y * z)) ∧
      ((ε₀ 1 1 = 1) → βE 1 = 1) ∧
      IsLocallyConstant βE ∧ GlueDescent.B2.IsSignCocycle εE) := by
  intro N _ χ₀ ε₀ β₀ hε hβlc hβsq hβco ρ
  let S : Set Qbar := coefficients χ₀ ε₀ β₀
  let E : IntermediateField ℚ Qbar := coefficientField χ₀ ε₀ β₀
  let j : E →ₐ[ℚ] Qbar := fieldInclusion χ₀ ε₀ β₀
  let ju : Eˣ →* Qbarˣ := unitInclusion χ₀ ε₀ β₀
  let ρE : E →ₐ[ℚ] ℂ := restrictedComplexPlace χ₀ ε₀ β₀ ρ
  let uρ : Eˣ →* ℂˣ := unitComplexPlace χ₀ ε₀ β₀ ρ
  have hj : Function.Injective j := j.injective
  have hju : Function.Injective ju :=
    Units.map_injective (f := j.toRingHom.toMonoidHom) hj

  have hχfin : (characterValues χ₀).Finite := characterValues_finite χ₀
  have hβfin : (betaValues β₀).Finite := betaValues_finite χ₀ β₀ hβsq
  have hεfin : (epsilonValues ε₀).Finite := epsilonValues_finite ε₀ hε
  have hβu : (Set.range β₀).Finite := range_units_finite (f := β₀) hβfin
  have hεu : (Set.range (Function.uncurry ε₀)).Finite :=
    range_units_finite (f := Function.uncurry ε₀) hεfin
  have hS : S.Finite := (hχfin.union hβfin).union hεfin
  have hfield := ClimbFiniteCoefficientField.finiteSet_numberField_fixedPlace S hS ρ
  obtain ⟨hfd, hnf, hinc, hmin, _, hfr⟩ := hfield
  have hImage : Set.range (fun x : E => ρE x) = ρ '' (E : Set Qbar) := by
    exact (ClimbFiniteCoefficientField.restrictedRingPlace_compatible S ρ.toRingHom).2.2

  have hc (a : ZMod N) : j (characterLift χ₀ ε₀ β₀ a) = χ₀ a := rfl
  have hb (g : GQ) : j (betaLift χ₀ ε₀ β₀ g) = (β₀ g : Qbar) := rfl
  have he (g h : GQ) : j (epsilonLift χ₀ ε₀ β₀ g h) = (ε₀ g h : Qbar) := rfl
  have hbne (g : GQ) : betaLift χ₀ ε₀ β₀ g ≠ 0 := by
    intro hz
    have hz' := congrArg j hz
    rw [hb g, map_zero] at hz'
    exact (β₀ g).ne_zero hz'
  have hene (g h : GQ) : epsilonLift χ₀ ε₀ β₀ g h ≠ 0 := by
    intro hz
    have hz' := congrArg j hz
    rw [he g h, map_zero] at hz'
    exact (ε₀ g h).ne_zero hz'
  let βE : GQ → Eˣ := fun g => Units.mk0 (betaLift χ₀ ε₀ β₀ g) (hbne g)
  let εE : GQ → GQ → Eˣ := fun g h => Units.mk0 (epsilonLift χ₀ ε₀ β₀ g h) (hene g h)
  have hbE (g : GQ) : (βE g : E) = betaLift χ₀ ε₀ β₀ g := rfl
  have heE (g h : GQ) : (εE g h : E) = epsilonLift χ₀ ε₀ β₀ g h := rfl
  have hbU (g : GQ) : ju (βE g) = β₀ g := by
    apply Units.ext
    change j (betaLift χ₀ ε₀ β₀ g) = (β₀ g : Qbar)
    exact hb g
  have heU (g h : GQ) : ju (εE g h) = ε₀ g h := by
    apply Units.ext
    change j (epsilonLift χ₀ ε₀ β₀ g h) = (ε₀ g h : Qbar)
    exact he g h
  let χE : DirichletCharacter E N :=
    { toFun := characterLift χ₀ ε₀ β₀
      map_one' := by
        apply hj
        simp only [hc, map_one]
      map_mul' := by
        intro a b
        apply hj
        simp only [map_mul, hc]
      map_nonunit' := by
        intro a ha
        apply hj
        simp only [hc, map_zero]
        exact χ₀.map_nonunit ha }
  have hχliteral (a : ZMod N) : χE a = characterLift χ₀ ε₀ β₀ a := rfl
  have hχ (a : ZMod N) : j (χE a) = χ₀ a := hc a
  have hχU (a : (ZMod N)ˣ) : ju (χE.toUnitHom a) = χ₀.toUnitHom a := by
    apply Units.ext
    change j (χE (a : ZMod N)) = χ₀ (a : ZMod N)
    exact hχ (a : ZMod N)
  have hχinc : χE.ringHomComp j.toRingHom = χ₀ := by
    apply MulChar.ext'
    intro a
    exact hχ a
  have hχmapinj : Function.Injective (MulChar.ringHomCompHom (R := ZMod N) j.toRingHom) :=
    MulChar.injective_ringHomComp hj
  have hχorder : orderOf χE = orderOf χ₀ := by
    have h := orderOf_injective (MulChar.ringHomCompHom (R := ZMod N) j.toRingHom) hχmapinj χE
    change orderOf (χE.ringHomComp j.toRingHom) = orderOf χE at h
    rw [hχinc] at h
    exact h.symm
  have hρ : ρE = ρ.comp j := rfl
  have huρ : uρ = (ClimbBetaExpected.unitPlace ρ).comp ju := by
    change Units.map (ρ.toRingHom.toMonoidHom.comp j.toRingHom.toMonoidHom) =
      (Units.map ρ.toRingHom.toMonoidHom).comp (Units.map j.toRingHom.toMonoidHom)
    exact Units.map_comp j.toRingHom.toMonoidHom ρ.toRingHom.toMonoidHom
  have hχcomplex : χE.ringHomComp ρE.toRingHom = χ₀.ringHomComp ρ.toRingHom := by
    apply MulChar.ext'
    intro a
    change ρE (χE a) = ρ (χ₀ a)
    rw [hρ, AlgHom.comp_apply, hχ a]
  have hccomplex (a : ZMod N) : ρE (χE a) = ρ (χ₀ a) := by
    rw [hρ, AlgHom.comp_apply, hχ a]
  have hbfield (g : GQ) : j (βE g : E) = (β₀ g : Qbar) := by rw [hbE g, hb g]
  have hefield (g h : GQ) : j (εE g h : E) = (ε₀ g h : Qbar) := by rw [heE g h, he g h]
  have hbcomplex (g : GQ) : uρ (βE g) = ClimbBetaExpected.unitPlace ρ (β₀ g) := by
    rw [huρ, MonoidHom.comp_apply, hbU g]
  have hecomplex (g h : GQ) : uρ (εE g h) = ClimbBetaExpected.unitPlace ρ (ε₀ g h) := by
    rw [huρ, MonoidHom.comp_apply, heU g h]
  have hbcomplexField (g : GQ) : ρE (βE g : E) = ρ (β₀ g : Qbar) := by
    rw [hρ, AlgHom.comp_apply, hbfield g]
  have hecomplexField (g h : GQ) : ρE (εE g h : E) = ρ (ε₀ g h : Qbar) := by
    rw [hρ, AlgHom.comp_apply, hefield g h]
  have hβsqE (g : GQ) : βE g ^ 2 = χE.toUnitHom (GlueDescent.B2Q.cyc N g) := by
    apply hju
    simpa only [map_pow, hbU, hχU, ClimbBetaExpected.galCharacter, MonoidHom.comp_apply] using hβsq g
  have hβcoE (g h : GQ) : βE g * βE h = εE g h * βE (g * h) := by
    apply hju
    simpa only [map_mul, hbU, heU] using hβco g h
  have hεsqE (g h : GQ) : εE g h ^ 2 = 1 := by
    apply hju
    simpa only [map_pow, heU, map_one] using hε.2.1 g h
  have hεcocE (x y z : GQ) : εE (x * y) z * εE x y = εE y z * εE x (y * z) := by
    apply hju
    simpa only [map_mul, heU] using hε.2.2 x y z
  have hβlcE : IsLocallyConstant βE := by
    apply IsLocallyConstant.desc βE ju ?_ hju
    have heq : (ju : Eˣ → Qbarˣ) ∘ βE = β₀ := funext hbU
    rw [heq]
    exact hβlc
  have hεlcE : IsLocallyConstant (Function.uncurry εE) := by
    apply IsLocallyConstant.desc (Function.uncurry εE) ju ?_ hju
    have heq : (ju : Eˣ → Qbarˣ) ∘ Function.uncurry εE = Function.uncurry ε₀ := by
      funext p
      exact heU p.1 p.2
    rw [heq]
    exact hε.1
  have hεsignE : GlueDescent.B2.IsSignCocycle εE := ⟨hεlcE, hεsqE, hεcocE⟩
  have hβoneE : ε₀ 1 1 = 1 → βE 1 = 1 := by
    intro h11
    have hβ01 : β₀ 1 = 1 := ClimbBetaFixedPlace.normalizationFromUnitEquation ε₀ β₀ hβco h11
    apply hju
    simpa only [hbU, map_one] using hβ01
  have hχimage : Set.range (fun a : ZMod N => ρE (χE a)) =
      Set.range (fun a : ZMod N => ρ (χ₀ a)) := congrArg Set.range (funext hccomplex)
  have hβimage : Set.range (fun g : GQ => uρ (βE g)) =
      Set.range (fun g : GQ => ClimbBetaExpected.unitPlace ρ (β₀ g)) := congrArg Set.range (funext hbcomplex)
  have hεimage : Set.range (fun p : GQ × GQ => uρ (εE p.1 p.2)) =
      Set.range (fun p : GQ × GQ => ClimbBetaExpected.unitPlace ρ (ε₀ p.1 p.2)) := by
    apply congrArg Set.range
    funext p
    exact hecomplex p.1 p.2
  have hβimageField : Set.range (fun g : GQ => ρE (βE g : E)) =
      Set.range (fun g : GQ => ρ (β₀ g : Qbar)) := congrArg Set.range (funext hbcomplexField)
  have hεimageField : Set.range (fun p : GQ × GQ => ρE (εE p.1 p.2 : E)) =
      Set.range (fun p : GQ × GQ => ρ (ε₀ p.1 p.2 : Qbar)) := by
    apply congrArg Set.range
    funext p
    exact hecomplexField p.1 p.2
  dsimp only
  refine ⟨hχfin, hβfin, hβu, hεfin, hεu, hS, hfd, hnf, hinc, hmin,
    hρ, ?_, huρ, hfr, hImage, χE, βE, εE, ?_, ?_, ?_, hχinc, hχcomplex,
    hχorder, ?_, hχimage, hβimage, hεimage, hβimageField, hεimageField,
    hβsqE, hβcoE, hεsqE, hεcocE, hβoneE, hβlcE, hεsignE⟩
  · intro x
    rfl
  · intro a
    exact ⟨hχliteral a, hχ a, hccomplex a⟩
  · intro g
    exact ⟨hbE g, hbU g, hbfield g, hbcomplex g, hbcomplexField g⟩
  · intro g h
    exact ⟨heE g h, heU g h, hefield g h, hecomplex g h, hecomplexField g h⟩
  · intro a ha
    exact χE.map_nonunit ha

end ClimbB2CoefficientPacking
