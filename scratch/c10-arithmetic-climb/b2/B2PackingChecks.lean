/-
GIVEN B2 PACKING — FULL TARGET/AXIOM CHECK SOURCE v1, UNCOMPILED.
One full type assignment to the immutable source7a887 target and selected
axiom reports for ALL seven new proof declarations. ParentA executes; the
source-author child does not compile or borrow the worker.
Named level fixtures specialize GIVEN data, not B2 existence or original
arithmetic input construction. The level1 convention is retained.
-/
import B2PackingProof
noncomputable section
namespace ClimbB2CoefficientPackingChecks
open ClimbB2CoefficientPacking

example :
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
      IsLocallyConstant βE ∧ GlueDescent.B2.IsSignCocycle εE) :=
  packGivenActualB2

/-- Full inferred packing result for GIVEN level1 data; no χ(0)=0 shortcut. -/
def PLevelOne (χ₀ : DirichletCharacter Qbar 1) (ε₀ : GQ → GQ → Qbarˣ)
    (β₀ : GQ → Qbarˣ) (hε : GlueDescent.B2.IsSignCocycle ε₀)
    (hβlc : IsLocallyConstant β₀)
    (hβsq : ∀ g, β₀ g ^ 2 = ClimbBetaExpected.galCharacter χ₀ g)
    (hβco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h))
    (ρ : Qbar →ₐ[ℚ] ℂ) :=
  packGivenActualB2 1 χ₀ ε₀ β₀ hε hβlc hβsq hβco ρ

/-- Full inferred packing result for GIVEN level3 data, including nonunits. -/
def PLevelThree (χ₀ : DirichletCharacter Qbar 3) (ε₀ : GQ → GQ → Qbarˣ)
    (β₀ : GQ → Qbarˣ) (hε : GlueDescent.B2.IsSignCocycle ε₀)
    (hβlc : IsLocallyConstant β₀)
    (hβsq : ∀ g, β₀ g ^ 2 = ClimbBetaExpected.galCharacter χ₀ g)
    (hβco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h))
    (ρ : Qbar →ₐ[ℚ] ℂ) :=
  packGivenActualB2 3 χ₀ ε₀ β₀ hε hβlc hβsq hβco ρ

/-- Nonzero-polynomial guard includes the c=0 quadratic fibre. -/
example : {z : Qbar | z ^ 2 = 0}.Finite := finite_square_fibre 0

/-- Same actual character law on any GIVEN nonunit, not an invented witness. -/
example (N : ℕ) [NeZero N] (χ₀ : DirichletCharacter Qbar N)
    (a : ZMod N) (ha : ¬ IsUnit a) : χ₀ a = 0 := χ₀.map_nonunit ha

end ClimbB2CoefficientPackingChecks

#check @ClimbB2CoefficientPacking.finite_square_fibre
#check @ClimbB2CoefficientPacking.characterValues_finite
#check @ClimbB2CoefficientPacking.beta_sq_eq
#check @ClimbB2CoefficientPacking.betaValues_finite
#check @ClimbB2CoefficientPacking.epsilonValues_finite
#check @ClimbB2CoefficientPacking.range_units_finite
#check @ClimbB2CoefficientPacking.packGivenActualB2
#print axioms ClimbB2CoefficientPacking.finite_square_fibre
#print axioms ClimbB2CoefficientPacking.characterValues_finite
#print axioms ClimbB2CoefficientPacking.beta_sq_eq
#print axioms ClimbB2CoefficientPacking.betaValues_finite
#print axioms ClimbB2CoefficientPacking.epsilonValues_finite
#print axioms ClimbB2CoefficientPacking.range_units_finite
#print axioms ClimbB2CoefficientPacking.packGivenActualB2
#print axioms ClimbB2CoefficientPackingChecks.PLevelOne
#print axioms ClimbB2CoefficientPackingChecks.PLevelThree
#check @ClimbB2CoefficientPackingChecks.PLevelOne
#check @ClimbB2CoefficientPackingChecks.PLevelThree
