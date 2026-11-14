/-
GIVEN ACTUAL B2 COEFFICIENT PACKING — DEFINITIONS/TARGET SOURCE v1.
UNCOMPILED. No candidate theorem bodies and no new supplier are in this file.

OLD contract: OLD-B2-PACKING-EXPECTATION-v1.md SHA256
1c30d67fe09ad1af6a42e1064496bb5f8bc394c1d5d88213de0b9017da7015ac.
Accepted FCF target/proof remain unchanged (66c85645... / 08ad6244...).

All values, the nonzero level, GQ, cyc N and complex place are GIVEN actual
old-source objects. S is exactly their three FULL value ranges, not a sample
or a polynomial-root superset. Finite ranges and FD/NumberField are OUTPUTS.
N=1 is allowed; no Finite GQ, finite quotient or extra arithmetic leaf is used.

Finiteness route: finite ZMod N from returned NeZero N; finite quadratic
fibres X^2-Cc for beta over the actual finite character value range; X^2-1
for epsilon. Polynomial nonzeroness and finiteness use pinned Mathlib APIs.
No new 2*totient lemma, Galois theory or preimage proof is required.

LC output is only the existing GIVEN LC transferred by IsLocallyConstant.desc
through injective unit inclusion, never LC inferred from finite range.
No field topology/continuity is constructed, and beta(1)=1 remains conditional.

Opaque actualB2Transport does NOT return the original complex chi/beta image
certificates. Core recovery below is of the GIVEN Qbar tuple and its same-rho
images. External complex chi/beta recovery needs retained old strong witnesses.
-/

import BetaFixedPlace
import FCF_Proof
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

namespace ClimbB2CoefficientPacking

abbrev Qbar : Type := GlueC10.Qbar
abbrev GQ : Type := GlueDescent.B2Q.GQ

/-- Includes ALL Dirichlet values, including zero on nonunits. -/
def characterValues {N : ℕ} (χ₀ : DirichletCharacter Qbar N) : Set Qbar :=
  Set.range (fun a : ZMod N => χ₀ a)

def betaValues (β₀ : GQ → Qbarˣ) : Set Qbar :=
  Set.range (fun g : GQ => (β₀ g : Qbar))

def epsilonValues (ε₀ : GQ → GQ → Qbarˣ) : Set Qbar :=
  Set.range (fun p : GQ × GQ => (ε₀ p.1 p.2 : Qbar))

/-- Exact left-associated union fixed by the independent OLD contract. -/
def coefficients {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ) : Set Qbar :=
  (characterValues χ₀ ∪ betaValues β₀) ∪ epsilonValues ε₀

abbrev coefficientField {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ) :
    IntermediateField ℚ Qbar :=
  ClimbFiniteCoefficientField.fieldOf (coefficients χ₀ ε₀ β₀)

def fieldInclusion {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ) :
    coefficientField χ₀ ε₀ β₀ →ₐ[ℚ] Qbar :=
  (coefficientField χ₀ ε₀ β₀).val

def restrictedComplexPlace {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ)
    (ρ : Qbar →ₐ[ℚ] ℂ) : coefficientField χ₀ ε₀ β₀ →ₐ[ℚ] ℂ :=
  ClimbFiniteCoefficientField.restrictedPlace (coefficients χ₀ ε₀ β₀) ρ

def unitInclusion {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ) :
    (coefficientField χ₀ ε₀ β₀)ˣ →* Qbarˣ :=
  Units.map (fieldInclusion χ₀ ε₀ β₀).toRingHom.toMonoidHom

def unitComplexPlace {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ)
    (ρ : Qbar →ₐ[ℚ] ℂ) : (coefficientField χ₀ ε₀ β₀)ˣ →* ℂˣ :=
  Units.map (restrictedComplexPlace χ₀ ε₀ β₀ ρ).toRingHom.toMonoidHom

/-- Each prescribed field-valued lift is the original coefficient, literally. -/
def characterLift {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ) (a : ZMod N) :
    coefficientField χ₀ ε₀ β₀ :=
  ClimbFiniteCoefficientField.coefficientLift (coefficients χ₀ ε₀ β₀)
    ⟨χ₀ a, Or.inl (Or.inl ⟨a, rfl⟩)⟩

def betaLift {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ) (g : GQ) :
    coefficientField χ₀ ε₀ β₀ :=
  ClimbFiniteCoefficientField.coefficientLift (coefficients χ₀ ε₀ β₀)
    ⟨(β₀ g : Qbar), Or.inl (Or.inr ⟨g, rfl⟩)⟩

def epsilonLift {N : ℕ} (χ₀ : DirichletCharacter Qbar N)
    (ε₀ : GQ → GQ → Qbarˣ) (β₀ : GQ → Qbarˣ) (g h : GQ) :
    coefficientField χ₀ ε₀ β₀ :=
  ClimbFiniteCoefficientField.coefficientLift (coefficients χ₀ ε₀ β₀)
    ⟨(ε₀ g h : Qbar), Or.inr ⟨(g, h), rfl⟩⟩

/- Full frozen target name: packGivenActualB2.
   The only inputs are the exact GIVEN old B2 tuple, its old sign/LC/square/
   cochain clauses, returned NeZero N, and the caller's SAME rho.
   Character/unit packaging is existential ONLY with its value function fixed
   to the literal lifts above and all original-value equations retained.
   No desired finite range, FD/NumberField, chosen E or normalization is a premise.
-/
#check
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
    -- R1: full ranges; no finite GQ or finite sampling.
    (characterValues χ₀).Finite ∧
    (betaValues β₀).Finite ∧ (Set.range β₀).Finite ∧
    (epsilonValues ε₀).Finite ∧ (Set.range (Function.uncurry ε₀)).Finite ∧
    S.Finite ∧
    -- R2: one exact least finite-rational-degree field.
    FiniteDimensional ℚ E ∧ NumberField E ∧
    (S ⊆ (E : Set Qbar)) ∧
    (∀ F : IntermediateField ℚ Qbar, S ⊆ (F : Set Qbar) → E ≤ F) ∧
    -- R4: SAME place and full field/unit maps, not only generator samples.
    (ρE = ρ.comp ιE) ∧ (∀ x : E, ρE x = ρ (ιE x)) ∧
    (uρ = (ClimbBetaExpected.unitPlace ρ).comp uι) ∧
    (ρE.fieldRange = E.map ρ) ∧
    (Set.range (fun x : E => ρE x) = ρ '' (E : Set Qbar)) ∧
    -- R3/R5/R6 use the SAME returned E-valued structural objects.
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
      IsLocallyConstant βE ∧ GlueDescent.B2.IsSignCocycle εE)

end ClimbB2CoefficientPacking
