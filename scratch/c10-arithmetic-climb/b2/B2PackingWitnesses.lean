/-
REAL LEVEL-1 B2 BOUNDARY WITNESSES — SOURCE v1, UNCOMPILED.
These are explicit admissible GIVEN-data fixtures over the SAME Qbar/GQ,
not the original arithmetic output of B2 leaves or an existence theorem for it.
They specialize the COMPLETE packing root, never a convenient output clause.
Original source/target/proof/check files are unchanged.
-/
import B2PackingProof
noncomputable section
namespace ClimbB2PackingWitnesses
open ClimbB2CoefficientPacking

/-- A literal unit with value -1 in the actual algebraic closure. -/
def negativeUnit : Qbarˣ := Units.mk0 (-1 : Qbar) (by norm_num)

/-- The constant -1 datum satisfies the required unit square equation. -/
theorem negativeUnit_squared : negativeUnit ^ 2 = 1 := by
  apply Units.ext
  change (-1 : Qbar) ^ 2 = 1
  norm_num

/-- It is genuinely unnormalized, not an assumed unequal-unit parameter. -/
theorem negativeUnit_ne_one : negativeUnit ≠ 1 := by
  intro h
  have hv := congrArg (fun u : Qbarˣ => (u : Qbar)) h
  change (-1 : Qbar) = 1 at hv
  norm_num at hv

/-- The same actual cyclotomic map for the actual trivial character. -/
theorem trivial_galCharacter {N : ℕ} [NeZero N] (g : GQ) :
    ClimbBetaExpected.galCharacter (1 : DirichletCharacter Qbar N) g = 1 := by
  apply Units.ext
  change (1 : DirichletCharacter Qbar N) (GlueDescent.B2Q.cyc N g : ZMod N) = 1
  simp

/-- Existing LC of a constant and its own square identity give sign data. -/
theorem constant_sign (u : Qbarˣ) (hsq : u ^ 2 = 1) :
    GlueDescent.B2.IsSignCocycle (fun _ _ : GQ => u) := by
  refine ⟨IsLocallyConstant.of_constant _ (fun _ _ => rfl), ?_, ?_⟩
  · intro g h
    exact hsq
  · intro x y z
    rfl

/-- Full inferred R1-R6 result for a literal constant unit and level1 character. -/
def constantPacking (u : Qbarˣ) (hsq : u ^ 2 = 1) (ρ : Qbar →ₐ[ℚ] ℂ) :=
  packGivenActualB2 1 (1 : DirichletCharacter Qbar 1)
    (fun _ _ : GQ => u) (fun _ : GQ => u)
    (constant_sign u hsq)
    (IsLocallyConstant.of_constant _ (fun _ _ => rfl))
    (fun g => by rw [trivial_galCharacter]; exact hsq)
    (fun _ _ => rfl) ρ

/-- REAL normalized χ=1, ε=β=1 level1 tuple; every R1-R6 output is returned. -/
def PNormalizedOne (ρ : Qbar →ₐ[ℚ] ℂ) :=
  constantPacking (1 : Qbarˣ) (by simp) ρ

/-- REAL unnormalized χ=1, ε=β=-1 tuple; no replacement normalization. -/
def PUnnormalizedMinusOne (ρ : Qbar →ₐ[ℚ] ℂ) :=
  constantPacking negativeUnit negativeUnit_squared ρ

-- Both original epsilon(1,1) and beta(1) really fail normalization here.
example : (fun _ _ : GQ => negativeUnit) 1 1 ≠ 1 := negativeUnit_ne_one
example : (fun _ : GQ => negativeUnit) 1 ≠ 1 := negativeUnit_ne_one

-- The c=0 fibre uses the NONZERO X^2 polynomial, not a zero-polynomial rootset.
example : {z : Qbar | z ^ 2 = 0}.Finite := finite_square_fibre 0

end ClimbB2PackingWitnesses

#check @ClimbB2PackingWitnesses.PNormalizedOne
#check @ClimbB2PackingWitnesses.PUnnormalizedMinusOne
#print axioms ClimbB2PackingWitnesses.negativeUnit
#print axioms ClimbB2PackingWitnesses.negativeUnit_squared
#print axioms ClimbB2PackingWitnesses.negativeUnit_ne_one
#print axioms ClimbB2PackingWitnesses.trivial_galCharacter
#print axioms ClimbB2PackingWitnesses.constant_sign
#print axioms ClimbB2PackingWitnesses.constantPacking
#print axioms ClimbB2PackingWitnesses.PNormalizedOne
#print axioms ClimbB2PackingWitnesses.PUnnormalizedMinusOne
