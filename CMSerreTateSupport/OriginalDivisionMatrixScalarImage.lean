import OriginalFiniteLevelCongruenceDiagonal
import ActualFiniteRamificationV002
import ActualCongruenceProEllFiniteQuotients
import ValuationResidueCharacteristicCoherent

/-!
# Finite-level matrices of the original Tate action

The matrix quotient is constructed from the actual division field fixed
by the original torsion action kernel. Finiteness of the original torsion
level is explicitly an intermediate premise here; the geometric count
supplier must instantiate it in the final original-object theorem.
-/

noncomputable section
set_option autoImplicit false

namespace NativeTateCongruence

open CategoryTheory AlgebraicGeometry MonObj Matrix
open ActualFiniteLevel ActualDivisionField

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable [CharZero K] [IsAlgClosure K Ω]
variable {d : Type*} [Fintype d] [DecidableEq d]

variable (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime]
  (b : Module.Basis d ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))))

def matrixLevel (n : ℕ) : (Ω ≃ₐ[K] Ω) →* GL d (ZMod (ell ^ (n + 1))) :=
  (IntegralCongruence.level ell n).comp (originalTateMatrix A ell b)

theorem point_kernel_le_matrix_kernel (n : ℕ) :
    (action (Ω := Ω) A (ell ^ (n + 1))).ker ≤ (matrixLevel A ell b n).ker := by
  intro σ hσ
  exact level_identity_of_original_points_fixed A ell b σ n
    ((mem_action_ker A (ell ^ (n + 1)) σ).mp hσ)

def divisionMatrix (n : ℕ) [Finite (torsionSubgroup A Ω (ell ^ (n + 1)))] :
    (divisionField (Ω := Ω) A (ell ^ (n + 1)) ≃ₐ[K] divisionField (Ω := Ω) A (ell ^ (n + 1))) →*
      GL d (ZMod (ell ^ (n + 1))) :=
  (restriction (Ω := Ω) A (ell ^ (n + 1))).liftOfSurjective (restriction_surjective (Ω := Ω) A _)
    ⟨matrixLevel A ell b n, by
      rw [restriction_ker]
      exact point_kernel_le_matrix_kernel A ell b n⟩

theorem divisionMatrix_restriction (n : ℕ) [Finite (torsionSubgroup A Ω (ell ^ (n + 1)))]
    (σ : Ω ≃ₐ[K] Ω) :
    divisionMatrix A ell b n (restriction (Ω := Ω) A (ell ^ (n + 1)) σ) = matrixLevel A ell b n σ := by
  exact (restriction (Ω := Ω) A (ell ^ (n + 1))).liftOfRightInverse_comp_apply _ _ _ σ

theorem divisionMatrix_comp (n : ℕ) [Finite (torsionSubgroup A Ω (ell ^ (n + 1)))] :
    (divisionMatrix A ell b n).comp (restriction (Ω := Ω) A (ell ^ (n + 1))) = matrixLevel A ell b n :=
  MonoidHom.ext (divisionMatrix_restriction A ell b n)

/-- Continuity is obtained through the actual finite Galois restriction,
not added to an arbitrary representation as a premise. -/
theorem matrixLevel_continuous (n : ℕ) [Finite (torsionSubgroup A Ω (ell ^ (n + 1)))] :
    Continuous (matrixLevel A ell b n) := by
  have hf : Continuous (divisionMatrix A ell b n) := continuous_of_discreteTopology
  have he : (divisionMatrix A ell b n) ∘ restriction (Ω := Ω) A (ell ^ (n + 1)) = matrixLevel A ell b n :=
    congrArg DFunLike.coe (divisionMatrix_comp A ell b n)
  rw [← he]
  exact hf.comp (restriction_continuous A (ell ^ (n + 1)))

def wildIntegralMatrix (w : ValuationSubring Ω) :
    WildFiniteGroup.strictDisplacementGroup (K := K) w →* GL d ℤ_[ell] :=
  (originalTateMatrix A ell b).comp (WildFiniteGroup.strictDisplacementGroup (K := K) w).subtype

/-- Actual residue characteristics are transported to the actual division
field. The p-group conclusion is derived from strict-displacement finite
quotients, not assumed as a model of wild inertia. -/
theorem wild_matrix_level_isPGroup (w : ValuationSubring Ω) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField w) p] (n : ℕ)
    [Finite (torsionSubgroup A Ω (ell ^ (n + 1)))] :
    IsPGroup p ((IntegralCongruence.level ell n).comp (wildIntegralMatrix A ell b w)).range := by
  let W := WildFiniteGroup.strictDisplacementGroup (K := K) w
  let L := finiteDivisionField (Ω := Ω) A (ell ^ (n + 1))
  haveI : CharP (IsLocalRing.ResidueField (w.comap L.val.toRingHom)) p :=
    (ValuationResidueCharacteristic.residue_charP_iff w L.val.toRingHom p).mpr inferInstance
  have hP := ActualFiniteRamification.wildImage_isPGroup w L p
  have he : W.map (matrixLevel A ell b n) =
      (ActualFiniteRamification.wildImage w L).map (divisionMatrix A ell b n) := by
    change W.map (matrixLevel A ell b n) =
      (W.map (restriction (Ω := Ω) A (ell ^ (n + 1)))).map (divisionMatrix A ell b n)
    rw [Subgroup.map_map, divisionMatrix_comp]
  have hM : IsPGroup p (W.map (matrixLevel A ell b n)) := by
    rw [he]
    exact hP.map (divisionMatrix A ell b n)
  intro x
  have hx : x.1 ∈ W.map (matrixLevel A ell b n) := by
    obtain ⟨sigma, hsigma⟩ := x.2
    refine ⟨sigma.1, sigma.2, ?_⟩
    exact hsigma
  let y : W.map (matrixLevel A ell b n) := ⟨x.1, hx⟩
  obtain ⟨k, hk⟩ := hM y
  refine ⟨k, Subtype.ext ?_⟩
  have hval : y.1 ^ (p ^ k) = 1 := congrArg (fun z : W.map (matrixLevel A ell b n) => z.1) hk
  change x.1 ^ (p ^ k) = 1
  exact hval

/-- An intermediate finiteness statement for the original matrix action.
Its basis and actual finite torsion premises are still to be instantiated
by the genuine Mumford compatible-Tate supplier. -/
theorem wild_matrix_image_finite (w : ValuationSubring Ω) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField w) p] (hne : p ≠ ell)
    [∀ n : ℕ, Finite (torsionSubgroup A Ω (ell ^ (n + 1)))] :
    (Set.range (wildIntegralMatrix A ell b w)).Finite :=
  IntegralCongruence.finite_image_of_finite_level_pGroups p ell hne _
    (fun n => wild_matrix_level_isPGroup A ell b w p n)

#print axioms point_kernel_le_matrix_kernel
#print axioms divisionMatrix_comp
#print axioms matrixLevel_continuous
#print axioms wild_matrix_level_isPGroup
#check wild_matrix_image_finite
#print axioms wild_matrix_image_finite

end NativeTateCongruence
