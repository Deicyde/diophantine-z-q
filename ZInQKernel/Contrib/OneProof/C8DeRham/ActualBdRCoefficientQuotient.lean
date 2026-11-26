import ZInQKernel.Contrib.OneProof.C8DeRham.ActualBdRCoefficients

/-! # The coefficient quotient of the full de Rham comparison space

The scalar extension is first over `ℚ_p`, as in the definition of `IsDeRham`.
Projection to the factor selected by the actual coefficient embedding is
surjective and equivariant on the fixing subgroup. No splitting of a tensor
product into coefficient-embedding factors is assumed.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
variable {n : ℕ}

/-- Apply the canonical coefficient embedding on coordinates. -/
def coeffVector : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → BdR p) where
  toFun v i := coeffToBdR p E (v i)
  map_add' v w := by ext i; exact map_add (coeffToBdR p E) (v i) (w i)
  map_smul' c v := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, map_mul, AlgHom.commutes]

/-- The quotient of `B_dR ⊗_{ℚ_p} E^n` for the actual coefficient embedding. -/
def coeffProjection : (BdR p ⊗[ℚ_[p]] (Fin n → E)) →ₗ[BdR p] (Fin n → BdR p) :=
  (coeffVector p E).liftBaseChange (BdR p)

@[simp]
theorem coeffProjection_tmul (b : BdR p) (v : Fin n → E) :
    coeffProjection p E (b ⊗ₜ[ℚ_[p]] v) = b • coeffVector p E v :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- Surjectivity uses the standard vectors in the actual coefficient field. -/
theorem coeffProjection_surjective : Function.Surjective (coeffProjection p E (n := n)) := by
  classical
  intro x
  refine ⟨∑ i : Fin n, (x i) ⊗ₜ[ℚ_[p]] (Pi.single i (1 : E)), ?_⟩
  rw [map_sum]
  ext j
  simp only [coeffProjection_tmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coeffVector,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp [Pi.single_apply, mul_ite]

set_option maxHeartbeats 1300000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- On the fixing subgroup the quotient is equivariant for the **same** `r`
and the original action on `B_dR`. This does not yet construct a basis of
invariant vectors of the full scalar extension. -/
theorem coeffProjection_equivariant (r : GQp p →* GL (Fin n) E) (σ : GQp p)
    (hσ : σ ∈ E.fixingSubgroup) (t : BdR p ⊗[ℚ_[p]] (Fin n → E)) :
    coeffProjection p E (TensorProduct.map (bdrActHom p σ) (rRep p r σ) t) =
      ((r σ : Matrix (Fin n) (Fin n) E).map (coeffToBdR p E)).mulVec
        (fun i => bdrAct p σ (coeffProjection p E t i)) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    change (0 : Fin n → BdR p) =
      ((r σ : Matrix (Fin n) (Fin n) E).map (coeffToBdR p E)).mulVec 0
    rw [Matrix.mulVec_zero]
  | tmul b v =>
    rw [TensorProduct.map_tmul, coeffProjection_tmul, coeffProjection_tmul, bdrActHom_apply, rRep_apply]
    ext i
    simp only [coeffVector, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, bdrAct_coeffToBdR p E σ hσ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  | add x y hx hy =>
    have he : (fun i => bdrAct p σ (coeffProjection p E (x + y) i)) =
        (fun i => bdrAct p σ (coeffProjection p E x i)) + fun i => bdrAct p σ (coeffProjection p E y i) := by
      ext i
      simp only [map_add, Pi.add_apply]
    rw [map_add, map_add, hx, hy, he, Matrix.mulVec_add]

end HDec.G0Galois.C8Conrad.Manuscript
