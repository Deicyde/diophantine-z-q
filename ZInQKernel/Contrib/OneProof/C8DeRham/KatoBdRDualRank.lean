import ZInQKernel.Contrib.OneProof.ModularHTCoeff

/-! # Kato's de Rham rank and the arithmetic contragredient

Kato's period rank concerns the cohomological representation. The project
uses arithmetic Frobenius, so its representation is the linear dual. The
trace pairing identifies the actual tensor invariants of the original
representation with the project's `ddrSpace` for that dual. The theorem
below only transports the rank on the same coefficient matrices: it does
not identify a Lean representation with Kato's Hecke quotient.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {n : ℕ}
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]

/-- The diagonal action on the scalar extension; the order of the tensor
factors is exchanged relative to Kato's `B_dR ⊗ V`. -/
abbrev geomBdRAct (r : GQp p →* GL (Fin n) E) (σ : GQp p) :
    ((Fin n → E) ⊗[ℚ_[p]] BdR p) →ₗ[ℚ_[p]] ((Fin n → E) ⊗[ℚ_[p]] BdR p) :=
  TensorProduct.map (rRep p r σ) (bdrActHom p σ)

/-- The genuine `B_dR` tensor invariants of the cohomological matrices. -/
def geomBdRSpace (r : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] ((Fin n → E) ⊗[ℚ_[p]] BdR p) where
  carrier := {v | ∀ σ, geomBdRAct p E r σ v = v}
  zero_mem' σ := map_zero _
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  smul_mem' a v hv σ := by rw [map_smul, hv σ]

/-- `V ⊗ B_dR ≃ Hom_{Q_p}(V,B_dR)`, through the finite coefficient trace. -/
def traceBdR : ((Fin n → E) ⊗[ℚ_[p]] BdR p) ≃ₗ[ℚ_[p]]
    ((Fin n → E) →ₗ[ℚ_[p]] BdR p) :=
  (TensorProduct.congr (HTNewAssembly.trEquiv p E) (LinearEquiv.refl ℚ_[p] (BdR p))).trans
    (dualTensorHomEquiv ℚ_[p] (Fin n → E) (BdR p))

theorem traceBdR_tmul (v u : Fin n → E) (b : BdR p) :
    traceBdR p E (v ⊗ₜ b) u = Algebra.trace ℚ_[p] E (u ⬝ᵥ v) • b := by
  simp [traceBdR, HTNewAssembly.trEquiv_apply]

set_option synthInstance.maxHeartbeats 300000 in
/-- Equivariance on the cohomological matrices, with the transpose in the
argument of the trace functional. -/
theorem traceBdR_action (r : GQp p →* GL (Fin n) E) (σ : GQp p)
    (t : (Fin n → E) ⊗[ℚ_[p]] BdR p) (u : Fin n → E) :
    traceBdR p E (geomBdRAct p E r σ t) u =
      bdrAct p σ (traceBdR p E t ((r σ : Matrix (Fin n) (Fin n) E).transpose.mulVec u)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [TensorProduct.map_tmul, traceBdR_tmul, traceBdR_tmul, rRep_apply, bdrActHom_apply, bdrAct_smul,
      Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

set_option maxHeartbeats 1500000 in
/-- Fixed tensors are exactly the equivariant linear maps for the
contragredient, on the full local Galois group. -/
theorem traceBdR_mem_iff (r : GQp p →* GL (Fin n) E) (t : (Fin n → E) ⊗[ℚ_[p]] BdR p) :
    traceBdR p E t ∈ ddrSpace p (HTNewAssembly.dualE r) ↔ t ∈ geomBdRSpace p E r := by
  constructor
  · intro h σ
    apply (traceBdR p E).injective
    refine LinearMap.ext fun u => ?_
    have he : traceBdR p E t ((r σ : Matrix (Fin n) (Fin n) E).transpose.mulVec u) =
        bdrAct p σ⁻¹ (traceBdR p E t u) := by
      simpa only [HTNewAssembly.dualE_val, inv_inv] using h σ⁻¹ u
    rw [traceBdR_action, he]
    have hp := congrArg (fun f : BdR p →ₗ[ℚ_[p]] BdR p => f (traceBdR p E t u))
      (map_mul (bdrActHom p) σ σ⁻¹)
    rw [mul_inv_cancel, map_one] at hp
    exact hp.symm
  · intro h σ u
    have he := LinearMap.congr_fun (congrArg (traceBdR p E) (h σ))
      ((r σ⁻¹ : Matrix (Fin n) (Fin n) E).transpose.mulVec u)
    rw [traceBdR_action, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] at he
    change traceBdR p E t ((HTNewAssembly.dualE r σ : Matrix (Fin n) (Fin n) E).mulVec u) = _
    rw [HTNewAssembly.dualE_val, ← he]

/-- The period rank of Kato's cohomological representation supplies the
arithmetic dual's de Rham rank, without changing the coefficient field or
postulating the de Rham property of an arbitrary attached representation. -/
theorem isDeRham_dual_of_geomBdR_rank (r : GQp p →* GL (Fin n) E)
    (h : finrank ℚ_[p] (geomBdRSpace p E r) = n * finrank ℚ_[p] E) :
    IsDeRham p (HTNewAssembly.dualE r) := by
  have hmap : (geomBdRSpace p E r).map (traceBdR p E (n := n)).toLinearMap =
      ddrSpace p (HTNewAssembly.dualE r) := by
    ext φ
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (traceBdR_mem_iff p E r t).mpr ht
    · intro hφ
      refine ⟨(traceBdR p E).symm φ, ?_, (traceBdR p E).apply_symm_apply φ⟩
      exact (traceBdR_mem_iff p E r ((traceBdR p E).symm φ)).mp (by simpa only [LinearEquiv.apply_symm_apply] using hφ)
  rw [IsDeRham, ← hmap, LinearEquiv.finrank_map_eq, h]

end HDec.G0Galois.C8Conrad.Manuscript
