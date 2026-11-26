import ZInQKernel.Contrib.OneProof.C8DeRham.ActualBdRRows
import ZInQKernel.Contrib.OneProof.C8DeRham.FontaineClosureQp

/-! # De Rham rank gives period rows for the original coefficient matrices

Restrict scalars to `ℚ_p` using a basis. The project's de Rham rank is
computed on equivariant forms, so the standard de Rham rank first appears
on the dual. Dualize back before taking fixed columns and transporting them
to the full comparison tensor. The final coefficient quotient recovers
period rows for the original representation.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4
open _root_.ZInQ.Contrib.HodgeSplit
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
variable {n m : ℕ}

private def matrixRep (r : GQp p →* GL (Fin n) E)
    (b : Module.Basis (Fin m) ℚ_[p] (Fin n → E)) : GQp p →* GL (Fin m) ℚ_[p] :=
  ((LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom.comp (rRep p r)).toHomUnits

omit [FiniteDimensional ℚ_[p] E] in
private theorem matrixRep_mulVec (r : GQp p →* GL (Fin n) E)
    (b : Module.Basis (Fin m) ℚ_[p] (Fin n → E)) (σ : GQp p) (v : Fin n → E) :
    (matrixRep p E r b σ : Matrix (Fin m) (Fin m) ℚ_[p]).mulVec (b.equivFun v) =
      b.equivFun (rRep p r σ v) := by
  change (LinearMap.toMatrix b b (rRep p r σ)).mulVec (b.equivFun v) = _
  simpa only [Module.Basis.equivFun_apply] using
    (LinearMap.toMatrix_mulVec_repr b b (rRep p r σ) v)

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 300000 in
private def matrixRep_ddrSpace (r : GQp p →* GL (Fin n) E)
    (b : Module.Basis (Fin m) ℚ_[p] (Fin n → E)) :
    ddrSpace p r ≃ₗ[ℚ_[p]] ddrSpace p (matrixRep p E r b) where
  toFun φ := ⟨φ.1.comp b.equivFun.symm.toLinearMap, fun σ v => by
    change φ.1 (b.equivFun.symm ((matrixRep p E r b σ : Matrix _ _ _).mulVec v)) =
      bdrAct p σ (φ.1 (b.equivFun.symm v))
    have h := matrixRep_mulVec p E r b σ (b.equivFun.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply, rRep_apply]
    exact φ.2 σ _⟩
  invFun ψ := ⟨ψ.1.comp b.equivFun.toLinearMap, fun σ v => by
    change ψ.1 (b.equivFun (rRep p r σ v)) = bdrAct p σ (ψ.1 (b.equivFun v))
    rw [← matrixRep_mulVec p E r b]
    exact ψ.2 σ _⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  left_inv φ := Subtype.ext (LinearMap.ext fun v => by
    change φ.1 (b.equivFun.symm (b.equivFun v)) = φ.1 v
    rw [LinearEquiv.symm_apply_apply])
  right_inv ψ := Subtype.ext (LinearMap.ext fun v => by
    change ψ.1 (b.equivFun (b.equivFun.symm v)) = ψ.1 v
    rw [LinearEquiv.apply_symm_apply])

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 300000 in
omit [FiniteDimensional ℚ_[p] E] in
private theorem baseChange_equivFun_action (r : GQp p →* GL (Fin n) E)
    (b : Module.Basis (Fin m) ℚ_[p] (Fin n → E)) (σ : GQp p)
    (t : BdR p ⊗[ℚ_[p]] (Fin n → E)) :
    (b.baseChange (BdR p)).equivFun (TensorProduct.map (bdrActHom p σ) (rRep p r σ) t) =
      (matB p (matrixRep p E r b σ : Matrix _ _ _)).mulVec
        (bAct p σ ((b.baseChange (BdR p)).equivFun t)) := by
  let f := (b.baseChange (BdR p)).equivFun
  change f _ = (matB p _).mulVec (bAct p σ (f t))
  have hf (x : BdR p) (v : Fin n → E) :
      f (x ⊗ₜ[ℚ_[p]] v) = x • (fun i => algebraMap ℚ_[p] (BdR p) (b.equivFun v i)) := by
    ext i
    simp only [f, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      Pi.smul_apply, Algebra.smul_def]
    exact mul_comm _ _
  have hfix (v : Fin n → E) :
      bAct p σ (fun i => algebraMap ℚ_[p] (BdR p) (b.equivFun v i)) =
        algebraMap ℚ_[p] (BdR p) ∘ b.equivFun v :=
    funext fun i => bdrAct_qpToBdR p σ (b.equivFun v i)
  induction t using TensorProduct.inductionOn with
  | tmul x v =>
    rw [TensorProduct.map_tmul, hf, hf, bAct_smul, bdrActHom_apply, Matrix.mulVec_smul, hfix]
    congr 1
    rw [← matrixRep_mulVec p E r b]
    funext i
    simpa only [matB, Function.comp_apply] using
      RingHom.map_mulVec (algebraMap ℚ_[p] (BdR p))
        (matrixRep p E r b σ : Matrix (Fin m) (Fin m) ℚ_[p]) (b.equivFun v) i
  | add x y hx hy =>
    rw [map_add, map_add, map_add, bAct_add, Matrix.mulVec_add, hx, hy]

private theorem exists_basis_of_columns {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (f : W ≃ₗ[K] (Fin m → K)) (P : Matrix (Fin m) (Fin m) K) (hdet : P.det ≠ 0) :
    ∃ c : Module.Basis (Fin m) K W, ∀ i, f (c i) = P.col i := by
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet
  let c := (Pi.basisFun K (Fin m)).map
    ((Matrix.GeneralLinearGroup.toLin U).toLinearEquiv.trans f.symm)
  refine ⟨c, fun i => ?_⟩
  have hU : (U : Matrix (Fin m) (Fin m) K) = P := rfl
  simp only [c, Module.Basis.map_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearMap.GeneralLinearGroup.coe_toLinearEquiv, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply, Pi.basisFun_apply, hU, Matrix.mulVec_single_one]

set_option maxHeartbeats 1700000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- The de Rham rank produces a full basis of invariant tensors for the
original action, before any coefficient quotient is taken. -/
theorem exists_invariant_basis_of_isDeRham (r : GQp p →* GL (Fin n) E)
    (hr : IsDeRham p r) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ_[p] (Fin n → E))) (BdR p)
        (BdR p ⊗[ℚ_[p]] (Fin n → E)),
      ∀ i σ, TensorProduct.map (bdrActHom p σ) (rRep p r σ) (b i) = b i := by
  classical
  let b := Module.finBasis ℚ_[p] (Fin n → E)
  let ρ := matrixRep p E r b
  have hρ : IsDeRham p ρ := by
    unfold IsDeRham at hr ⊢
    rw [← (matrixRep_ddrSpace p E r b).finrank_eq, hr, Module.finrank_self, mul_one,
      Module.finrank_pi_fintype]
    simp
  have hdual := (isDeRham_iff_std p ρ).mp hρ
  have hstd : IsDeRhamStd p ρ := by
    apply dual_of_bdr p (bdrInvariantsQp_proof p) (dualRep p ρ) ρ _ hdual
    intro σ
    rw [← map_inv, dualRep_val, inv_inv, Matrix.transpose_transpose]
  obtain ⟨P, hdet, hP⟩ := exists_matrix_of_isDeRhamStd p (bdrInvariantsQp_proof p) ρ hstd
  let f := (b.baseChange (BdR p)).equivFun
  let modB : Module (BdR p) (BdR p ⊗[ℚ_[p]] (Fin n → E)) := inferInstance
  have hcols : ∃ c : Module.Basis (Fin (Module.finrank ℚ_[p] (Fin n → E))) (BdR p)
      (BdR p ⊗[ℚ_[p]] (Fin n → E)), ∀ i, f (c i) = P.col i :=
    @exists_basis_of_columns _ (BdR p) (BdR p ⊗[ℚ_[p]] (Fin n → E))
      (DeRhamPrint.bdrField p) inferInstance modB f P hdet
  obtain ⟨c, hc⟩ := hcols
  refine ⟨c, fun i σ => f.injective ?_⟩
  have hact : f (TensorProduct.map (bdrActHom p σ) (rRep p r σ) (c i)) =
      (matB p (ρ σ : Matrix _ _ _)).mulVec (bAct p σ (f (c i))) :=
    baseChange_equivFun_action p E r b σ (c i)
  rw [hact, hc]
  funext j
  have h := congrFun (congrFun (hP σ) j) i
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col_apply, bAct, Matrix.map_apply] using h

/-- The actual `E`-valued matrices of a de Rham representation admit
`B_dR` period rows on the subgroup fixing `E`. There is no normality or
continuity assumption and no replacement coefficient field. -/
theorem hasBdRRows_of_isDeRham (r : GQp p →* GL (Fin n) E)
    (hr : IsDeRham p r) : HasBdRRows p E r := by
  obtain ⟨b, hb⟩ := exists_invariant_basis_of_isDeRham p E r hr
  exact hasBdRRows_of_invariant_basis p E r b fun i σ _ => hb i σ

end HDec.G0Galois.C8Conrad.Manuscript
