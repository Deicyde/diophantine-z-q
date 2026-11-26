import ZInQKernel.Contrib.OneProof.C8DeRham.ActualBdRCoefficientQuotient
import ZInQKernel.Contrib.OneProof.C8DeRham.BdRHomPeriod

/-! # Invariant comparison vectors give actual coefficient period rows

Project a full comparison basis along the actual coefficient embedding. The
images span; choose a basis among those images, which are fixed by the
semilinear action on the fixing subgroup. The inverse of their column matrix
is the required row matrix.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4
open _root_.ZInQ.Contrib.HodgeSplit
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
variable {n : ℕ}

private theorem exists_column_matrix_of_span {K : Type*} [Field K]
    (s : Set (Fin n → K)) (hs : ⊤ ≤ Submodule.span K s) :
    ∃ U : GL (Fin n) K, ∀ j, (fun i => U i j) ∈ s := by
  classical
  let c := Module.Basis.ofSpan (K := K) (V := Fin n → K) hs
  let := FiniteDimensional.fintypeBasisIndex c
  let e := Fintype.equivFinOfCardEq ((Module.finrank_eq_card_basis c).symm.trans
    (Module.finrank_fin_fun K))
  let d := c.reindex e
  have hd (j : Fin n) : d j ∈ s :=
    Module.Basis.ofSpan_subset (K := K) (V := Fin n → K) hs
      ⟨e.symm j, Module.Basis.reindex_apply c e j |>.symm⟩
  let P : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => d j i
  have hdet : P.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hvP⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    have hsum : (∑ j, v j • d j) = 0 := by
      funext i
      simpa [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using congrFun hvP i
    exact hv (funext fun j => Fintype.linearIndependent_iff.mp d.linearIndependent v hsum j)
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet, hd⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- A full invariant basis before taking the coefficient quotient suffices.
It need only be invariant on the subgroup fixing the actual coefficients. -/
theorem hasBdRRows_of_invariant_basis (r : GQp p →* GL (Fin n) E)
    {ι : Type*} (b : Module.Basis ι (BdR p) (BdR p ⊗[ℚ_[p]] (Fin n → E)))
    (hb : ∀ i σ, σ ∈ E.fixingSubgroup →
      TensorProduct.map (bdrActHom p σ) (rRep p r σ) (b i) = b i) :
    HasBdRRows p E r := by
  classical
  let L := coeffProjection p E (n := n)
  let s : Set (Fin n → BdR p) := Set.range fun i => L (b i)
  have hs : ⊤ ≤ Submodule.span (BdR p) s := by
    rw [show s = L '' Set.range b from Set.range_comp' L b,
      ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.mpr (coeffProjection_surjective p E)]
  have hcols : ∃ U : GL (Fin n) (BdR p), ∀ j, (fun i => U i j) ∈ s :=
    @exists_column_matrix_of_span n (BdR p) (DeRhamPrint.bdrField p) s hs
  obtain ⟨U, hd⟩ := hcols
  let R : GQp p →* GL (Fin n) (BdR p) :=
    (Matrix.GeneralLinearGroup.map (coeffToBdR p E).toRingHom).comp r
  refine ⟨U⁻¹, fun σ hσ => ?_⟩
  let S := Matrix.GeneralLinearGroup.map (n := Fin n) (bdrAct p σ)
  have hU : R σ * S U = U := by
    apply Units.ext
    ext i j
    obtain ⟨k, hk⟩ := hd j
    change L (b k) = (fun i => U i j) at hk
    have hc := coeffProjection_equivariant p E r σ hσ (b k)
    rw [hb k σ hσ] at hc
    change L (b k) = ((r σ : Matrix (Fin n) (Fin n) E).map (coeffToBdR p E)).mulVec
      (fun i => bdrAct p σ (L (b k) i)) at hc
    rw [hk] at hc
    change (∑ k : Fin n, coeffToBdR p E (r σ i k) * bdrAct p σ (U k j)) = U i j
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply] using (congrFun hc i).symm
  have hS : S U = (R σ)⁻¹ * U := by
    calc
      S U = (R σ)⁻¹ * (R σ * S U) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = _ := congrArg (fun W => (R σ)⁻¹ * W) hU
  calc
    S (U⁻¹) = (S U)⁻¹ := map_inv S U
    _ = U⁻¹ * R σ := by rw [hS, mul_inv_rev, inv_inv]

end HDec.G0Galois.C8Conrad.Manuscript
