import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceOrbitForms

/-!
# Actual split-label motions and trace averaging

Principal-group motions act only on the prime part of a coprime split label.
The normalized trace is constant along the genuine raw-product orbit. A
nonempty finite orbit sum can therefore be divided by its proved nonzero
cardinality, without an assumed stabilizer multiplicity formula.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation TorsionCorrelationLower TorsionQuadraticGenerators DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

lemma pointAction_scale (M : ℕ) (γ : SL(2, ℤ)) (s : ZMod M) (T : Point M) :
    pointAction M γ (scale s T) = scale s (pointAction M γ T) := by
  apply Prod.ext <;> simp [pointAction, scale] <;> ring

lemma reducePoint_action (n m : ℕ) (hnm : n ∣ m) (γ : SL(2, ℤ)) (P : Point m) :
    reducePoint n m hnm (pointAction m γ P) = pointAction n γ (reducePoint n m hnm P) := by
  apply Prod.ext <;> simp only [reducePoint, pointAction, Prod.fst, Prod.snd,
    map_add, map_mul, map_intCast]

/-- The lower component is actually fixed and only the prime component moves. -/
theorem splitPoint_action (p N : ℕ) [NeZero p] [NeZero N] (hcop : Nat.Coprime p N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) (A : Point N) (T : Point p) :
    pointAction (p * N) γ (splitPoint p N A T) = splitPoint p N A (pointAction p γ T) := by
  apply point_eq_of_reductions p N hcop
  · rw [reducePoint_action, reduce_split_p, pointAction_scale, reduce_split_p]
  · rw [reducePoint_action, reduce_split_N, pointAction_Gamma N γ hγ, reduce_split_N]

/-- A field row-pair motion lifts to an actual principal-group split-label motion. -/
theorem exists_Gamma_split_pair_move (p N : ℕ) [Fact p.Prime] [NeZero N] (hcop : Nat.Coprime p N)
    (A B : Point N) (T0 U0 T U : Point p) (G : SL(2, ZMod p))
    (hT : ![T0.1,T0.2] ᵥ* G.1 = ![T.1,T.2])
    (hU : ![U0.1,U0.2] ᵥ* G.1 = ![U.1,U.2]) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma N ∧
      pointAction (p * N) γ (splitPoint p N A T0) = splitPoint p N A T ∧
      pointAction (p * N) γ (splitPoint p N B U0) = splitPoint p N B U := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨γ, hγ, hmap⟩ := exists_mem_Gamma_map_intCast_zmod_eq hcop G
  have he (i j : Fin 2) : (γ i j : ZMod p) = G i j := by
    have h := congrArg (fun g : SL(2, ZMod p) => g i j) hmap
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Int.coe_castRingHom] using h
  have hact (P Q : Point p) (hv : ![P.1,P.2] ᵥ* G.1 = ![Q.1,Q.2]) : pointAction p γ P = Q := by
    apply Prod.ext
    · have h := congrFun hv 0
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, pointAction, he] using h
    · have h := congrFun hv 1
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, pointAction, he] using h
  refine ⟨γ, hγ, ?_, ?_⟩
  · rw [splitPoint_action p N hcop γ hγ, hact T0 T hT]
  · rw [splitPoint_action p N hcop γ hγ, hact U0 U hU]

lemma rawProductForm_slash (M : ℕ) (hM : 0 < M) (P Q : Point M) (γ : SL(2, ℤ)) :
    (⇑(rawProductForm M hM P Q)) ∣[(2 : ℤ)] γ =
      ⇑(rawProductForm M hM (pointAction M γ P) (pointAction M γ Q)) := by
  change (((⇑(rawForm M hM P) : ℍ → ℂ) * ⇑(rawForm M hM Q)) ∣[(1 + 1 : ℤ)] γ) = _
  rw [ModularForm.mul_slash_SL2, rawForm_slash, rawForm_slash]
  rfl

/-- Actual raw-product trace constancy, including all zero classes. -/
theorem normalizedTrace_rawProduct_action (N M : ℕ) (hM : 0 < M)
    (P Q : Point M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) :
    normalizedTrace N M hM (rawProductForm M hM (pointAction M γ P) (pointAction M γ Q)) =
      normalizedTrace N M hM (rawProductForm M hM P Q) := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let _ := DivisionEisensteinLowerClosure.mapped_principal_subgroup_normal N M
  let I := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype I := Fintype.ofFinite I
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  have hs : ⇑(rawProductForm M hM (pointAction M γ P) (pointAction M γ Q)) =
      (⇑(rawProductForm M hM P Q) : ℍ → ℂ) ∣[(2 : ℤ)] mapGL ℝ γ :=
    (rawProductForm_slash M hM P Q γ).symm
  have he (q : I) :
      SlashInvariantForm.quotientFunc (rawProductForm M hM (pointAction M γ P) (pointAction M γ Q)) q =
      SlashInvariantForm.quotientFunc (rawProductForm M hM P Q) (MulOpposite.op g⁻¹ • q) := by
    induction q using QuotientGroup.induction_on' with
    | H r =>
      rw [MulAction.Quotient.smul_coe, SlashInvariantForm.quotientFunc_mk,
        SlashInvariantForm.quotientFunc_mk, hs, ← SlashAction.slash_mul]
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Subgroup.coe_mul,
        Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, g]
  rw [normalizedTrace_apply, normalizedTrace_apply]
  apply congrArg (fun F : _root_.ModularForm (ΓP N) 2 => (traceIndex N M : ℂ)⁻¹ • F)
  apply DFunLike.coe_injective
  rw [_root_.ModularForm.coe_trace, _root_.ModularForm.coe_trace]
  simp_rw [he]
  exact Equiv.sum_comp (MulAction.toPerm (MulOpposite.op g⁻¹))
    (SlashInvariantForm.quotientFunc (rawProductForm M hM P Q))

/-- Genuine nonempty finite-orbit averaging; the lower sum form and its
membership are supplied only after being constructed and proved. -/
theorem trace_of_finite_orbit_sum {I : Type*} [Fintype I] (i0 : I)
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hNM : N ∣ M)
    (f : I → _root_.ModularForm (ΓP M) 2) (f0 : _root_.ModularForm (ΓP M) 2)
    (R : _root_.ModularForm (ΓP N) 2) (hR : R ∈ productSpan N hN)
    (hsum : ∑ i, f i = restriction N M hNM R)
    (hconst : ∀ i, normalizedTrace N M hM (f i) = normalizedTrace N M hM f0) :
    normalizedTrace N M hM f0 ∈ productSpan N hN := by
  let : Nonempty I := ⟨i0⟩
  have hc : (Fintype.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have he : (Fintype.card I : ℂ) • normalizedTrace N M hM f0 = R := by
    calc (Fintype.card I : ℂ) • normalizedTrace N M hM f0 =
        ∑ i, normalizedTrace N M hM (f i) := by simp [hconst, Nat.cast_smul_eq_nsmul]
      _ = normalizedTrace N M hM (∑ i, f i) := (map_sum _ _ _).symm
      _ = R := by rw [hsum, normalizedTrace_restriction hM hNM R]
  have h := congrArg (fun F : _root_.ModularForm (ΓP N) 2 => (Fintype.card I : ℂ)⁻¹ • F) he
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  rw [h]
  exact Submodule.smul_mem _ _ hR

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
