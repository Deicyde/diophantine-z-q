import ZInQKernel.Contrib.OneProof.C8Printed

/-! # The pre-comparison weight of the actual C8 twisting line

The finite-coefficient period argument in `TailT` is used without specializing
any modular weight. We retain the Hodge–Tate witness of the character, rather
than just the equality of the two weight multisets. This is a `ℂ_p` calculation;
it does not assert the stronger `B_dR`-admissibility of the twisting line.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open Module _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.HodgeSplit
open _root_.ZInQ.Contrib.G9.PkgI4 (GQp GaloisRep GaloisChar decomp cpAct cycPow htMult htSpace)

private theorem tateInvariants : TateTwistInvariants :=
  ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof

private theorem fixedField : AxSenTate := ZInQ.Contrib.CloudB3W11.axSenTate_proof

set_option maxHeartbeats 1800000 in
/-- If the scalar action by `ψ` has a nonzero period in weight `s` over the
coefficient fixing subgroup, its unique weight in the Tate convention is `-s`.
Uses only the already-proved Tate–Sen dimension bounds. -/
theorem hasHTWeights_of_inverse_period (p : ℕ) [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
    (ψ : GQp p →* Eˣ) (s : ℤ) (β : ℂ_[p]) (hβ : β ≠ 0)
    (hrel : ∀ σ ∈ E.fixingSubgroup,
      cpAct p σ β = (algebraMap E ℂ_[p] (ψ σ : E))⁻¹ * (cycPow p σ s • β)) :
    HDec.PkgI4.HasHTWeights p (charRep ψ) {-s} := by
  let cv : Fin 1 → ℂ_[p] := fun _ => β⁻¹
  have hcv0 : cv ≠ 0 := fun h => (inv_ne_zero hβ) (congrFun h 0)
  have hc (σ : GQp p) : algebraMap E ℂ_[p] (ψ σ : E) ≠ 0 := (map_ne_zero _).mpr (ψ σ).ne_zero
  have hcyc (σ : GQp p) : algebraMap ℚ_[p] ℂ_[p] (cycPow p σ s) ≠ 0 := by
    intro hz
    have he := map_mul (algebraMap ℚ_[p] ℂ_[p]) (cycPow p σ (-s)) (cycPow p σ s)
    rw [cycPow_neg_mul, map_one, hz, mul_zero] at he
    exact one_ne_zero he
  have hcv : cv ∈ Ysp p (charRep ψ) s E := by
    intro σ hσ
    ext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have hm : ((charRep ψ σ : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) 0 0 = (ψ σ : E) := by
      simp [charRep, Matrix.algebraMap_matrix_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.transpose_apply, matC,
      Matrix.map_apply, Pi.smul_apply, vAct, hm, cv, Algebra.smul_def, map_inv₀, hrel σ hσ]
    field_simp [hc σ, hcyc σ, hβ]
  intro w
  change htMult p (charRep ψ) w = ({-s} : Multiset ℤ).count w
  rw [htMult_eq_finrank_Ysp p tateInvariants fixedField E (charRep ψ) w]
  letI : ∀ i : ℤ, FiniteDimensional E (Ysp p (charRep ψ) i E) := fun i =>
    Ysp_finiteDimensional p tateInvariants fixedField E (charRep ψ) i
  by_cases hw : w = -s
  · subst w
    rw [neg_neg, Multiset.count_singleton_self]
    have hne : Ysp p (charRep ψ) s E ≠ ⊥ := fun h =>
      hcv0 ((Submodule.mem_bot E).mp (h ▸ hcv))
    have : Module.IsTorsionFree E (Fin 1 → ℂ_[p]) := DivisionSemiring.to_moduleIsTorsionFree
    have hpos : 0 < Module.finrank E (Ysp p (charRep ψ) s E) :=
      Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
    have hle := TwistHT.finrank_Ysp_le p E (charRep ψ) s
    omega
  · rw [Multiset.count_singleton, if_neg hw]
    by_contra hne
    have hy : Ysp p (charRep ψ) (-w) E ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hne
      exact hne rfl
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy
    have hli := TwistHT.linIndep_two p E (charRep ψ) s (-w) (by omega) cv z hcv hz hcv0 hz0
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fin_fun] at hcard
    omega

set_option maxHeartbeats 2200000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- From a scalar twist of two Hodge–Tate representations of full rank, retain
both the actual local coefficient character and its integral weight. Neither
input multiset is fixed to `{0, -1}`. The proof extracts one nonzero coordinate
of the Hom period, as in `exists_twist_scalar`, and applies the same period to
the weight spaces of the two representations. -/
theorem actualTwistHT_and_shift (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n)
    (ρ ρ' : GaloisRep p n) (ψ : GaloisChar p) (S S' : Multiset ℤ)
    (htw : ZInQ.Contrib.HodgeSplit.G0Galois.IsTwist ρ' ψ ρ)
    (hS : S.card = n) (hS' : S'.card = n)
    (hρ : ρ.HasHTWeightsAtSelf p S) (hρ' : ρ'.HasHTWeightsAtSelf p S') :
    ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
      (_ : IsGalois ℚ_[p] E) (ψE : GQp p →* Eˣ) (w : ℤ),
      (∀ σ, (((ψE σ : Eˣ) : E) : PadicAlgCl p) = (ψ.toHom (decomp p σ) : PadicAlgCl p)) ∧
      HDec.PkgI4.HasHTWeights p (charRep ψE) {w} ∧ S' = S.map (· + w) := by
  classical
  obtain ⟨E₁, hE₁, ρ₁, h₁, hw₁⟩ := hρ
  obtain ⟨E₂, hE₂, ρ₂, h₂, hw₂⟩ := hρ'
  let E₀ := E₁ ⊔ E₂
  let E := IntermediateField.normalClosure ℚ_[p] E₀ (PadicAlgCl p)
  haveI : FiniteDimensional ℚ_[p] E := inferInstance
  haveI : IsGalois ℚ_[p] E := IsGalois.mk
  have hE₀E : E₀ ≤ E := IntermediateField.le_normalClosure E₀
  let ρL := ρ.restrictLocal p
  let ρ'L := ρ'.restrictLocal p
  have hent₁ : ∀ σ i j, (((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j : E₁) : PadicAlgCl p) =
      (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro σ i j; rw [← h₁ σ]; rfl
  have hent₂ : ∀ σ i j, (((ρ₂ σ : Matrix (Fin n) (Fin n) E₂) i j : E₂) : PadicAlgCl p) =
      (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro σ i j; rw [← h₂ σ]; rfl
  have hmem : ∀ σ i j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E := by
    intro σ i j; rw [← hent₁]
    exact hE₀E ((le_sup_left : E₁ ≤ E₀) ((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j).2)
  have hmem' : ∀ σ i j, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E := by
    intro σ i j; rw [← hent₂]
    exact hE₀E ((le_sup_right : E₂ ≤ E₀) ((ρ₂ σ : Matrix (Fin n) (Fin n) E₂) i j).2)
  let ρE := liftGL E ρL hmem
  let ρ'E := liftGL E ρ'L hmem'
  have hwE : ∀ w, htMult p ρE w = S.count w := fun w =>
    (htMult_eq_of_lifts p ρL ρE ρ₁ (liftGL_map E ρL hmem) h₁ w).trans (hw₁ w)
  have hw'E : ∀ w, htMult p ρ'E w = S'.count w := fun w =>
    (htMult_eq_of_lifts p ρ'L ρ'E ρ₂ (liftGL_map E ρ'L hmem') h₂ w).trans (hw₂ w)
  have htwL : ∀ σ, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
      (ψ.toHom (decomp p σ) : PadicAlgCl p) • (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) :=
    fun σ => htw (decomp p σ)
  have hψmem : ∀ σ, (ψ.toHom (decomp p σ) : PadicAlgCl p) ∈ E := by
    intro σ
    have hdet : (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero _
    obtain ⟨j, hj⟩ : ∃ j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j ≠ 0 := by
      by_contra! h
      exact hdet (Matrix.det_eq_zero_of_row_eq_zero ⟨0, hn⟩ h)
    have e := congrFun (congrFun (htwL σ) ⟨0, hn⟩) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    have : (ψ.toHom (decomp p σ) : PadicAlgCl p) =
        (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j /
          (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j := by
      rw [e, mul_div_assoc, div_self hj, mul_one]
    rw [this]
    exact E.div_mem (hmem' σ _ _) (hmem σ _ _)
  let c : GQp p → E := fun σ => ⟨(ψ.toHom (decomp p σ) : PadicAlgCl p), hψmem σ⟩
  have hc0 : ∀ σ, c σ ≠ 0 := fun σ h =>
    (ψ.toHom (decomp p σ)).ne_zero (congrArg Subtype.val h)
  let ψE : GQp p →* Eˣ :=
    { toFun := fun σ => Units.mk0 (c σ) (hc0 σ)
      map_one' := Units.ext (Subtype.ext (by change (ψ.toHom (decomp p 1) : PadicAlgCl p) = 1; simp))
      map_mul' := fun a b => Units.ext (Subtype.ext (by
        change (ψ.toHom (decomp p (a * b)) : PadicAlgCl p) =
          (ψ.toHom (decomp p a) : PadicAlgCl p) * (ψ.toHom (decomp p b) : PadicAlgCl p)
        simp)) }
  have hc : ∀ σ, matC p (ρ'E σ : Matrix (Fin n) (Fin n) E) =
      algebraMap E ℂ_[p] (c σ) • matC p (ρE σ : Matrix (Fin n) (Fin n) E) := by
    intro σ
    ext a b
    have hE : ((ρ'E σ : Matrix (Fin n) (Fin n) E) a b) = c σ * ((ρE σ : Matrix (Fin n) (Fin n) E) a b) :=
      Subtype.ext (by
        change (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) a b =
          (ψ.toHom (decomp p σ) : PadicAlgCl p) * (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) a b
        rw [htwL σ]
        rfl)
    simp only [matC, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hE, map_mul]
  have hdY : ∀ i, Module.finrank E (Ysp p ρE i E) = S.count (-i) := by
    intro i; rw [← hwE, htMult_eq_finrank_Ysp p tateInvariants fixedField E ρE (-i), neg_neg]
  have hdY' : ∀ i, Module.finrank E (Ysp p ρ'E i E) = S'.count (-i) := by
    intro i; rw [← hw'E, htMult_eq_finrank_Ysp p tateInvariants fixedField E ρ'E (-i), neg_neg]
  let J' : Finset ℤ := (S'.map fun w => -w).toFinset
  have hsum : ∑ j ∈ J', Module.finrank E (Ysp p ρ'E j E) = n := by
    simp only [hdY']
    have hJ : J' = S'.toFinset.map ⟨fun w => -w, neg_injective⟩ := by
      ext j; simp [J']
    rw [hJ, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, neg_neg]
    rw [Multiset.toFinset_sum_count_eq, hS']
  obtain ⟨ι, _, b, jb, hb⟩ := exists_basis_Ysp p tateInvariants fixedField E ρ'E J' hsum
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∈ S := by
    have : S ≠ 0 := by
      intro h; rw [h, Multiset.card_zero] at hS; omega
    exact Multiset.exists_mem_of_ne_zero this
  have hne : Ysp p ρE (-w₀) E ≠ ⊥ := by
    intro h
    have := hdY (-w₀)
    rw [h, finrank_bot, neg_neg] at this
    exact (Multiset.count_ne_zero.mpr hw₀) this.symm
  obtain ⟨y₀, hy₀, hy₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨s, β, hβ, hrel⟩ := exists_twist_scalar p ρE ρ'E c hc hc0 b jb hb hy₀ hy₀ne
  have hdim : ∀ i, Module.finrank E (Ysp p ρE i E) = Module.finrank E (Ysp p ρ'E (i + s) E) :=
    finrank_Ysp_twist p ρE ρ'E c hc hc0 s β hβ hrel
  refine ⟨E, inferInstance, inferInstance, ψE, -s, fun _ => rfl,
    hasHTWeights_of_inverse_period p E ψE s β hβ hrel, ?_⟩
  symm
  ext u
  have e1 : S.count (u + s) = S'.count u := by
    have := hdim (-(u + s))
    rw [hdY, hdY', neg_neg] at this
    rw [this]
    congr 1
    ring
  have e2 : (S.map (· + -s)).count u = S.count (u + s) := by
    have := Multiset.count_map_eq_count' (fun w => w + -s) S (add_left_injective _) (u + s)
    simp only [add_neg_cancel_right] at this
    exact this
  rw [e2, e1]

end HDec.G0Galois.C8Conrad.Manuscript
