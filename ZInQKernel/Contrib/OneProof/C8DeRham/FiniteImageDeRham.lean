import ZInQKernel.Contrib.OneProof.C8DeRham.ActualBdRCoefficients

/-! # Finite-image representations are de Rham

This supplies the de Rham, not just Hodge–Tate, part of the weight-one branch
of C8 after Deligne–Serre. The restriction to a finite Galois fixing subgroup
is trivial; finite descent and the proved B_dR fixed-field theorem compute the
full invariant dimension on the original local group.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4
open _root_.ZInQ.Contrib.HodgeSplit Module

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- A representation trivial on a finite Galois fixing subgroup is de Rham. -/
theorem isDeRham_of_galois_trivial (p : ℕ) [Fact p.Prime]
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M] [IsGalois ℚ_[p] M]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E] {n : ℕ}
    (r : GQp p →* GL (Fin n) E) (htriv : ∀ σ ∈ M.fixingSubgroup, r σ = 1) :
    IsDeRham p r := by
  let γ : GQp p →* (M ≃ₐ[ℚ_[p]] M) := AlgEquiv.restrictNormalHom M
  have hγ : Function.Surjective γ := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)
  have hker : (γ.ker : Set (GQp p)) = (M.fixingSubgroup : Set (GQp p)) := by
    rw [IntermediateField.restrictNormalHom_ker]
  have hsemi (g : GQp p) (x : M) (b : BdR p) :
      bdrActHom p g (coeffToBdR p M x * b) = coeffToBdR p M (γ g x) * bdrActHom p g b := by
    rw [bdrActHom_apply, bdrActHom_apply, map_mul, bdrAct_coeffToBdR_restrict]
  have hd := descent_finrank (bdrActHom p) (rRep p r) (coeffToBdR p M) γ hγ hsemi
  rw [← ddrSpace_eq_DspAct] at hd
  have hρ : ∀ g ∈ (γ.ker : Set (GQp p)), rRep p r g = LinearMap.id := by
    intro g hg
    rw [hker] at hg
    refine LinearMap.ext fun v => ?_
    rw [rRep_apply, htriv g hg]
    simp
  let J := (coeffToBdR p M).toLinearMap
  let W := LinearMap.range J
  have hW : ∀ x, x ∈ W ↔ ∀ g ∈ (γ.ker : Set (GQp p)), bdrActHom p g x = x := by
    intro x
    rw [hker]
    constructor
    · rintro ⟨y, rfl⟩ g hg
      exact bdrAct_coeffToBdR p M g hg y
    · intro hx
      exact exists_coeffToBdR_of_fixed p M x hx
  have hdW : finrank ℚ_[p] W = finrank ℚ_[p] M := LinearMap.finrank_range_of_inj (coeffToBdR p M).injective
  have hM : 0 < finrank ℚ_[p] M := Module.finrank_pos
  letI : FiniteDimensional ℚ_[p] W := Module.finite_of_finrank_pos (hdW ▸ hM)
  have he := finrank_Dsp_triv (bdrActHom p) (rRep p r) (γ.ker : Set (GQp p)) hρ W hW
  rw [he, hdW, Module.finrank_pi_fintype] at hd
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hd
  change finrank ℚ_[p] (ddrSpace p r) = n * finrank ℚ_[p] E
  apply Nat.eq_of_mul_eq_mul_left hM
  rw [← hd, mul_comm]

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 300000 in
/-- A continuous finite-image local representation is genuinely de Rham
in the project's finite-coefficient model and fixed algebraic closure. -/
theorem localIsDeRham_of_finite_image (p : ℕ) [Fact p.Prime] {n : ℕ}
    (r : GQp p →* GL (Fin n) (PadicAlgCl p)) (hc : Continuous r) (hfin : (Set.range r).Finite) :
    LocalIsDeRham p n r := by
  obtain ⟨E, hE, hmem⟩ := exists_coef_field p r hfin
  letI : FiniteDimensional ℚ_[p] E := hE
  obtain ⟨M, hM, hGal, htriv⟩ := exists_galois_trivial p r hc hfin
  letI : FiniteDimensional ℚ_[p] M := hM
  letI : IsGalois ℚ_[p] M := hGal
  let rE := liftGL E r hmem
  have hρ : ∀ σ ∈ M.fixingSubgroup, rE σ = 1 := by
    intro σ hσ
    have hm := liftGL_map E r hmem σ
    rw [htriv σ hσ] at hm
    apply Units.ext
    apply Matrix.map_injective (algebraMap E (PadicAlgCl p)).injective
    have he := congrArg (fun u : GL (Fin n) (PadicAlgCl p) => (u : Matrix (Fin n) (Fin n) (PadicAlgCl p))) hm
    change ((rE σ : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl p))) = 1 at he
    change ((rE σ : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl p))) =
      (1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (PadicAlgCl p))
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact he
  exact ⟨E, inferInstance, rE, liftGL_map E r hmem, isDeRham_of_galois_trivial p M rE hρ⟩

/-- Deligne–Serre's finite-image conclusion can therefore feed the exact
local de Rham receiver, not a substituted Hodge–Tate receiver. -/
theorem localIsDeRham_restrictLocal_of_finite_image (p : ℕ) [Fact p.Prime] {n : ℕ}
    (r : GaloisRep p n) (hfin : (Set.range r.toHom).Finite) : LocalIsDeRham p n (r.restrictLocal p) :=
  localIsDeRham_of_finite_image p (r.restrictLocal p) (continuous_restrictLocal p r)
    (hfin.subset (Set.range_comp_subset_range (decomp p) r.toHom))

end HDec.G0Galois.C8Conrad.Manuscript
