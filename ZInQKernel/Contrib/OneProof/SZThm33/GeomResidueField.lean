import ZInQKernel.Contrib.OneProof.SZThm33.RationalFixedTate

/-!
# The ambient valuation has the canonical geometric residue field

The residue polynomial argument adapts the general valuation calculation in
ZInQKernel.Contrib.RC53Assist.TateReduction.Comparison to the exact residue map
of the Néron model.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Polynomial IsLocalRing ReductSplit ReductGlue

namespace SZRaynaud.Ambient

theorem isAlgClosed_residue_of_valuationSubring {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (w : ValuationSubring Ω) : IsAlgClosed (ResidueField w) := by
  refine IsAlgClosed.of_exists_root _ fun f hfm hfi => ?_
  obtain ⟨g, hgf, hgdeg, hgm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts f).mpr (map_surjective (residue w) residue_surjective f)) hfm
  have hdeg : (g.map (algebraMap w Ω)).degree ≠ 0 := by
    rw [degree_eq_natDegree (hgm.map _).ne_zero, hgm.natDegree_map, hgdeg]
    exact_mod_cast hfi.natDegree_pos.ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hint : IsIntegral w α := ⟨g, hgm, by rwa [IsRoot, Polynomial.eval_map] at hα⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨residue w a, ?_⟩
  have h0 : algebraMap w Ω (g.eval a) = 0 := by
    rw [← eval₂_at_apply]
    rwa [IsRoot, Polynomial.eval_map] at hα
  have h1 : g.eval a = 0 := (IsFractionRing.injective w Ω) (by rw [h0, map_zero])
  rw [← hgf, Polynomial.eval_map, eval₂_at_apply, h1, map_zero]

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O)

theorem residue_isAlgebraic_of_isAlgebraic [Algebra.IsAlgebraic K Ω] :
    letI := (resMap hw).toAlgebra
    Algebra.IsAlgebraic (ResidueField O) (ResidueField w) := by
  let := (resMap hw).toAlgebra
  constructor
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨f, hf0, hfx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) (x : Ω)
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image f.support (fun i => O.valuation (f.coeff i))
    (support_nonempty.mpr hf0)
  have hc : f.coeff i₀ ≠ 0 := mem_support_iff.mp hi₀
  have hcoeff (i : ℕ) : (f.coeff i₀)⁻¹ * f.coeff i ∈ O := by
    rw [← O.valuation_le_one_iff]
    by_cases hi : f.coeff i = 0
    · rw [hi, mul_zero, map_zero]
      exact zero_le
    · rw [map_mul, map_inv₀]
      exact inv_mul_le_one_of_le₀ (hmax i (mem_support_iff.mpr hi)) zero_le
  obtain ⟨g, hg⟩ : ∃ g : O[X], g.map (algebraMap O K) = C (f.coeff i₀)⁻¹ * f := by
    rw [← mem_lifts, lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    exact ⟨⟨_, hcoeff n⟩, rfl⟩
  have hg1 : g.coeff i₀ = 1 := by
    apply Subtype.ext
    have h := congrArg (fun q => q.coeff i₀) hg
    simp only [coeff_map, coeff_C_mul, inv_mul_cancel₀ hc] at h
    exact h
  refine ⟨g.map (residue O), fun h => ?_, ?_⟩
  · have h' := congrArg (fun q => q.coeff i₀) h
    simp only [coeff_map, hg1, map_one, coeff_zero] at h'
    exact one_ne_zero h'
  · have hev : g.eval₂ (ReductSplit.comapHom hw) x = 0 := by
      apply Subtype.ext
      have h1 := hom_eval₂ g (ReductSplit.comapHom hw) w.subtype x
      have h2 : w.subtype.comp (ReductSplit.comapHom hw) = (algebraMap K Ω).comp (algebraMap O K) :=
        RingHom.ext fun r => rfl
      rw [h2, ← eval₂_map, hg] at h1
      change w.subtype (g.eval₂ (ReductSplit.comapHom hw) x) = 0
      rw [h1]
      simpa [eval₂_mul, aeval_def] using Or.inr hfx
    have hc₀ : (resMap hw).comp (residue O) = (residue w).comp (ReductSplit.comapHom hw) :=
      RingHom.ext (resMap_residue hw)
    change (g.map (residue O)).eval₂ (resMap hw) (residue w x) = 0
    rw [eval₂_map, hc₀, ← hom_eval₂, hev, map_zero]

theorem isAlgClosure_ambientResidue [IsAlgClosure K Ω] :
    letI := (resMap hw).toAlgebra
    IsAlgClosure (ResidueField O) (ResidueField w) := by
  let := (resMap hw).toAlgebra
  have := IsAlgClosure.isAlgClosed K (K := Ω)
  exact ⟨isAlgClosed_residue_of_valuationSubring w, residue_isAlgebraic_of_isAlgebraic hw⟩

/-- The residue-field equivalence with the model's specified geometric
residue field, obtained over the original residue field. -/
def geomResidueEquiv [IsAlgClosure K Ω] : ResidueField w ≃+* ResBarO O :=
  letI := (resMap hw).toAlgebra
  letI := isAlgClosure_ambientResidue hw
  (IsAlgClosure.equiv (ResidueField O) (ResidueField w) (ResBarO O)).toRingEquiv

theorem geomResidueEquiv_comp [IsAlgClosure K Ω] :
    (geomResidueEquiv hw).toRingHom.comp ((residue w).comp (ReductSplit.comapHom hw)) =
      algebraMap O (ResBarO O) := by
  let := (resMap hw).toAlgebra
  have := isAlgClosure_ambientResidue hw
  ext a
  change geomResidueEquiv hw (residue w (ReductSplit.comapHom hw a)) = _
  rw [← resMap_residue hw a]
  change (IsAlgClosure.equiv (ResidueField O) (ResidueField w) (ResBarO O))
    (algebraMap (ResidueField O) (ResidueField w) (residue O a)) = _
  rw [AlgEquiv.commutes]
  rfl

#print axioms isAlgClosure_ambientResidue
#print axioms geomResidueEquiv_comp

end SZRaynaud.Ambient
