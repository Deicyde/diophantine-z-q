import ZInQKernel.Contrib.OneProof.RC.LocalTorus.CompletedIntegers
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.TorusComparison
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ResidueDegree

/-! The valuation of the absolute ideal norm, and simultaneous matching
of the integral coordinates over one rational prime. On-the-spot (c),
for the norm character in tex 9180–9194. -/

noncomputable section

open scoped NumberField nonZeroDivisors BigOperators
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing

namespace ZInQ.Manuscript.RC.O7Residual

open Adelic PicardFibers LocalTorus

variable {F : Type} [Field F] [NumberField F]

/-- Equality of the exponents above (p) suffices to compare the
(p)-parts of the norms. Each term is weighted by the residue degree. -/
theorem absNorm_factorization_eq_of_counts (p : Prime)
    (J K : Ideal (𝓞 F)) (hJ : J ≠ 0) (hK : K ≠ 0)
    (h : ∀ v : PlacesAbove F p,
      FractionalIdeal.count F v.val (J : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.count F v.val (K : FractionalIdeal (𝓞 F)⁰ F)) :
    (Ideal.absNorm J).factorization p.val = (Ideal.absNorm K).factorization p.val := by
  classical
  let U := (Ideal.hasFiniteMulSupport hJ).toFinset ∪
    (Ideal.hasFiniteMulSupport hK).toFinset
  have factored (I : Ideal (𝓞 F)) (hI : I ≠ 0)
      (hU : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I) ⊆ U) :
      (Ideal.absNorm I).factorization p.val =
        ∑ v ∈ U, (if primeBelow F v = p then Ideal.inertiaDeg v.asIdeal ℤ *
          (Associates.mk v.asIdeal).count (Associates.mk I).factors else 0) := by
    have he := Ideal.finprod_heightOneSpectrum_factorization hI
    rw [finprod_eq_prod_of_mulSupport_subset _ hU] at he
    have hn (v : HeightOneSpectrum (𝓞 F)) :
        Ideal.absNorm (v.maxPowDividing I) ≠ 0 :=
      fun h => (pow_ne_zero _ v.ne_bot) (Ideal.absNorm_eq_zero_iff.mp h)
    conv_lhs => rw [← he, map_prod, Nat.factorization_prod_apply (fun v _ => hn v)]
    apply Finset.sum_congr rfl
    intro v _
    rw [HeightOneSpectrum.maxPowDividing, map_pow, TauCeti.absNorm_eq_rationalPrimeBelow_pow,
      ← pow_mul, (TauCeti.prime_rationalPrimeBelow v).factorization_pow]
    by_cases hv : primeBelow F v = p
    · rw [ite_eq_left hv]
      have hh : TauCeti.rationalPrimeBelow v = p.val := congrArg Subtype.val hv
      rw [hh, Finsupp.single_eq_same]
    · rw [ite_eq_right hv, Finsupp.single_eq_of_ne]
      exact fun he => hv (Subtype.ext he.symm)
  rw [factored J hJ (fun v hv => Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr hv)),
    factored K hK (fun v hv => Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hv))]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : primeBelow F v = p
  · rw [ite_eq_left hv, ite_eq_left hv]
    have hc := h ⟨v, hv⟩
    rw [FractionalIdeal.count_coe _ _ hJ, FractionalIdeal.count_coe _ _ hK,
      Nat.cast_inj] at hc
    rw [hc]
  · simp only [ite_eq_right hv]

/-- An integral block has the same valuations as one nonzero global
integer. Density supplies the simultaneous approximation. -/
theorem exists_integer_of_block (p : Prime) (u : ∀ v : PlacesAbove F p, (v.val.adicCompletion F)ˣ)
    (hu : ∀ v : PlacesAbove F p, Valued.v (u v).val ≤ 1) :
    ∃ k : 𝓞 F, k ≠ 0 ∧ ∀ v : PlacesAbove F p,
      Valued.v (algebraMap (𝓞 F) (v.val.adicCompletion F) k) = Valued.v (u v).val := by
  classical
  let x (v : PlacesAbove F p) : v.val.adicCompletionIntegers F := ⟨(u v).val, hu v⟩
  have hne (v : PlacesAbove F p) : Valued.v (u v).val ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (u v).ne_zero
  have hw : {y : ∀ v : PlacesAbove F p, v.val.adicCompletionIntegers F |
      ∀ v, Valued.v (y v).val = Valued.v (u v).val} ∈ nhds x := by
    rw [nhds_pi]
    apply Filter.mem_pi.mpr
    refine ⟨Set.univ, Set.finite_univ, fun v => {y | Valued.v y.val = Valued.v (u v).val},
      ?_, ?_⟩
    · intro v
      exact continuous_subtype_val.continuousAt (Valued.locally_const (hne v))
    · exact fun _ h v => h v (Set.mem_univ v)
  obtain ⟨k, hk⟩ := (denseRange_diagonal_integers (F := F) p).mem_nhds hw
  by_cases h0 : k = 0
  · refine ⟨1, one_ne_zero, fun v => (hne v ?_).elim⟩
    have he := hk v
    simpa [h0] using he.symm
  · exact ⟨k, h0, hk⟩

end ZInQ.Manuscript.RC.O7Residual
