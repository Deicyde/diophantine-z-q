import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Topology.Sequences
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Norm

/-! The finite complete coefficient extension in tex 9649–9654.
The compositum already sits in `ℂ`; the complex embedding of its completion
extends that algebraic inclusion and does not use the complex topology. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open NumberField IsDedekindDomain HeightOneSpectrum
open scoped AdicCompletionExtension NNReal Cardinal Topology

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E]
variable [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

omit [NumberField E] in
/-- Every finite constituent compositum admits a place over the fixed prime. -/
theorem exists_constituent_place :
    ∃ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 E) v.asIdeal
  let := hQv
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hQv⟩

variable (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

theorem constituent_completion_finite :
    FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) := by
  let : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let : Finite (𝓞 E ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  exact TauCeti.finite_of_valuativeExtension _ _

/-- The ordinary completed field has the valuation scale of its own residue
field. Its local degree is the exponent by which that scale differs from `v`. -/
def constituentLocalDegree : ℕ :=
  Module.finrank (v.adicCompletion F) (w.adicCompletion E)

private theorem constituentLocalDegree_pos : 0 < constituentLocalDegree v w := by
  let := constituent_completion_finite v w
  exact Module.finrank_pos

private def rootNormHom (d : ℕ) (hd : 0 < d) : ℝ≥0 →*₀o ℝ≥0 where
  toFun x := x ^ (d : ℝ)⁻¹
  map_zero' := NNReal.zero_rpow (by positivity)
  map_one' := NNReal.one_rpow _
  map_mul' _ _ := NNReal.mul_rpow
  monotone' := NNReal.monotone_rpow_of_nonneg (by positivity)

private def ordinaryNormHom : WithZero (Multiplicative ℤ) →*₀o ℝ≥0 where
  toMonoidWithZeroHom := WithZeroMulInt.toNNReal (absNorm_ne_zero w)
  monotone' := (WithZeroMulInt.toNNReal_strictMono (one_lt_absNorm_nnreal w)).monotone

/-- The valuation of the receiving completion normalized to restrict to the
fixed field's absolute value. -/
def constituentValuation : Valuation (w.adicCompletion E) ℝ≥0 :=
  (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).map
    ((rootNormHom (constituentLocalDegree v w) (constituentLocalDegree_pos v w)).comp
      (ordinaryNormHom w))

private theorem constituentValuation_equiv :
    (constituentValuation v w).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  rw [Valuation.isEquiv_iff_val_lt_val]
  intro x y
  change (ordinaryNormHom w (Valued.v x)) ^ (constituentLocalDegree v w : ℝ)⁻¹ <
    (ordinaryNormHom w (Valued.v y)) ^ (constituentLocalDegree v w : ℝ)⁻¹ ↔ _
  have hd := constituentLocalDegree_pos v w
  rw [NNReal.rpow_lt_rpow_iff (by positivity)]
  exact (WithZeroMulInt.toNNReal_strictMono (one_lt_absNorm_nnreal w)).lt_iff_lt

theorem constituentValuation_extends (x : v.adicCompletion F) :
    constituentValuation v w (v.adicCompletionExtension F E w x) = ‖x‖₊ := by
  have hnorm (y : w.adicCompletion E) :
      ordinaryNormHom w (Valued.v y) = ‖y‖₊ := by
    apply NNReal.eq
    exact (FinitePlace.norm_def w y).symm
  change ordinaryNormHom w (Valued.v (v.adicCompletionExtension F E w x)) ^
      ((constituentLocalDegree v w : ℕ) : ℝ)⁻¹ = ‖x‖₊
  rw [hnorm]
  have hpow : ‖v.adicCompletionExtension F E w x‖₊ = ‖x‖₊ ^ constituentLocalDegree v w := by
    apply NNReal.eq
    exact v.norm_adicCompletionExtension w x
  have hd : (constituentLocalDegree v w : ℝ) ≠ 0 := by
    exact_mod_cast (constituentLocalDegree_pos v w).ne'
  rw [hpow, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, mul_inv_cancel₀ hd, NNReal.rpow_one]

/-- Normalizing the valuation does not change completeness. -/
theorem constituentValuation_complete :
    @CompleteSpace _ (Valued.mk' (constituentValuation v w)).toUniformSpace := by
  let v₀ : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)) := Valued.v
  have hu : (Valued.mk' v₀).toUniformSpace = (inferInstance : UniformSpace (w.adicCompletion E)) :=
    (Valued.toUniformSpace_eq (w.adicCompletion E) (WithZero (Multiplicative ℤ))).symm
  have he := constituentValuation_equiv v w
  have hU : (Valued.mk' (constituentValuation v w)).toUniformSpace =
      (Valued.mk' v₀).toUniformSpace := le_antisymm
    (le_iff_uniformContinuous_id.mpr he.symm.uniformContinuous)
    (le_iff_uniformContinuous_id.mpr he.uniformContinuous)
  rw [hU, hu]
  exact inferInstance

/-- Agreement with the ring of integers at the receiving place. -/
theorem constituentValuation_integral (x : w.adicCompletion E) :
    (∃ z : w.adicCompletionIntegers E, (z : w.adicCompletion E) = x) ↔
      constituentValuation v w x ≤ 1 := by
  rw [Valuation.isEquiv_iff_val_le_one.mp (constituentValuation_equiv v w)]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ (mem_adicCompletionIntegers _ _ _).mp z.property,
    fun hx => ⟨⟨x, (mem_adicCompletionIntegers _ _ _).mpr hx⟩, rfl⟩⟩

/-- Agreement with the maximal ideal at the receiving place. -/
theorem constituentValuation_maximal (z : w.adicCompletionIntegers E) :
    z ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔
      constituentValuation v w (z : w.adicCompletion E) < 1 := by
  rw [Valuation.isEquiv_iff_val_lt_one.mp (constituentValuation_equiv v w)]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion E)
    (WithZero (Multiplicative ℤ))))

section ComplexEmbedding

open Cardinal Filter

variable {D : Type} [Field D] [NumberField D] (u : HeightOneSpectrum (𝓞 D))

private theorem numberField_mk_le (D : Type) [Field D] [NumberField D] : #D ≤ ℵ₀ := by
  simpa using Algebra.IsAlgebraic.cardinalMk_le_max ℚ D

private theorem mk_constituentCompletion_le : #(u.adicCompletion D) ≤ #ℂ := by
  have h (x : u.adicCompletion D) :
      ∃ f : ℕ → D, Tendsto (fun n => algebraMap D (u.adicCompletion D) (f n)) atTop (𝓝 x) := by
    obtain ⟨c, hc, hx⟩ := mem_closure_iff_seq_limit.mp ((u.denseRange_algebraMap D) x)
    choose f hf using hc
    exact ⟨f, by simpa only [hf] using hx⟩
  choose f hf using h
  have hinj : Function.Injective f := by
    intro x y he
    have hy := hf y
    rw [← he] at hy
    exact tendsto_nhds_unique (hf x) hy
  calc
    #(u.adicCompletion D) ≤ #(ℕ → D) := mk_le_of_injective hinj
    _ = #D ^ ℵ₀ := by rw [mk_arrow, lift_id, lift_id, mk_nat]
    _ ≤ ℵ₀ ^ ℵ₀ := power_le_power_right (numberField_mk_le D)
    _ = #ℂ := by rw [aleph0_power_aleph0, mk_complex]

variable [Algebra D ℂ]

/-- Extend the given embedding of the algebraic constituent field into `ℂ`
to an algebraic map of fields on its completion. The completion need not
be algebraic over the number field; first map a transcendence basis. -/
def constituentComplexEmbedding : u.adicCompletion D →ₐ[D] ℂ := by
  classical
  let K := u.adicCompletion D
  let s : Set K := (exists_isTranscendenceBasis D K).choose
  have hs := (exists_isTranscendenceBasis D K).choose_spec
  let t : Set ℂ := (exists_isTranscendenceBasis D ℂ).choose
  have ht := (exists_isTranscendenceBasis D ℂ).choose_spec
  have htcard : #t = #ℂ := (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
    _ ht (numberField_mk_le D) (by rw [mk_complex]; exact aleph0_lt_continuum)).symm
  have hst : #s ≤ #t := (mk_subtype_le _).trans ((mk_constituentCompletion_le u).trans_eq htcard.symm)
  let j : s ↪ t := ((le_def s t).1 hst).some
  let A := Algebra.adjoin D (Set.range ((↑) : s → K))
  let g : A →ₐ[D] ℂ := (MvPolynomial.aeval (fun x : s => (j x : ℂ))).comp
    hs.1.aevalEquiv.symm.toAlgHom
  have hj : AlgebraicIndependent D (fun x : s => (j x : ℂ)) := ht.1.comp j j.injective
  have hg : Function.Injective g :=
    (algebraicIndependent_iff_injective_aeval.mp hj).comp hs.1.aevalEquiv.symm.injective
  letI : Algebra A ℂ := g.toRingHom.toAlgebra
  letI : Module.IsTorsionFree A ℂ := Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  letI : IsScalarTower D A ℂ := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  letI : Algebra.IsAlgebraic A K := hs.isAlgebraic
  exact (IsAlgClosed.lift : K →ₐ[A] ℂ).restrictScalars D

theorem constituentComplexEmbedding_constituent (x : D) :
    constituentComplexEmbedding u (FinitePlace.embedding u x) = algebraMap D ℂ x :=
  (constituentComplexEmbedding u).commutes x

variable {F : Type*} [Field F] [NumberField F] [Algebra F D]
variable (v : HeightOneSpectrum (𝓞 F)) [u.asIdeal.LiesOver v.asIdeal]

theorem constituentComplexEmbedding_fixed (x : F) :
    constituentComplexEmbedding u
      (v.adicCompletionExtension F D u (FinitePlace.embedding v x)) =
    algebraMap D ℂ (algebraMap F D x) := by
  rw [FinitePlace.embedding_apply, adicCompletionExtension_coe]
  exact constituentComplexEmbedding_constituent u _

end ComplexEmbedding

end ZInQ.Manuscript.RC.EvenJoin
