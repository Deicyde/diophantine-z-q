import InertiaFieldValuationV004
import UnramifiedAtFromValuationV002

/-!
# Inertia-fixed embedded fields are unramified at `w`: `Algebra.IsUnramifiedAt`

Let `K` be a number field, `O ⊆ K` a discrete valuation subring, `Ω` an algebraic closure, `w` a
valuation subring of `Ω` above `O`, and `ι : M' →ₐ[K] Ω` a `K`-embedding of a finite extension
`M'` whose image is fixed by the inertia subgroup of `w`. Let `B` be the integral closure of `O` in
`M'` and `Q = {b ∈ B | v_w(ι b) < 1}` the center of `w` on `B`. Then `B` is unramified over `O` at
`Q` (`Algebra.IsUnramifiedAt O Q`), and `Q` has ramification index one.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open IsLocalRing

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
variable {M' : Type*} [Field M'] [Algebra K M'] [FiniteDimensional K M']

theorem integralOver_embed (O : ValuationSubring K) [Algebra O M'] [IsScalarTower O K M']
    (ι : M' →ₐ[K] Ω) (b : integralClosure O M') : IntegralOver O (ι (b : M')) := by
  let _ : Algebra O Ω := ((algebraMap K Ω).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h : IsIntegral O (b : M') := (mem_integralClosure_iff O M').mp b.2
  exact h.map (ι.restrictScalars O)

/-- The center of `w` on the integral closure of `O` in `M'`, through the embedding `ι`. -/
def integralCenter (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) [Algebra O M'] [IsScalarTower O K M']
    (ι : M' →ₐ[K] Ω) : Ideal (integralClosure O M') :=
  (maximalIdeal w).comap
    (((ι : M' →+* Ω).comp (algebraMap (integralClosure O M') M')).codRestrict w.toSubring
      (fun b => mem_of_integralOver O w hw (integralOver_embed O ι b)))

theorem mem_integralCenter_iff (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) [Algebra O M'] [IsScalarTower O K M']
    (ι : M' →ₐ[K] Ω) (b : integralClosure O M') :
    b ∈ integralCenter O w hw ι ↔ w.valuation (ι (b : M')) < 1 := by
  unfold integralCenter
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

instance (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) [Algebra O M'] [IsScalarTower O K M']
    (ι : M' →ₐ[K] Ω) : (integralCenter O w hw ι).IsPrime := by
  unfold integralCenter
  exact Ideal.comap_isPrime _ _

theorem embed_algebraMap (O : ValuationSubring K) [Algebra O M'] [IsScalarTower O K M']
    (ι : M' →ₐ[K] Ω) (a : O) : ι (algebraMap O M' a) = algebraMap K Ω (a : K) := by
  rw [IsScalarTower.algebraMap_apply O K M', AlgHom.commutes]
  rfl

theorem under_integralCenter (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) [Algebra O M'] [IsScalarTower O K M']
    (ι : M' →ₐ[K] Ω) : (integralCenter O w hw ι).under O = maximalIdeal O := by
  ext a
  rw [Ideal.mem_comap, mem_integralCenter_iff, mem_maximalIdeal_iff_val O w hw]
  change w.valuation (ι (algebraMap O M' a)) < 1 ↔ _
  rw [embed_algebraMap]

/-- **Ramification index one at the center.** -/
theorem ramificationIdx_integralCenter_eq_one (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) [Algebra O M']
    [IsScalarTower O K M'] (ι : M' →ₐ[K] Ω)
    (hfix : ∀ m : M', ∀ σ : Ω ≃ₐ[K] Ω, (∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) → σ (ι m) = ι m) :
    (integralCenter O w hw ι).ramificationIdx O = 1 := by
  classical
  let B := integralClosure O M'
  have hsep : Algebra.IsSeparable K M' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfrB : IsFractionRing B M' := integralClosure.isFractionRing_of_finite_extension (A := O) K M'
  have hdB : IsDedekindDomain B := integralClosure.isDedekindDomain O K M'
  let W : ValuationSubring M' := w.comap (ι : M' →+* Ω)
  have hB : ∀ b : B, algebraMap B M' b ∈ W := fun b =>
    ValuationSubring.mem_comap.mpr (mem_of_integralOver O w hw (integralOver_embed O ι b))
  have hcen : center W hB = integralCenter O w hw ι := by
    ext b
    rw [mem_center_iff, comap_valuation_lt_one_iff, mem_integralCenter_iff]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖspan : (center W hB).under O = Ideal.span {ϖ} := by
    rw [hcen, under_integralCenter, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  have hϖK : (ϖ : K) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hιϖ : ι (algebraMap B M' (algebraMap O B ϖ)) = algebraMap K Ω (ϖ : K) := by
    change ι (algebraMap O M' ϖ) = _
    rw [embed_algebraMap]
  have hϖ0 : algebraMap B M' (algebraMap O B ϖ) ≠ 0 := by
    intro h0
    have := hιϖ
    rw [h0, map_zero] at this
    exact hϖK ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 this.symm)
  -- the image field and the valuation statement
  let Mι : IntermediateField K Ω := ι.fieldRange
  have : FiniteDimensional K Mι :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField ι).toLinearEquiv
  have hMι : ∀ m ∈ Mι, ∀ σ : Ω ≃ₐ[K] Ω, (∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) → σ m = m := by
    rintro m ⟨m', rfl⟩ σ hσ
    exact hfix m' σ hσ
  have hdiv : ∀ x : M', W.valuation x < 1 →
      x * (algebraMap B M' (algebraMap O B ϖ))⁻¹ ∈ W := by
    intro x hx
    rw [comap_valuation_lt_one_iff] at hx
    have h := div_uniformizer_mem_of_inertia_fixed O w hw Mι hMι ϖ hϖ (ι x) ⟨x, rfl⟩ hx
    apply ValuationSubring.mem_comap.mpr
    change ι (x * (algebraMap B M' (algebraMap O B ϖ))⁻¹) ∈ w
    rw [map_mul, map_inv₀, hιϖ]
    exact h
  have he := ramificationIdx_eq_one_of_div_mem W hB ϖ hϖspan hϖ0 hdiv
  rw [hcen] at he
  exact he

/-- **`Algebra.IsUnramifiedAt` at the center.** -/
theorem isUnramifiedAt_integralCenter (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) [Algebra O M']
    [IsScalarTower O K M'] (ι : M' →ₐ[K] Ω)
    (hfix : ∀ m : M', ∀ σ : Ω ≃ₐ[K] Ω, (∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) → σ (ι m) = ι m) :
    Algebra.IsUnramifiedAt O (integralCenter O w hw ι) := by
  classical
  have hsep : Algebra.IsSeparable K M' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfin : Module.Finite O (integralClosure O M') :=
    IsIntegralClosure.finite O K M' (integralClosure O M')
  have hess : Algebra.EssFiniteType O (integralClosure O M') := inferInstance
  have hu := under_integralCenter O w hw ι
  have hmax : ((integralCenter O w hw ι).under O).IsMaximal := hu ▸ inferInstance
  have hfinq : Finite (O ⧸ (integralCenter O w hw ι).under O) := hu ▸ finite_residueField K O
  have hfinRes : Finite ((integralCenter O w hw ι).under O).ResidueField :=
    Finite.of_surjective _
      (Ideal.bijective_algebraMap_quotient_residueField ((integralCenter O w hw ι).under O)).2
  have : Fintype ((integralCenter O w hw ι).under O).ResidueField := Fintype.ofFinite _
  have hsepRes : Algebra.HasSeparableResidueFieldsAt O (integralClosure O M')
      ((integralCenter O w hw ι).under O) := inferInstance
  exact (Ideal.ramificationIdx_eq_one_iff).1 (ramificationIdx_integralCenter_eq_one O w hw ι hfix)

end InertiaPointDescent
