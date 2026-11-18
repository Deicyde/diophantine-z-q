import ZInQKernel.Contrib.OneProof.RC.TraceLimits.InertiaLift
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Quadratic
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The inertia of a squarefree radical

Tex 9748–9750, on-the-spot (c). First compare the absolute and finite inertia
groups, then use the ramification index forced by the square root of a
squarefree integer.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.PrintsArith
open scoped NumberField

/-- The inclusion of the integers of a subfield into the absolute integral closure. -/
private def integerInclusion (E : IntermediateField ℚ Qbar) : 𝓞 E →+* Zbar :=
  NumberField.RingOfIntegers.mapRingHom E.val.toRingHom

/-- The absolute inertia over a prime surjects onto the inertia in every
finite Galois subextension. -/
theorem absolute_inertia_maps (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (Q : Ideal Zbar) [Q.IsPrime] :
    (Q.inertia GalQ).map (AlgEquiv.restrictNormalHom E) =
      (Q.comap (integerInclusion E)).inertia (E ≃ₐ[ℚ] E) := by
  let R := NumberField.RingOfIntegers E
  letI : Algebra R Zbar := (integerInclusion E).toAlgebra
  let P := Q.under R
  have : Q.LiesOver P := ⟨rfl⟩
  have : CompactSpace E.fixingSubgroup :=
    isCompact_iff_compactSpace.mp E.fixingSubgroup_isClosed.isCompact
  let _ : TopologicalSpace Zbar := ⊥
  have : DiscreteTopology Zbar := ⟨rfl⟩
  have : ContinuousSMul GalQ Zbar := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) (x : Qbar) using 1
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have : Algebra.IsInvariant R Zbar E.fixingSubgroup := by
    constructor
    intro b hb
    have hfix : (b : Qbar) ∈ E := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup E]
      exact fun σ => congrArg Subtype.val (hb σ)
    let y : E := ⟨b, hfix⟩
    have hy : IsIntegral ℤ y :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Qbar)
        (algebraMap E Qbar).injective).mp b.2
    exact ⟨⟨y, hy⟩, rfl⟩
  exact map_inertia_of_profinite (AlgEquiv.restrictNormalHom E) E.fixingSubgroup P Q
    (fun τ => ⟨τ.liftNormal Qbar, τ.restrict_liftNormal Qbar⟩) (le_of_eq E.restrictNormalHom_ker.symm) fun g x => by
      apply Subtype.ext
      exact AlgEquiv.restrictNormal_commutes g E (x : E)

/-- An odd prime dividing a squarefree radicand admits an absolute inertia
element acting nontrivially on the radical (tex 9748–9750). -/
theorem oddRadicalRamification : OddRadicalRamification := by
  intro d hd s hs q hq _ hqd
  let E := IntermediateField.adjoin ℚ {s}
  have : FiniteDimensional ℚ E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have hsE : s ∈ E := IntermediateField.mem_adjoin_simple_self ℚ _
  have hfix (σ : GalQ) : σ ∈ E.fixingSubgroup ↔ σ s = s := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    refine ⟨fun h => h s hsE, fun h x hx => ?_⟩
    have e : E.toSubalgebra = Algebra.adjoin ℚ {s} :=
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsIntegral.isIntegral s).isAlgebraic
    have hx' : x ∈ Algebra.adjoin ℚ {s} := e ▸ hx
    exact (AlgHom.eqOn_adjoin_iff (φ := σ.toAlgHom) (ψ := AlgHom.id ℚ Qbar)).2
      (Set.eqOn_singleton.2 h) hx'
  have hker : E.fixingSubgroup = (sqrtChar d).ker := by
    ext σ
    rw [hfix, MonoidHom.mem_ker, sqrtChar_eq_one_iff d hd.ne_zero]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((sqrtQbar_sq d).trans hs.symm) with e | e
    · rw [e]
    · rw [e, map_neg, neg_inj]
  have : E.fixingSubgroup.Normal := hker ▸ (sqrtChar d).normal_ker
  have : IsGalois ℚ E := (InfiniteGalois.normal_iff_isGalois E).1 inferInstance
  have : NumberField E := ⟨⟩
  obtain ⟨Q, hQ, hqQ⟩ := exists_isMaximal_of_prime hq
  have := hQ.isPrime
  refine ⟨Q, hQ, hqQ, ?_⟩
  let P := Q.comap (integerInclusion E)
  have : P.IsPrime := hQ.isPrime.comap _
  have hqP : (q : 𝓞 E) ∈ P := by
    change (integerInclusion E) (q : 𝓞 E) ∈ Q
    rw [map_natCast]
    simpa only [Int.cast_natCast] using hqQ
  have hP0 : P ≠ ⊥ := fun h => hq.ne_zero (by
    simpa only [h, Ideal.mem_bot, Nat.cast_eq_zero] using hqP)
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  have : Fact q.Prime := ⟨hq⟩
  have hp : P.LiesOver p := ⟨(Int.ideal_span_isMaximal_of_prime q).eq_of_le
    (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under, eq_intCast, Int.cast_natCast]
      exact hqP)⟩
  let sE : E := ⟨s, hsE⟩
  have hsint : IsIntegral ℤ s := IsIntegral.of_pow (n := 2) (by decide) (hs ▸ isIntegral_intCast d)
  let x : 𝓞 E := ⟨sE, (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E Qbar)
     (algebraMap E Qbar).injective).mp hsint⟩
  have hx : x ^ 2 = (d : 𝓞 E) := Subtype.ext (Subtype.ext hs)
  have he := ramificationIdx_two_le_of_square hq hd hqd P inferInstance hP0 x hx
  have hp0 : p ≠ ⊥ := by
    change Ideal.span {(q : ℤ)} ≠ ⊥
    simpa using hq.ne_zero
  have hcard := Ideal.card_inertia_eq_ramificationIdx ℤ (E ≃ₐ[ℚ] E) P
  have hn : Nontrivial (P.inertia (E ≃ₐ[ℚ] E)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by
      rw [hcard, ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
      exact he)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : P.inertia (E ≃ₐ[ℚ] E))
  have ht : (τ : E ≃ₐ[ℚ] E) ∈ (Q.inertia GalQ).map (AlgEquiv.restrictNormalHom E) := by
    rw [absolute_inertia_maps]
    exact τ.2
  obtain ⟨σ, hσ, e⟩ := ht
  refine ⟨σ, hσ, fun h => hτ (Subtype.ext ?_)⟩
  have hσ' : σ ∈ (AlgEquiv.restrictNormalHom E).ker := E.restrictNormalHom_ker ▸ (hfix σ).2 h
  exact e ▸ MonoidHom.mem_ker.1 hσ'

#print axioms absolute_inertia_maps
#print axioms oddRadicalRamification

end ZInQ.Manuscript.RC.TraceLimits
