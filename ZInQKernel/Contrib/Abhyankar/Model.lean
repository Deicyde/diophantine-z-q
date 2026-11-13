import ZInQKernel.Contrib.Abhyankar.Field
import ZInQKernel.Contrib.Abhyankar.Etale
import ZInQKernel.Contrib.Abhyankar.ReducedLocal
import ZInQKernel.Contrib.Abhyankar.Fraction
import ZInQKernel.Contrib.Abhyankar.Local
import ZInQKernel.Contrib.Abhyankar.Transport
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The tame root model inside a field

The model is the actual subalgebra `B[y,t]` of a field, with
`y^e = u` and `t^d = ϖ y`. The unit-root step is etale; modulo `t`,
the model is a quotient of that etale step. The quotient is reduced over
the residue field, and at every maximal ideal `t` is a uniformizer.

This is the local computation of Stacks 0BRM and of Tau Ceti's
`DiscreteValuationRing/AbhyankarModel/Basic.lean` (revision
`30f41378f0cb1d569f51d8a4d0cb74aea8a80e44`). The proof here uses a
subalgebra of the specified field rather than assuming a field factor of
an adjoin-root ring. There is no completeness, henselianity, or residue
perfection hypothesis. The faithful field embedding is explicit.
-/

namespace ZInQ.Contrib.Abhyankar

open Polynomial IsLocalRing

/-- The tame root model as a subalgebra of the given ambient field. -/
abbrev tameRootModel (B : Type*) {M : Type*} [CommRing B] [CommRing M]
    [Algebra B M] (y t : M) : Subalgebra B M := Algebra.adjoin B {y, t}

/-- The unit-root generator in the actual subalgebra. -/
abbrev tameModelY (B : Type*) {M : Type*} [CommRing B] [CommRing M]
    [Algebra B M] (y t : M) : tameRootModel B y t :=
  ⟨y, Algebra.subset_adjoin (by simp)⟩

/-- The uniformizer-root generator in the actual subalgebra. -/
abbrev tameModelT (B : Type*) {M : Type*} [CommRing B] [CommRing M]
    [Algebra B M] (y t : M) : tameRootModel B y t :=
  ⟨t, Algebra.subset_adjoin (by simp)⟩

private theorem tameModel_adjoin_eq_top
    {B M : Type*} [CommRing B] [CommRing M] [Algebra B M] (y t : M) :
    Algebra.adjoin B {tameModelY B y t, tameModelT B y t} = ⊤ := by
  apply Subalgebra.map_injective (f := (tameRootModel B y t).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Set.image_pair, Algebra.map_top, Subalgebra.range_val]
  rfl

/-- The two integral generators make the model finite over the actual DVR base. -/
theorem finite_tameRootModel
    {B M : Type*} [CommRing B] [CommRing M] [Algebra B M]
    {ϖ u : B} {e d : ℕ} (he : 0 < e) (hd : 0 < d) {y t : M}
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y) :
    Module.Finite B (tameRootModel B y t) := by
  have hiy : IsIntegral B y := isIntegral_root he hy
  have hit : IsIntegral B t := by
    apply IsIntegral.of_pow hd
    rw [ht]
    exact isIntegral_algebraMap.mul hiy
  exact Algebra.finite_adjoin_of_finite_of_isIntegral ((Set.finite_singleton t).insert y)
    (by rintro z (rfl | rfl); exact hiy; exact hit)

/-- The generator `y` is a unit in the integral model, not just in its fraction field. -/
theorem isUnit_tameModelY
    {B M : Type*} [CommRing B] [CommRing M] [Algebra B M]
    {u : B} (hu : IsUnit u) {e : ℕ} (he : 0 < e) {y t : M}
    (hy : y ^ e = algebraMap B M u) : IsUnit (tameModelY B y t) := by
  have hyp : (tameModelY B y t) ^ e = algebraMap B (tameRootModel B y t) u := Subtype.ext hy
  apply isUnit_of_dvd_unit (dvd_pow_self _ he.ne')
  rw [hyp]
  exact hu.map (algebraMap B (tameRootModel B y t))

/-- Modulo the root `t`, the model is formally unramified over `B`:
it is an actual quotient of the etale unit-root algebra. -/
theorem formallyUnramified_tameModel_mod_root
    {B M : Type*} [CommRing B] [CommRing M] [Algebra B M]
    {u : B} (hu : IsUnit u) {e : ℕ} (he : 0 < e) (heunit : IsUnit (e : B))
    {y t : M} (hy : y ^ e = algebraMap B M u) :
    Algebra.FormallyUnramified B
      (tameRootModel B y t ⧸ Ideal.span {tameModelT B y t}) := by
  let D := tameRootModel B y t
  let I : Ideal D := Ideal.span {tameModelT B y t}
  let W := D ⧸ I
  have hyD : (tameModelY B y t) ^ e = algebraMap B D u := Subtype.ext hy
  have hroot : (X ^ e - C u).eval₂ (algebraMap B W)
      (Ideal.Quotient.mk I (tameModelY B y t)) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, ← map_pow, hyD,
      ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply B D W, sub_self]
  let f : AdjoinRoot (X ^ e - C u) →ₐ[B] W :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId B W) (Ideal.Quotient.mk I (tameModelY B y t)) hroot
  have hle : Algebra.adjoin B {tameModelY B y t, tameModelT B y t} ≤
      f.range.comap (Ideal.Quotient.mkₐ B I) := by
    apply Algebra.adjoin_le
    rintro z (rfl | rfl)
    · exact ⟨AdjoinRoot.root _, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
    · refine ⟨0, ?_⟩
      simp only [map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)).symm
  rw [tameModel_adjoin_eq_top] at hle
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hle Algebra.mem_top
  have : Algebra.Etale B (AdjoinRoot (X ^ e - C u)) := etale_unitRoot hu he heunit
  exact Algebra.FormallyUnramified.of_surjective f hf

section DVR

variable {B M : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Field M] [Algebra B M] {ϖ u : B} {e d : ℕ} {y t : M}

/-- The mapped base maximal ideal is the `d`-th power of the ideal generated by `t`. -/
theorem tameModel_map_maximalIdeal
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e)
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y) :
    (maximalIdeal B).map (algebraMap B (tameRootModel B y t)) =
      Ideal.span {tameModelT B y t} ^ d := by
  have htD : (tameModelT B y t) ^ d =
      algebraMap B (tameRootModel B y t) ϖ * tameModelY B y t := Subtype.ext ht
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  calc
    Ideal.span {algebraMap B (tameRootModel B y t) ϖ} =
        Ideal.span {algebraMap B (tameRootModel B y t) ϖ * tameModelY B y t} :=
      (Ideal.span_singleton_mul_right_unit (isUnit_tameModelY hu he hy) _).symm
    _ = Ideal.span {(tameModelT B y t) ^ d} := by rw [htD]
    _ = Ideal.span {tameModelT B y t} ^ d := (Ideal.span_singleton_pow _ _).symm

/-- Every prime containing `t` is maximal, and every maximal prime contains `t`. -/
theorem tameModel_isMaximal_iff_root_mem
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (P : Ideal (tameRootModel B y t)) [P.IsPrime] :
    P.IsMaximal ↔ tameModelT B y t ∈ P := by
  have : Module.Finite B (tameRootModel B y t) := finite_tameRootModel he hd hy ht
  have htD : (tameModelT B y t) ^ d =
      algebraMap B (tameRootModel B y t) ϖ * tameModelY B y t := Subtype.ext ht
  have hyunit := isUnit_tameModelY (t := t) hu he hy
  constructor
  · intro hP
    have : P.IsMaximal := hP
    have hunder : P.under B = maximalIdeal B := eq_maximalIdeal (Ideal.IsMaximal.under B P)
    have hϖP : algebraMap B (tameRootModel B y t) ϖ ∈ P := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, hunder, hϖ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self _
    apply Ideal.IsPrime.mem_of_pow_mem inferInstance d
    rw [htD]
    exact P.mul_mem_right _ hϖP
  · intro hx
    have hϖP : algebraMap B (tameRootModel B y t) ϖ ∈ P := by
      have hprod := P.pow_mem_of_mem hx d hd
      rw [htD] at hprod
      exact (Ideal.IsPrime.mem_or_mem inferInstance hprod).resolve_right
        (fun hyP ↦ (Ideal.IsPrime.ne_top inferInstance) (P.eq_top_of_isUnit_mem hyP hyunit))
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) P
    have hle : maximalIdeal B ≤ P.under B := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
      exact hϖP
    have heq := (maximalIdeal.isMaximal B).eq_of_le (Ideal.IsPrime.under B P).ne_top hle
    rw [← heq]
    infer_instance

/-- Every maximal ideal is minimal over the reduced root divisor. -/
theorem tameModel_mem_minimalPrimes
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (P : Ideal (tameRootModel B y t)) [P.IsMaximal] :
    P ∈ (Ideal.span {tameModelT B y t}).minimalPrimes := by
  have hx := (tameModel_isMaximal_iff_root_mem hϖ hu he hd hy ht P).mp inferInstance
  refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem P).mpr hx⟩, ?_⟩
  rintro Q ⟨hQprime, hQroot⟩ hQP
  have := (tameModel_isMaximal_iff_root_mem hϖ hu he hd hy ht Q).mpr
    ((Ideal.span_singleton_le_iff_mem Q).mp hQroot)
  exact (this.eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hQP).ge

/-- The root quotient is reduced, using its actual residue-field algebra.
No perfect-field hypothesis is needed for the etale unit-root quotient. -/
theorem isReduced_tameModel_mod_root
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y) :
    IsReduced (tameRootModel B y t ⧸ Ideal.span {tameModelT B y t}) := by
  let D := tameRootModel B y t
  let I : Ideal D := Ideal.span {tameModelT B y t}
  let W := D ⧸ I
  have hle : (maximalIdeal B).map (algebraMap B D) ≤ I := by
    rw [tameModel_map_maximalIdeal hϖ hu he hy ht]
    exact Ideal.pow_le_self hd.ne'
  let ρ : (B ⧸ maximalIdeal B) →+* W := Ideal.Quotient.lift (maximalIdeal B)
    (algebraMap B W) (by
      intro b hb
      rw [IsScalarTower.algebraMap_apply B D W, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hle (Ideal.mem_map_of_mem _ hb))
  let : Algebra (B ⧸ maximalIdeal B) W := ρ.toAlgebra
  have : IsScalarTower B (B ⧸ maximalIdeal B) W := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    change algebraMap B W b = ρ (Ideal.Quotient.mk (maximalIdeal B) b)
    rw [Ideal.Quotient.lift_mk]
  let := Ideal.Quotient.field (maximalIdeal B)
  have : Algebra.FormallyUnramified B W := formallyUnramified_tameModel_mod_root hu he heunit hy
  have : Algebra.FormallyUnramified (B ⧸ maximalIdeal B) W :=
    Algebra.FormallyUnramified.of_restrictScalars B _ _
  have : Module.Finite B D := finite_tameRootModel he hd hy ht
  have : Algebra.FiniteType (B ⧸ maximalIdeal B) W :=
    Algebra.FiniteType.of_restrictScalars_finiteType B _ _
  exact Algebra.FormallyUnramified.isReduced_of_field (B ⧸ maximalIdeal B) W

/-- Every maximal localization of the model is a DVR with root uniformizer. -/
theorem tameModel_local_dvr
    [FaithfulSMul B M]
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (P : Ideal (tameRootModel B y t)) [P.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  have : Module.Finite B (tameRootModel B y t) := finite_tameRootModel he hd hy ht
  have : IsNoetherianRing (tameRootModel B y t) := IsNoetherianRing.of_finite B _
  have : IsReduced (tameRootModel B y t ⧸ Ideal.span {tameModelT B y t}) :=
    isReduced_tameModel_mod_root hϖ hu he hd heunit hy ht
  have hyunit : IsUnit y := isUnit_of_dvd_unit (dvd_pow_self y he.ne')
    (by rw [hy]; exact hu.map (algebraMap B M))
  have hϖ0 : algebraMap B M ϖ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B M)).mpr hϖ.ne_zero
  have ht0 : t ≠ 0 := by
    intro hz
    exact (mul_ne_zero hϖ0 hyunit.ne_zero) (by simpa [hz, zero_pow hd.ne'] using ht.symm)
  have hx0 : tameModelT B y t ≠ 0 := fun h ↦ ht0 (congrArg Subtype.val h)
  exact local_dvr_of_reduced_principal hx0 (tameModel_mem_minimalPrimes hϖ hu he hd hy ht P)

/-- Every maximal localization has the root as a generator of its maximal ideal. -/
theorem tameModel_local_maximalIdeal
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (P : Ideal (tameRootModel B y t)) [P.IsMaximal] :
    maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap (tameRootModel B y t) (Localization.AtPrime P) (tameModelT B y t)} := by
  have : IsReduced (tameRootModel B y t ⧸ Ideal.span {tameModelT B y t}) :=
    isReduced_tameModel_mod_root hϖ hu he hd heunit hy ht
  exact local_maximalIdeal_eq_span (tameModel_mem_minimalPrimes hϖ hu he hd hy ht P)

/-- Residue separability at every maximal model prime above the original closed point. -/
theorem tameModel_residue_separable
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (P : Ideal (tameRootModel B y t)) [P.IsMaximal] [P.LiesOver (maximalIdeal B)] :
    Algebra.IsSeparable (B ⧸ maximalIdeal B) (tameRootModel B y t ⧸ P) := by
  have hx := (tameModel_isMaximal_iff_root_mem hϖ hu he hd hy ht P).mp inferInstance
  have hle := (Ideal.span_singleton_le_iff_mem P).mpr hx
  have : Algebra.FormallyUnramified B
      (tameRootModel B y t ⧸ Ideal.span {tameModelT B y t}) :=
    formallyUnramified_tameModel_mod_root hu he heunit hy
  have : Algebra.FormallyUnramified B (tameRootModel B y t ⧸ P) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.factorₐ B hle)
      (Ideal.Quotient.factor_surjective hle)
  have : Algebra.FormallyUnramified (B ⧸ maximalIdeal B) (tameRootModel B y t ⧸ P) :=
    Algebra.FormallyUnramified.of_restrictScalars B _ _
  have : Module.Finite B (tameRootModel B y t) := finite_tameRootModel he hd hy ht
  have : Module.Finite (B ⧸ maximalIdeal B) (tameRootModel B y t ⧸ P) := inferInstance
  let := Ideal.Quotient.field (maximalIdeal B)
  let := Ideal.Quotient.field P
  exact Algebra.FormallyUnramified.isSeparable _ _

/-- The actual ramification index of a maximal model prime over `B` is `d`. -/
theorem tameModel_ramificationIdx
    [FaithfulSMul B M]
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (P : Ideal (tameRootModel B y t)) [P.IsMaximal] [P.LiesOver (maximalIdeal B)] :
    P.ramificationIdx B = d := by
  have : IsDiscreteValuationRing (Localization.AtPrime P) :=
    tameModel_local_dvr hϖ hu he hd heunit hy ht P
  have hmax := tameModel_local_maximalIdeal hϖ hu he hd heunit hy ht P
  apply ramificationIdx_eq_of_local_map_eq_pow (maximalIdeal B) P
  rw [IsScalarTower.algebraMap_eq B (tameRootModel B y t) (Localization.AtPrime P),
    ← Ideal.map_map, tameModel_map_maximalIdeal hϖ hu he hy ht, Ideal.map_pow,
    Ideal.map_span, Set.image_singleton, ← hmax]

/-- Normality of the actual subalgebra follows from its DVR localizations at
all maximal ideals. No field-factor normality is assumed. -/
theorem isIntegrallyClosed_tameRootModel
    [FaithfulSMul B M]
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y) :
    IsIntegrallyClosed (tameRootModel B y t) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P hP0 hPmax
  have : IsDiscreteValuationRing (Localization.AtPrime P) :=
    tameModel_local_dvr hϖ hu he hd heunit hy ht P
  infer_instance

/-- **Field-factor normalization.** If `t` generates the given field over
`Frac(B)`, the actual integral closure in that field is the subalgebra `B[y,t]`.
The fraction-field and normality bridges are proved, not added as premises. -/
theorem integralClosure_eq_tameRootModel
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra L M] [IsScalarTower B L M]
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (hgen : IntermediateField.adjoin L {t} = ⊤) :
    integralClosure B M = tameRootModel B y t := by
  have : FaithfulSMul B M := FaithfulSMul.trans B L M
  let D := tameRootModel B y t
  have : Module.Finite B D := finite_tameRootModel he hd hy ht
  have : IsIntegrallyClosed D := isIntegrallyClosed_tameRootModel hϖ hu he hd heunit hy ht
  have hpair : IntermediateField.adjoin L {y, t} = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact IntermediateField.adjoin.mono L _ _ (by simp)
  have : IsFractionRing D M := isFractionRing_adjoin_of_adjoin_eq_top hpair
  have : IsIntegralClosure D B M := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  refine le_antisymm (fun z hz ↦ ?_) ?_
  · obtain ⟨a, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := D)).mp hz
    exact a.2
  · exact le_integralClosure_iff_isIntegral.mpr inferInstance

/-- **All-prime tame model conclusion in the specified field.** Every prime of
its actual integral closure over the maximal ideal has index `d` and separable
residue field. This is a proved local-model result, with explicit root data. -/
theorem tameRootModel_at_every_prime
    {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra L M] [IsScalarTower B L M]
    (hϖ : Irreducible ϖ) (hu : IsUnit u) (he : 0 < e) (hd : 0 < d)
    (heunit : IsUnit (e : B))
    (hy : y ^ e = algebraMap B M u) (ht : t ^ d = algebraMap B M ϖ * y)
    (hgen : IntermediateField.adjoin L {t} = ⊤)
    (Q : Ideal (integralClosure B M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal B)] :
    Q.ramificationIdx B = d ∧
      Algebra.IsSeparable (B ⧸ maximalIdeal B) (integralClosure B M ⧸ Q) := by
  have : FaithfulSMul B M := FaithfulSMul.trans B L M
  let D := tameRootModel B y t
  have : Module.Finite B D := finite_tameRootModel he hd hy ht
  let σ : D ≃ₐ[B] integralClosure B M := Subalgebra.equivOfEq _ _
    (integralClosure_eq_tameRootModel hϖ hu he hd heunit hy ht hgen).symm
  refine allPrimeData_of_algEquiv (maximalIdeal B) σ ?_ Q
  intro P hPprime hPover
  have : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) P
    rw [← P.over_def (maximalIdeal B)]
    infer_instance
  exact ⟨tameModel_ramificationIdx hϖ hu he hd heunit hy ht P,
    tameModel_residue_separable hϖ hu he hd heunit hy ht P⟩

end DVR

end ZInQ.Contrib.Abhyankar
