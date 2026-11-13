import ZInQKernel.Contrib.Abhyankar.Builder
import ZInQKernel.Contrib.Abhyankar.Primes
import ZInQKernel.Contrib.Abhyankar.LocalField
import ZInQKernel.Contrib.Abhyankar.Frame
import ZInQKernel.Contrib.Abhyankar.Comparison
import ZInQKernel.HDecomp.Objects
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Assembly of the exact tame DVR conclusion

The local normalized conclusion below uses the actual prime index and constructs
the uniformizer/root model. The base-localization fraction field and scalar
towers are proved, and residue separability is composed through actual residue
algebra maps. No completeness or perfect-residue hypothesis is introduced.
-/

namespace ZInQ.Contrib.Abhyankar

open IsLocalRing

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- At a specified original integral-closure prime, the constructed normalized
model has the exact index over `R` and a separable residue extension. -/
theorem normalized_at_prime
    {R K L M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra R M] [IsScalarTower R L M]
    (q : Ideal (integralClosure R L)) [q.IsPrime] [q.LiesOver (maximalIdeal R)]
    [Algebra (Localization.AtPrime q) L]
    [IsScalarTower (integralClosure R L) (Localization.AtPrime q) L]
    [Algebra (Localization.AtPrime q) M]
    [IsScalarTower (integralClosure R L) (Localization.AtPrime q) M]
    {π : R} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (htame : IsUnit ((q.ramificationIdx R : ℕ) : R) ∧ q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ q))
    {t : M} (ht : t ^ n = algebraMap R M π)
    (hgen : IntermediateField.adjoin L {t} = ⊤)
    (P : @Ideal (integralClosure (Localization.AtPrime q) M)
      (inferInstance : CommRing (integralClosure (Localization.AtPrime q) M)).toSemiring)
    [P.IsPrime]
    [P.LiesOver (maximalIdeal (Localization.AtPrime q))] [P.LiesOver (maximalIdeal R)] :
    P.ramificationIdx R = n ∧ Algebra.IsSeparable (R ⧸ maximalIdeal R)
      (integralClosure (Localization.AtPrime q) M ⧸ P) := by
  let S := integralClosure R L
  let B := Localization.AtPrime q
  let U := integralClosure B M
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : IsDedekindDomain S := integralClosure.isDedekindDomain R K L
  have : IsDiscreteValuationRing B := integralClosure_local_dvr R K L q
  have : IsDedekindDomain B := IsLocalization.AtPrime.isDedekindDomain S q B
  have : IsFractionRing B L := localization_isFractionRing S L q
  have : IsScalarTower B L M := localization_field_scalarTower S L M q
  have : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr (IsFractionRing.injective B L)
  have : FaithfulSMul B M := FaithfulSMul.trans B L M
  have hπq : algebraMap R B π ≠ 0 := by
    simpa only [map_zero] using (integralClosure_local_algebraMap_injective R K L q).ne hπ.ne_zero
  obtain ⟨ϖ, u, d, y, hϖ, he, hd, hnd, heunit, hy, hty⟩ :=
    exists_tameModel_data q hπ hπq hn htame.1 htame.2.1 ht
  obtain ⟨hidxB, hsepB⟩ := tameRootModel_at_every_prime
    hϖ u.isUnit he hd heunit hy hty hgen P
  have : Module.IsTorsionFree B M := Module.IsTorsionFree.of_smul_eq_zero fun b m hm ↦ by
    simpa only [Algebra.smul_def, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] using hm
  have htf : Module.IsTorsionFree B U := inferInstance
  have : Module.Flat B U :=
    (IsDedekindDomain.flat_iff_torsion_eq_bot (R := B) (M := U)).mpr
      ((Submodule.isTorsionFree_iff_torsion_eq_bot (R := B) (M := U)).mp htf)
  have hidxR : P.ramificationIdx R = n := by
    rw [Ideal.ramificationIdx_tower (q := maximalIdeal B),
      ramificationIdx_localization_atPrime (R := R) q, hidxB, ← hnd]
  have : q.IsMaximal := integralClosure_prime_isMaximal q
  have : (maximalIdeal B).LiesOver (maximalIdeal R) :=
    Ideal.LiesOver.trans (maximalIdeal B) q (maximalIdeal R)
  have : P.LiesOver (maximalIdeal R) :=
    Ideal.LiesOver.trans P (maximalIdeal B) (maximalIdeal R)
  let σ : (S ⧸ q) ≃ₐ[R] B ⧸ maximalIdeal B := quotient_equiv_local_residue q
  let τ : (S ⧸ q) ≃ₐ[R ⧸ maximalIdeal R] B ⧸ maximalIdeal B :=
    σ.extendScalarsOfSurjective (R := R) (S := R ⧸ maximalIdeal R) Ideal.Quotient.mk_surjective
  have : Algebra.IsSeparable (R ⧸ maximalIdeal R) (B ⧸ maximalIdeal B) :=
    (AlgEquiv.Algebra.isSeparable_iff τ).mp htame.2.2
  have : Algebra.IsSeparable (B ⧸ maximalIdeal B) (U ⧸ P) := hsepB
  have : P.IsMaximal := integralClosure_prime_isMaximal P
  let := Ideal.Quotient.field (maximalIdeal R)
  let := Ideal.Quotient.field (maximalIdeal B)
  let := Ideal.Quotient.field P
  let hBP : Algebra (B ⧸ maximalIdeal B) (U ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver (A := B) (B := U) P (maximalIdeal B)
  let _ : Algebra (B ⧸ maximalIdeal B) (U ⧸ P) := hBP
  let _ : SMul (B ⧸ maximalIdeal B) (U ⧸ P) := hBP.toSMul
  have : IsScalarTower (R ⧸ maximalIdeal R) (B ⧸ maximalIdeal B) (U ⧸ P) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver,
      Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.algebraMap_mk_of_liesOver,
      ← IsScalarTower.algebraMap_apply R B U]
  exact ⟨hidxR, Algebra.IsSeparable.trans (R ⧸ maximalIdeal R) (B ⧸ maximalIdeal B) (U ⧸ P)⟩

open scoped ZInQ.Contrib.Abhyankar.ClosureTower

/-- **Closed exact general tame DVR form.** This has the unchanged baseline
proposition as its whole type; all intermediate maps, localizations, model
hypotheses, and prime-family comparisons are constructed in the proof. -/
theorem abhyankarDVR : PkgI2.AbhyankarDVR.{0} := by
  intro R K L M instR domR dvrR instK algRK fracRK instL algKL algRL towerRKL
    finKL sepKL instM algLM algKM algRM towerKLM towerRKM π hπ n hn hunit htame
    t ht hgen Q hQprime hQover
  have : IsScalarTower R L M := scalarTower_right (K := K)
  let S := integralClosure R L
  let C := integralClosure S M
  let σ : C ≃ₐ[R] integralClosure R M := ClosureTower.equivBase R L M
  refine allPrimeData_of_algEquiv (maximalIdeal R) σ ?_ Q
  intro Q0 hQ0prime hQ0over
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : FaithfulSMul S L :=
    (faithfulSMul_iff_algebraMap_injective S L).mpr (IsFractionRing.injective S L)
  have : FaithfulSMul S M :=
    (faithfulSMul_iff_algebraMap_injective S M).mpr
      ((algebraMap L M).injective.comp Subtype.val_injective)
  have : IsScalarTower R S M := inferInstance
  have : Algebra.IsIntegral R C := (σ.isIntegral_iff).mpr inferInstance
  have : Q0.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) Q0
    rw [← Q0.over_def (maximalIdeal R)]
    infer_instance
  let q : Ideal S := Q0.under S
  have : q.IsPrime := Ideal.IsPrime.under S Q0
  have : Q0.LiesOver q := ⟨rfl⟩
  have : q.LiesOver (maximalIdeal R) :=
    Ideal.LiesOver.tower_bot Q0 q (maximalIdeal R)
  let B := Localization.AtPrime q
  let _ : Algebra B L := normalizationAtPrimeFieldAlgebra S L q
  let _ : IsScalarTower S B L := normalizationAtPrimeFieldTower S L q
  let _ : Algebra B M := normalizationAtPrimeFieldAlgebra S M q
  let _ : IsScalarTower S B M := normalizationAtPrimeFieldTower S M q
  let U := integralClosure B M
  let hCU : Algebra C U := normalizationAlgebra S B M
  let _ : Algebra C U := hCU
  let _ : SMul C U := hCU.toSMul
  have : IsScalarTower S C U := normalization_sourceTower S B M
  have : IsScalarTower C U M := normalization_ambientTower S B M
  let P : Ideal U := normalizationPrime S M q Q0
  have : P.IsPrime := normalizationPrime_isPrime S M q Q0
  have : P.LiesOver Q0 := normalizationPrime_liesOver S M q Q0
  have : P.LiesOver (maximalIdeal B) := normalizationPrime_liesOver_maximalIdeal S M q Q0
  have : IsScalarTower R S U := IsScalarTower.to₁₂₄ R S B U
  have : IsScalarTower R C U := IsScalarTower.to₁₃₄ R S C U
  have : P.LiesOver (maximalIdeal R) := Ideal.LiesOver.trans P Q0 (maximalIdeal R)
  have : P.IsMaximal := integralClosure_prime_isMaximal P
  obtain ⟨hidx, hsep⟩ := normalized_at_prime (K := K) q hπ hn (htame q) ht hgen P
  refine ⟨?_, ?_⟩
  · exact (normalization_ramificationIdx R S M q Q0).trans hidx
  · exact (normalization_residueSeparable_iff R S M q Q0 (maximalIdeal R)).mpr hsep

end ZInQ.Contrib.Abhyankar
