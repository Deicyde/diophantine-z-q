import ZInQKernel.Contrib.Abhyankar.Normalization
import ZInQKernel.Contrib.Abhyankar.Transport

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

/-!
# Consumer comparisons for normalization localization

These comparisons use the actual normalization inclusion and the canonical local algebra
equivalence constructed in `Normalization.lean`. The equivalence is proved to carry the
actual maximal ideals to one another before it is used for ramification or residue transport.

Source provenance: original connecting arguments using Mathlib 4.35.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, and the proved project suppliers in `Transport.lean`.
That module retains the Tau Ceti attribution for its ramification transport helpers.
Maximal-ideal transport uses the proved inverse for unit reflection and
`IsLocalRing.maximalIdeal_comap` in `Mathlib/RingTheory/LocalRing/RingHom/Basic.lean`, followed
by the surjective map/comap identity. Unit reflection is supplied by
`isLocalHom_of_leftInverse` in `Mathlib/Algebra/Group/Units/Hom.lean`. Quotient transport uses
`Ideal.quotientEquivAlg` in `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`;
separability transport uses `AlgEquiv.Algebra.isSeparable_iff` in
`Mathlib/FieldTheory/Separable.lean`. No external proof is ported by this module.

This module supplies only consumer comparisons. It does not construct root data or the
iterated-integral-closure identification, and it makes no general T2 or acceptance claim.
-/

namespace ZInQ.Contrib.Abhyankar

/-- An actual algebra equivalence between local rings carries their maximal ideals to each other.
This is a proved map equality, not an assumed identification of the residue ideals. -/
theorem localAlgEquiv_map_maximalIdeal
    {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] [IsLocalRing A] [IsLocalRing B] (e : A ≃ₐ[R] B) :
    (IsLocalRing.maximalIdeal A).map e.toRingHom = IsLocalRing.maximalIdeal B := by
  have : IsLocalHom e.toRingHom :=
    isLocalHom_of_leftInverse (f := e.toRingHom) e.symm.toRingHom e.symm_apply_apply
  rw [← IsLocalRing.maximalIdeal_comap e.toRingHom]
  exact Ideal.map_comap_of_surjective e.toRingHom e.surjective (IsLocalRing.maximalIdeal B)

/-- The residue algebra equivalence induced by an actual algebra equivalence of local rings.
The required maximal-ideal equality is supplied by `localAlgEquiv_map_maximalIdeal`. -/
noncomputable def localAlgEquivResidue
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsLocalRing A] [IsLocalRing B] (e : A ≃ₐ[R] B) :
    (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[R] B ⧸ IsLocalRing.maximalIdeal B :=
  Ideal.quotientEquivAlg (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B) e
    (localAlgEquiv_map_maximalIdeal (R := R) (A := A) (B := B) e).symm

/-- The induced residue map is the quotient of the given local algebra map. -/
@[simp]
theorem localAlgEquivResidue_mk
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃ₐ[R] B) (x : A) :
    localAlgEquivResidue e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) (e x) := rfl

/-- The residue equivalence preserves the original coefficient ring. -/
@[simp]
theorem localAlgEquivResidue_coefficient
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃ₐ[R] B) (r : R) :
    localAlgEquivResidue e (algebraMap R (A ⧸ IsLocalRing.maximalIdeal A) r) =
      algebraMap R (B ⧸ IsLocalRing.maximalIdeal B) r :=
  (localAlgEquivResidue e).commutes r

/-- The project quotient/local-residue comparison sends actual quotient classes to their
canonical localization classes. -/
@[simp]
theorem quotient_equiv_local_residue_mk
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (Q : Ideal A) [Q.IsMaximal] (x : A) :
    quotient_equiv_local_residue (R := R) Q (Ideal.Quotient.mk Q x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (algebraMap A (Localization.AtPrime Q) x) := rfl

section NormalizationComparison

variable (R S F : Type*) [CommRing R] [CommRing S] [IsDomain S] [Field F]
  [Algebra R S] [Algebra S F] [FaithfulSMul S F] [Algebra R F] [IsScalarTower R S F]
  (q : Ideal S) [q.IsPrime]
  [Algebra (Localization.AtPrime q) F] [IsScalarTower S (Localization.AtPrime q) F]
  (Q : Ideal (integralClosure S F)) [Q.IsPrime] [Q.LiesOver q]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical normalization local equivalence carries the specified maximal ideals. -/
theorem normalization_maximalIdeal_map :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).map
      (normalizationLocalAlgEquivOverBase R S F q Q).toRingHom =
        IsLocalRing.maximalIdeal (Localization.AtPrime (normalizationPrime S F q Q)) := by
  let e := normalizationLocalAlgEquivOverBase R S F q Q
  change (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).map e.toRingHom =
    IsLocalRing.maximalIdeal (Localization.AtPrime (normalizationPrime S F q Q))
  exact localAlgEquiv_map_maximalIdeal (R := R) (A := Localization.AtPrime Q)
    (B := Localization.AtPrime (normalizationPrime S F q Q)) e

set_option backward.isDefEq.respectTransparency false in
/-- The actual prime indices over the original coefficient ring agree under normalization
localization. The intermediate maximal-ideal identification is proved explicitly. -/
theorem normalization_ramificationIdx :
    Q.ramificationIdx R = (normalizationPrime S F q Q).ramificationIdx R := by
  have h := ramificationIdx_map_algEquiv (R := R)
    (S := Localization.AtPrime Q) (T := Localization.AtPrime (normalizationPrime S F q Q))
    (normalizationLocalAlgEquivOverBase R S F q Q)
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
  change ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).map
      (normalizationLocalAlgEquivOverBase R S F q Q).toRingHom).ramificationIdx R =
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).ramificationIdx R at h
  rw [normalization_maximalIdeal_map R S F q Q,
    ramificationIdx_localization_atPrime, ramificationIdx_localization_atPrime] at h
  exact h.symm

variable [Q.IsMaximal] [(normalizationPrime S F q Q).IsMaximal]

/-- Canonical quotient comparison for the actual normalization prime. It is composed from
both quotient/local-residue comparisons and the residue map of the canonical local equivalence. -/
noncomputable def normalizationQuotientAlgEquiv :
    (integralClosure S F ⧸ Q) ≃ₐ[R]
      integralClosure (Localization.AtPrime q) F ⧸ normalizationPrime S F q Q :=
  (quotient_equiv_local_residue (R := R) Q).trans
    ((localAlgEquivResidue (R := R) (A := Localization.AtPrime Q)
      (B := Localization.AtPrime (normalizationPrime S F q Q))
      (normalizationLocalAlgEquivOverBase R S F q Q)).trans
        (quotient_equiv_local_residue (R := R) (normalizationPrime S F q Q)).symm)

/-- The quotient comparison is induced by the actual normalization inclusion on quotient classes. -/
@[simp]
theorem normalizationQuotientAlgEquiv_mk (x : integralClosure S F) :
    normalizationQuotientAlgEquiv R S F q Q (Ideal.Quotient.mk Q x) =
      Ideal.Quotient.mk (normalizationPrime S F q Q) (normalizationMap S (Localization.AtPrime q) F x) := by
  apply (quotient_equiv_local_residue (R := R) (normalizationPrime S F q Q)).injective
  simp only [normalizationQuotientAlgEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    quotient_equiv_local_residue_mk, localAlgEquivResidue_mk,
    normalizationLocalAlgEquivOverBase_apply, normalizationLocalAlgEquiv_algebraMap]

/-- Original `R` coefficients are preserved by the canonical normalization quotient comparison. -/
@[simp]
theorem normalizationQuotientAlgEquiv_coefficient (r : R) :
    normalizationQuotientAlgEquiv R S F q Q (algebraMap R (integralClosure S F ⧸ Q) r) =
      algebraMap R (integralClosure (Localization.AtPrime q) F ⧸ normalizationPrime S F q Q) r :=
  (normalizationQuotientAlgEquiv R S F q Q).commutes r

variable (p : Ideal R) [Q.LiesOver p] [(normalizationPrime S F q Q).LiesOver p]

/-- The same quotient map as an algebra equivalence over the original residue base `R ⧸ p`.
The quotient algebras and scalar towers are the canonical ones from the two lying-over inputs. -/
noncomputable def normalizationResidueAlgEquiv :
    (integralClosure S F ⧸ Q) ≃ₐ[R ⧸ p]
      integralClosure (Localization.AtPrime q) F ⧸ normalizationPrime S F q Q :=
  (normalizationQuotientAlgEquiv R S F q Q).extendScalarsOfSurjective
    (R := R) (S := R ⧸ p) Ideal.Quotient.mk_surjective

/-- Extending to the residue base changes only the scalar-compatibility proof, not the map. -/
@[simp]
theorem normalizationResidueAlgEquiv_apply (x : integralClosure S F ⧸ Q) :
    normalizationResidueAlgEquiv R S F q Q p x = normalizationQuotientAlgEquiv R S F q Q x := rfl

/-- Exact separability transport over `R ⧸ p`, between the two specified prime quotients. -/
theorem normalization_residueSeparable_iff :
    Algebra.IsSeparable (R ⧸ p) (integralClosure S F ⧸ Q) ↔
      Algebra.IsSeparable (R ⧸ p)
        (integralClosure (Localization.AtPrime q) F ⧸ normalizationPrime S F q Q) :=
  AlgEquiv.Algebra.isSeparable_iff (normalizationResidueAlgEquiv R S F q Q p)

end NormalizationComparison

end ZInQ.Contrib.Abhyankar
