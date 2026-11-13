import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Normalization and localization at a coefficient prime

The integral closure of a coefficient localization is the localization of the original
integral closure at the image of the coefficient prime complement. The algebra map between
these integral closures is the actual inclusion inside the ambient field.

Source provenance: original connecting arguments using Mathlib 4.35.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The principal supplier is
`IsLocalization.integralClosure` in `Mathlib/RingTheory/Localization/Integral.lean`;
prime map/comap and disjointness are in `Localization/Ideal.lean` and `Ideal/Over.lean`;
composition is in `Localization/LocalizationLocalization.lean`. The localization files are
Apache-2.0 licensed and credit Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston,
and Anne Baanen; `Ideal/Over.lean` credits Anne Baanen and Yongle Hu. Top-ring restriction uses
`IsScalarTower.to₁₂₄` and `IsScalarTower.to₁₃₄` from `Algebra/Group/Action/Defs.lean`.
`Localization/AtPrime/Extension.lean` (Xavier Roblot) was inspected; its Dedekind-specific
prime equivalence is not assumed here. No external proof is ported.

This module does not construct a tame root model or assert an assembled T2 theorem.
-/

namespace ZInQ.Contrib.Abhyankar

section NormalizationMap

variable (S B F : Type*) [CommRing S] [CommRing B] [CommRing F]
  [Algebra S B] [Algebra S F] [Algebra B F] [IsScalarTower S B F]

/-- The actual inclusion of the integral closures, induced by the identity on the ambient ring.
Integrality over `S` implies integrality over `B` by mapping the monic polynomial's coefficients. -/
def normalizationMap : integralClosure S F →ₐ[S] integralClosure B F where
  toFun x := ⟨(x : F), x.property.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := Subtype.ext rfl

/-- Algebra structure on the localized integral closure coming from the actual inclusion. -/
instance (priority := 100) normalizationAlgebra :
    Algebra (integralClosure S F) (integralClosure B F) :=
  (normalizationMap S B F).toRingHom.toAlgebra

/-- The map between normalizations is the identity on their underlying ambient elements. -/
@[simp]
theorem normalizationMap_coe (x : integralClosure S F) :
    (normalizationMap S B F x : F) = (x : F) := rfl

/-- The installed algebra map is precisely `normalizationMap`. -/
@[simp]
theorem normalization_algebraMap (x : integralClosure S F) :
    algebraMap (integralClosure S F) (integralClosure B F) x = normalizationMap S B F x := rfl

/-- Compatibility with the original coefficient map. -/
@[simp]
theorem normalizationMap_algebraMap (s : S) :
    normalizationMap S B F (algebraMap S (integralClosure S F) s) =
      algebraMap S (integralClosure B F) s :=
  (normalizationMap S B F).commutes s

/-- The original coefficients act compatibly through the inclusion of integral closures. -/
instance normalization_sourceTower :
    IsScalarTower S (integralClosure S F) (integralClosure B F) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

/-- Both integral closures have the same prescribed embedding in the ambient ring. -/
instance normalization_ambientTower :
    IsScalarTower (integralClosure S F) (integralClosure B F) F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The identity-on-elements normalization map is injective. -/
theorem normalizationMap_injective : Function.Injective (normalizationMap S B F) :=
  fun _ _ h => Subtype.ext (congrArg (fun x : integralClosure B F => (x : F)) h)

end NormalizationMap

section FieldLocalization

variable (S F : Type*) [CommRing S] [IsDomain S] [Field F] [Algebra S F] [FaithfulSMul S F]
  (q : Ideal S) [q.IsPrime]

/-- Every element outside the coefficient prime maps to a nonzero unit of the ambient field. -/
theorem normalizationPrimeCompl_isUnit (m : q.primeCompl) : IsUnit (algebraMap S F m) := by
  apply IsUnit.mk0
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective S F)).mpr
    (nonZeroDivisors.ne_zero (q.primeCompl_le_nonZeroDivisors m.property))

/-- Canonical extension of the coefficient embedding to its prime localization. -/
noncomputable def normalizationAtPrimeToField : Localization.AtPrime q →ₐ[S] F :=
  IsLocalization.liftAlgHom (M := q.primeCompl) (f := Algebra.ofId S F)
    (normalizationPrimeCompl_isUnit S F q)

/-- The canonical extension agrees with the prescribed coefficient embedding. -/
@[simp]
theorem normalizationAtPrimeToField_algebraMap (s : S) :
    normalizationAtPrimeToField S F q (algebraMap S (Localization.AtPrime q) s) =
      algebraMap S F s :=
  (normalizationAtPrimeToField S F q).commutes s

/-- The canonical localization-to-field map is injective, not merely a chosen homomorphism. -/
theorem normalizationAtPrimeToField_injective :
    Function.Injective (normalizationAtPrimeToField S F q) := by
  change Function.Injective (normalizationAtPrimeToField S F q).toRingHom
  apply IsLocalization.injective_of_map_algebraMap_zero (M := q.primeCompl)
    (Localization.AtPrime q) (normalizationAtPrimeToField S F q).toRingHom
  intro s hs
  have hsF : algebraMap S F s = 0 := by
    change normalizationAtPrimeToField S F q (algebraMap S (Localization.AtPrime q) s) = 0 at hs
    rwa [normalizationAtPrimeToField_algebraMap] at hs
  have hs0 : s = 0 := (FaithfulSMul.algebraMap_injective S F) (by simpa only [map_zero] using hsF)
  simp only [hs0, map_zero]

/-- Default canonical field algebra for a coefficient prime localization. Local explicitly
provided compatible algebra instances may instead be supplied to the subsequent theorems. -/
noncomputable instance (priority := 100) normalizationAtPrimeFieldAlgebra :
    Algebra (Localization.AtPrime q) F :=
  (normalizationAtPrimeToField S F q).toRingHom.toAlgebra

/-- The default extension forms the required coefficient/localization/field scalar tower. -/
instance normalizationAtPrimeFieldTower : IsScalarTower S (Localization.AtPrime q) F :=
  IsScalarTower.of_algebraMap_eq fun s =>
    (normalizationAtPrimeToField_algebraMap S F q s).symm

/-- The default field algebra is faithful. -/
instance normalizationAtPrimeFieldFaithful : FaithfulSMul (Localization.AtPrime q) F :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (normalizationAtPrimeToField_injective S F q)

/-- The ambient field is its own localization at the image of the coefficient complement. -/
theorem normalizationField_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid F q.primeCompl) F := by
  apply IsLocalization.of_le_isUnit
  rintro _ ⟨m, hm, rfl⟩
  exact normalizationPrimeCompl_isUnit S F q ⟨m, hm⟩

end FieldLocalization

section NormalizationLocalization

variable (S B F : Type*) [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
  [Field F] [Algebra S F] [FaithfulSMul S F] [Algebra B F] [IsScalarTower S B F]
  (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime B q]

/-- Taking the actual integral closure commutes with coefficient localization at `q`.
The algebra and scalar-tower instances above fix the inclusion and all comparison maps. -/
theorem normalization_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl)
      (integralClosure B F) := by
  let := normalizationField_isLocalization S F q
  exact IsLocalization.integralClosure (R := S) (S := F) (Rf := B) (Sf := F) q.primeCompl

end NormalizationLocalization

section NormalizationAtPrime

variable (S F : Type*) [CommRing S] [IsDomain S] [Field F] [Algebra S F] [FaithfulSMul S F]
  (q : Ideal S) [q.IsPrime]
  [Algebra (Localization.AtPrime q) F] [IsScalarTower S (Localization.AtPrime q) F]

/-- Concrete coefficient-prime version of normalization localization. The field algebra may
be supplied explicitly; otherwise the canonical injective extension above is used. -/
instance normalizationAtPrime_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl)
      (integralClosure (Localization.AtPrime q) F) :=
  normalization_isLocalization S (Localization.AtPrime q) F q

/-- The actual extension of an ideal of the original normalization to the localized normalization.
No prime or lying-over property is assumed in this definition. -/
def normalizationPrime (Q : Ideal (integralClosure S F)) :
    Ideal (integralClosure (Localization.AtPrime q) F) :=
  Q.map (algebraMap (integralClosure S F) (integralClosure (Localization.AtPrime q) F))

variable (Q : Ideal (integralClosure S F)) [Q.IsPrime] [Q.LiesOver q]

omit [IsDomain S] [FaithfulSMul S F] [Algebra (Localization.AtPrime q) F]
  [IsScalarTower S (Localization.AtPrime q) F] [Q.IsPrime] in
/-- Every prime of the original normalization above `q` is disjoint from the actual inverted set. -/
theorem normalizationPrime_disjoint :
    Disjoint (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl : Set (integralClosure S F))
      (Q : Set (integralClosure S F)) :=
  Ideal.disjoint_primeCompl_of_liesOver Q q

/-- Extension of each lying-over prime is a genuine prime of the localized normalization. -/
instance normalizationPrime_isPrime : (normalizationPrime S F q Q).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl)
    (integralClosure (Localization.AtPrime q) F) Q inferInstance
    (normalizationPrime_disjoint S F q Q)

/-- Contracting the extended prime along the actual normalization inclusion recovers `Q`. -/
@[simp]
theorem normalizationPrime_comap :
    (normalizationPrime S F q Q).comap
      (algebraMap (integralClosure S F) (integralClosure (Localization.AtPrime q) F)) = Q :=
  IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl)
    (integralClosure (Localization.AtPrime q) F) inferInstance
    (normalizationPrime_disjoint S F q Q)

/-- The constructed prime lies over the given prime, not a separately chosen factor. -/
instance normalizationPrime_liesOver : (normalizationPrime S F q Q).LiesOver Q :=
  ⟨(normalizationPrime_comap S F q Q).symm⟩

/-- The constructed prime also lies over the maximal ideal of the coefficient localization. -/
instance normalizationPrime_liesOver_maximalIdeal :
    (normalizationPrime S F q Q).LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  have h : (normalizationPrime S F q Q).LiesOver (q.map (algebraMap S (Localization.AtPrime q))) :=
    IsLocalization.liesOver_of_isPrime_of_disjoint
      (R' := Localization.AtPrime q) (S' := integralClosure (Localization.AtPrime q) F)
      q.primeCompl (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl) q
      (normalizationPrime_disjoint S F q Q)
  simpa only [Localization.AtPrime.map_eq_maximalIdeal] using h

/-- Localizing the localized normalization at the constructed prime is the original
normalization localized at `Q`, with its actual coefficient algebra structure. -/
instance normalizationPrime_isLocalizationAtPrime :
    IsLocalization.AtPrime (Localization.AtPrime (normalizationPrime S F q Q)) Q := by
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl)
    (Localization.AtPrime (normalizationPrime S F q Q)) (normalizationPrime S F q Q)
  simpa only [normalizationPrime_comap] using h

/-- Canonical `S`-algebra equivalence between normalization-then-prime-localization and
prime-localization of the original normalization, for every prime above `q`. -/
noncomputable def normalizationLocalAlgEquiv :
    Localization.AtPrime Q ≃ₐ[S] Localization.AtPrime (normalizationPrime S F q Q) :=
  (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q) (Localization.AtPrime (normalizationPrime S F q Q))).restrictScalars S

/-- The canonical local equivalence extends the actual normalization inclusion. -/
@[simp]
theorem normalizationLocalAlgEquiv_algebraMap (x : integralClosure S F) :
    normalizationLocalAlgEquiv S F q Q (algebraMap (integralClosure S F) (Localization.AtPrime Q) x) =
      algebraMap (integralClosure (Localization.AtPrime q) F)
        (Localization.AtPrime (normalizationPrime S F q Q))
        (normalizationMap S (Localization.AtPrime q) F x) := by
  change (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q) (Localization.AtPrime (normalizationPrime S F q Q)))
      (algebraMap (integralClosure S F) (Localization.AtPrime Q) x) = _
  rw [AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply (integralClosure S F) (integralClosure (Localization.AtPrime q) F),
    normalization_algebraMap]

/-- Coefficient compatibility of the actual local equivalence. -/
@[simp]
theorem normalizationLocalAlgEquiv_coefficient (s : S) :
    normalizationLocalAlgEquiv S F q Q (algebraMap S (Localization.AtPrime Q) s) =
      algebraMap S (Localization.AtPrime (normalizationPrime S F q Q)) s :=
  (normalizationLocalAlgEquiv S F q Q).commutes s

/-- The local equivalence preserves the actual canonical embeddings in the ambient field. -/
theorem normalizationLocalAlgEquiv_field (x : Localization.AtPrime Q) :
    algebraMap (Localization.AtPrime (normalizationPrime S F q Q)) F
      (normalizationLocalAlgEquiv S F q Q x) = algebraMap (Localization.AtPrime Q) F x := by
  have h : (algebraMap (Localization.AtPrime (normalizationPrime S F q Q)) F).comp
      (normalizationLocalAlgEquiv S F q Q).toRingHom = algebraMap (Localization.AtPrime Q) F := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    ext t
    change algebraMap (Localization.AtPrime (normalizationPrime S F q Q)) F
      (normalizationLocalAlgEquiv S F q Q (algebraMap (integralClosure S F) (Localization.AtPrime Q) t)) =
        algebraMap (Localization.AtPrime Q) F (algebraMap (integralClosure S F) (Localization.AtPrime Q) t)
    rw [normalizationLocalAlgEquiv_algebraMap,
      ← IsScalarTower.algebraMap_apply (integralClosure (Localization.AtPrime q) F)
        (Localization.AtPrime (normalizationPrime S F q Q)) F,
      ← IsScalarTower.algebraMap_apply (integralClosure S F) (Localization.AtPrime Q) F]
    rfl
  exact RingHom.congr_fun h x

omit [IsDomain S] [FaithfulSMul S F] [Q.IsPrime] [Q.LiesOver q] in
/-- Contracting any prime above the coefficient-localization maximal ideal gives a prime-family
member over `q`. This is the reverse direction, without a chosen factor or finiteness assumption. -/
theorem normalizationComap_liesOver
    (P : Ideal (integralClosure (Localization.AtPrime q) F))
    [P.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime q))] :
    (P.comap (algebraMap (integralClosure S F) (integralClosure (Localization.AtPrime q) F))).LiesOver q := by
  have : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).LiesOver q := inferInstance
  have : P.LiesOver q := Ideal.LiesOver.trans P (IsLocalRing.maximalIdeal (Localization.AtPrime q)) q
  exact Ideal.comap_liesOver P q (normalizationMap S (Localization.AtPrime q) F)

/-- Bijection of the complete prime families on both sides of normalization localization.
It includes zero primes when they occur; no Dedekind, nonzero-prime, or finiteness hypothesis is used. -/
noncomputable def normalizationPrimeFamilyEquiv :
    { Q : Ideal (integralClosure S F) // Q.IsPrime ∧ Q.LiesOver q } ≃
      { P : Ideal (integralClosure (Localization.AtPrime q) F) //
        P.IsPrime ∧ P.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime q)) } where
  toFun Q := by
    let := Q.property.1
    let := Q.property.2
    exact ⟨normalizationPrime S F q Q.val, inferInstance, inferInstance⟩
  invFun P := by
    let := P.property.1
    let := P.property.2
    exact ⟨P.val.comap (algebraMap (integralClosure S F) (integralClosure (Localization.AtPrime q) F)),
      inferInstance, normalizationComap_liesOver S F q P.val⟩
  left_inv Q := by
    let := Q.property.1
    let := Q.property.2
    apply Subtype.ext
    exact normalizationPrime_comap S F q Q.val
  right_inv P := by
    apply Subtype.ext
    exact IsLocalization.map_under
      (Algebra.algebraMapSubmonoid (integralClosure S F) q.primeCompl)
      (integralClosure (Localization.AtPrime q) F) P.val

end NormalizationAtPrime

section NormalizationOverBase

variable (R S F : Type*) [CommRing R] [CommRing S] [IsDomain S] [Field F]
  [Algebra R S] [Algebra S F] [FaithfulSMul S F] [Algebra R F] [IsScalarTower R S F]
  (q : Ideal S) [q.IsPrime]
  [Algebra (Localization.AtPrime q) F] [IsScalarTower S (Localization.AtPrime q) F]

/-- Compatibility of a top coefficient ring with the actual prime-localization embedding. -/
instance normalizationAtPrime_baseTower : IsScalarTower R (Localization.AtPrime q) F :=
  IsScalarTower.to₁₃₄ R S (Localization.AtPrime q) F

/-- The same canonical local equivalence, over any compatible top coefficient ring `R`. -/
noncomputable def normalizationLocalAlgEquivOverBase
    (Q : Ideal (integralClosure S F)) [Q.IsPrime] [Q.LiesOver q] :
    Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime (normalizationPrime S F q Q) := by
  let := IsScalarTower.to₁₂₄ R S (integralClosure S F) (Localization.AtPrime Q)
  let := IsScalarTower.to₁₂₄ R S (integralClosure (Localization.AtPrime q) F)
    (Localization.AtPrime (normalizationPrime S F q Q))
  exact (normalizationLocalAlgEquiv S F q Q).restrictScalars R

/-- Restricting the base coefficients does not change the actual localization map. -/
@[simp]
theorem normalizationLocalAlgEquivOverBase_apply
    (Q : Ideal (integralClosure S F)) [Q.IsPrime] [Q.LiesOver q]
    (x : Localization.AtPrime Q) :
    normalizationLocalAlgEquivOverBase R S F q Q x = normalizationLocalAlgEquiv S F q Q x := rfl

end NormalizationOverBase

end ZInQ.Contrib.Abhyankar
