/-
# The actual finite localized fixed-field DVR tower

All rings are canonical prime localizations of the constructed F/U/E number
fields. Finiteness is proved using their actual unique-prime fibres. The local
unramifiedness and residue-surjectivity follow from the proved global prime
invariants and canonical localized maps, not assumed comparison facts.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldUnramifiedFactor
public import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldDifferentTransport
public import ZInQKernel.Contrib.GlobalDifferentTransport.NumberFieldLocalRamification

/-!
# Concrete A/U0/B supplier for the given-factor DVR arithmetic

The original field `L=M^H` is not assumed Galois. The ambient field `M/ℚ` is
finite Galois and its prime is nonzero when DVR properties are claimed.
Nothing here proves a derivative, monogenic, Hilbert, or global Serre bound.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open NumberField IsLocalRing
open scoped NumberField Pointwise GlobalDifferentTransportFixedFieldTower

namespace GlobalDifferentTransport.FixedFieldLocalTower

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (P : Ideal (𝓞 M)) [P.IsPrime] (H : Subgroup Gal(M/ℚ))

/-- The actual contracted prime in F. -/
abbrev basePrime := P.under (𝓞 (decompositionFixedField M P))
/-- The actual contracted prime in U. -/
abbrev factorPrime := P.under (𝓞 (unramifiedFactorFixedField M P H))
/-- The actual contracted prime in E. -/
abbrev extensionPrime := P.under (𝓞 (transportedFixedField M P H))

/-- The actual base localization A=(O F)_qF. -/
abbrev baseRing := Localization.AtPrime (basePrime M P)
/-- The actual factor localization U0=(O U)_qU. -/
abbrev factorRing := Localization.AtPrime (factorPrime M P H)
/-- The actual extension localization B=(O E)_qE. -/
abbrev extensionRing := Localization.AtPrime (extensionPrime M P H)

/-- The actual U-prime lies over the actual F-prime. -/
theorem factorPrime_liesOver_base : (factorPrime M P H).LiesOver (basePrime M P) :=
  Ideal.LiesOver.tower_bot P (factorPrime M P H) (basePrime M P)
/-- The actual E-prime lies over the actual U-prime. -/
theorem extensionPrime_liesOver_factor : (extensionPrime M P H).LiesOver (factorPrime M P H) :=
  Ideal.LiesOver.tower_bot P (extensionPrime M P H) (factorPrime M P H)
/-- The actual E-prime lies over the actual F-prime. -/
theorem extensionPrime_liesOver_base : (extensionPrime M P H).LiesOver (basePrime M P) :=
  Ideal.LiesOver.tower_bot P (extensionPrime M P H) (basePrime M P)

scoped[GlobalDifferentTransportLocalizedFixedFieldTower] attribute [instance]
  GlobalDifferentTransport.FixedFieldLocalTower.factorPrime_liesOver_base
  GlobalDifferentTransport.FixedFieldLocalTower.extensionPrime_liesOver_factor
  GlobalDifferentTransport.FixedFieldLocalTower.extensionPrime_liesOver_base

open scoped GlobalDifferentTransportLocalizedFixedFieldTower

/-- The canonical local F/U algebra. -/
@[reducible] def baseFactorAlgebra : Algebra (baseRing M P) (factorRing M P H) :=
  Localization.AtPrime.algebraOfLiesOver (basePrime M P) (factorPrime M P H)
/-- The canonical local U/E algebra. -/
@[reducible] def factorExtensionAlgebra : Algebra (factorRing M P H) (extensionRing M P H) :=
  Localization.AtPrime.algebraOfLiesOver (factorPrime M P H) (extensionPrime M P H)
/-- The canonical local F/E algebra. -/
@[reducible] def baseExtensionAlgebra : Algebra (baseRing M P) (extensionRing M P H) :=
  Localization.AtPrime.algebraOfLiesOver (basePrime M P) (extensionPrime M P H)

scoped[GlobalDifferentTransportLocalizedFixedFieldTower] attribute [instance 50]
  GlobalDifferentTransport.FixedFieldLocalTower.baseFactorAlgebra
  GlobalDifferentTransport.FixedFieldLocalTower.factorExtensionAlgebra
  GlobalDifferentTransport.FixedFieldLocalTower.baseExtensionAlgebra

/-- All three actual localized maps form the same scalar tower. -/
theorem localizations_isScalarTower :
    IsScalarTower (baseRing M P) (factorRing M P H) (extensionRing M P H) := by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [Localization.AtPrime.algebraMap_eq, ← Localization.localRingHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- The canonical local F/U map is local. -/
theorem baseFactor_isLocalHom : IsLocalHom (algebraMap (baseRing M P) (factorRing M P H)) := by
  rw [Localization.AtPrime.algebraMap_eq (basePrime M P) (factorPrime M P H)]
  infer_instance
/-- The canonical local U/E map is local. -/
theorem factorExtension_isLocalHom : IsLocalHom (algebraMap (factorRing M P H) (extensionRing M P H)) := by
  rw [Localization.AtPrime.algebraMap_eq (factorPrime M P H) (extensionPrime M P H)]
  infer_instance
/-- The canonical local F/E map is local. -/
theorem baseExtension_isLocalHom : IsLocalHom (algebraMap (baseRing M P) (extensionRing M P H)) := by
  rw [Localization.AtPrime.algebraMap_eq (basePrime M P) (extensionPrime M P H)]
  infer_instance

scoped[GlobalDifferentTransportLocalizedFixedFieldTower] attribute [instance]
  GlobalDifferentTransport.FixedFieldLocalTower.localizations_isScalarTower
  GlobalDifferentTransport.FixedFieldLocalTower.baseFactor_isLocalHom
  GlobalDifferentTransport.FixedFieldLocalTower.factorExtension_isLocalHom
  GlobalDifferentTransport.FixedFieldLocalTower.baseExtension_isLocalHom

/-- There is a unique actual E-prime above qU, derived from the unique F-prime fibre. -/
theorem extension_primesOver_factor :
    Ideal.primesOver (factorPrime M P H) (𝓞 (transportedFixedField M P H)) =
      {extensionPrime M P H} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro Q ⟨hQ, hQU⟩
  let := hQ
  let := hQU
  let : Q.LiesOver (basePrime M P) := Ideal.LiesOver.trans Q (factorPrime M P H) (basePrime M P)
  have hm : Q ∈ Ideal.primesOver (basePrime M P) (𝓞 (transportedFixedField M P H)) :=
    ⟨inferInstance, inferInstance⟩
  rw [transportedFixedField_primesOver M P H, Set.mem_singleton_iff] at hm
  exact hm

/-- The actual F/U localized extension is genuinely finite. -/
theorem factorRing_moduleFinite : Module.Finite (baseRing M P) (factorRing M P H) := by
  let : Module.Finite (𝓞 (decompositionFixedField M P)) (𝓞 (unramifiedFactorFixedField M P H)) :=
    Module.Finite.right ℤ _ _
  exact moduleFinite_atPrime_of_unique (basePrime M P) (factorPrime M P H)
    (unramifiedFactorFixedField_primesOver M P H)

/-- The actual U/E localized extension is genuinely finite. -/
theorem extensionRing_moduleFinite_factor : Module.Finite (factorRing M P H) (extensionRing M P H) := by
  let : Module.Finite (𝓞 (unramifiedFactorFixedField M P H)) (𝓞 (transportedFixedField M P H)) :=
    Module.Finite.right ℤ _ _
  exact moduleFinite_atPrime_of_unique (factorPrime M P H) (extensionPrime M P H)
    (extension_primesOver_factor M P H)

/-- The actual F/E localized extension is genuinely finite. -/
theorem extensionRing_moduleFinite_base : Module.Finite (baseRing M P) (extensionRing M P H) := by
  let : Module.Finite (𝓞 (decompositionFixedField M P)) (𝓞 (transportedFixedField M P H)) :=
    Module.Finite.right ℤ _ _
  exact moduleFinite_atPrime_of_unique (basePrime M P) (extensionPrime M P H)
    (transportedFixedField_primesOver M P H)

/-- The actual local F/U algebra is faithful. -/
theorem factorRing_faithfulSMul : FaithfulSMul (baseRing M P) (factorRing M P H) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (NumberFieldLocalization.atPrime_algebraMap_injective
      (decompositionFixedField M P) (unramifiedFactorFixedField M P H)
      (basePrime M P) (factorPrime M P H))
/-- The actual local U/E algebra is faithful. -/
theorem extensionRing_faithfulSMul_factor : FaithfulSMul (factorRing M P H) (extensionRing M P H) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (NumberFieldLocalization.atPrime_algebraMap_injective
      (unramifiedFactorFixedField M P H) (transportedFixedField M P H)
      (factorPrime M P H) (extensionPrime M P H))
/-- The actual local F/E algebra is faithful. -/
theorem extensionRing_faithfulSMul_base : FaithfulSMul (baseRing M P) (extensionRing M P H) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (NumberFieldLocalization.atPrime_algebraMap_injective
      (decompositionFixedField M P) (transportedFixedField M P H)
      (basePrime M P) (extensionPrime M P H))

scoped[GlobalDifferentTransportLocalizedFixedFieldTower] attribute [instance]
  GlobalDifferentTransport.FixedFieldLocalTower.factorRing_moduleFinite
  GlobalDifferentTransport.FixedFieldLocalTower.extensionRing_moduleFinite_factor
  GlobalDifferentTransport.FixedFieldLocalTower.extensionRing_moduleFinite_base
  GlobalDifferentTransport.FixedFieldLocalTower.factorRing_faithfulSMul
  GlobalDifferentTransport.FixedFieldLocalTower.extensionRing_faithfulSMul_factor
  GlobalDifferentTransport.FixedFieldLocalTower.extensionRing_faithfulSMul_base

/-- The actual local F/U extension is formally unramified by the global unramified prime theorem
and restriction of scalars through the canonical base localization. -/
theorem factorRing_formallyUnramified : Algebra.FormallyUnramified (baseRing M P) (factorRing M P H) := by
  let : Algebra.IsUnramifiedAt (𝓞 (decompositionFixedField M P)) (factorPrime M P H) :=
    unramifiedFactorPrime_isUnramifiedAt_decomposition M P H
  exact Algebra.FormallyUnramified.of_restrictScalars (𝓞 (decompositionFixedField M P))
    (baseRing M P) (factorRing M P H)

/-- The actual local F/U extension is unramified at its actual maximal ideal. -/
theorem factorRing_isUnramifiedAt :
    Algebra.IsUnramifiedAt (baseRing M P) (maximalIdeal (factorRing M P H)) := by
  let := factorRing_formallyUnramified M P H
  infer_instance

/-- The actual U/E residue-field map is surjective, because its proved global inertia degree
is one and `Ideal.inertiaDeg_eq` uses these very canonical localizations and residue maps. -/
theorem residueField_factorExtension_surjective :
    Function.Surjective (algebraMap (ResidueField (factorRing M P H)) (ResidueField (extensionRing M P H))) := by
  have hdeg : Module.finrank (ResidueField (factorRing M P H)) (ResidueField (extensionRing M P H)) = 1 := by
    change Module.finrank (factorPrime M P H).ResidueField (extensionPrime M P H).ResidueField = 1
    rw [← Ideal.inertiaDeg_eq (factorPrime M P H) (extensionPrime M P H)]
    exact transportedPrime_inertiaDeg_unramifiedFactor_eq_one M P H
  intro y
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (K := ResidueField (factorRing M P H)) (1 : ResidueField (extensionRing M P H)) one_ne_zero).mp hdeg y
  exact ⟨c, by simpa only [Algebra.smul_def, mul_one] using hc⟩

/-- The literal actual local inclusion followed by reduction is surjective. This is stronger
and more useful than an abstract residue-field isomorphism for the given-factor argument. -/
theorem residue_factorExtension_surjective :
    Function.Surjective ((residue (extensionRing M P H)).comp
      (algebraMap (factorRing M P H) (extensionRing M P H))) := by
  intro y
  obtain ⟨c, hc⟩ := residueField_factorExtension_surjective M P H y
  obtain ⟨u, rfl⟩ := residue_surjective c
  refine ⟨u, ?_⟩
  simpa only [RingHom.comp_apply, ResidueField.algebraMap_residue] using hc

variable (hP : P ≠ ⊥)
include hP

/-- All three actual localized rings are DVRs, with their nonzero prime conditions proved. -/
theorem localizations_areDVR :
    IsDiscreteValuationRing (baseRing M P) ∧ IsDiscreteValuationRing (factorRing M P H) ∧
      IsDiscreteValuationRing (extensionRing M P H) := by
  have hF : basePrime M P ≠ ⊥ := decompositionFixedField_under_ne_bot M P hP
  have hU : factorPrime M P H ≠ ⊥ := numberField_under_prime_ne_bot (unramifiedFactorFixedField M P H) M P hP
  have hE : extensionPrime M P H ≠ ⊥ := numberField_under_prime_ne_bot (transportedFixedField M P H) M P hP
  exact ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hF _,
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hU _,
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hE _⟩

/-- The actual local F/E ramification index is the original global L/ℚ index. -/
theorem extensionRing_ramificationIdx_eq_original :
    (maximalIdeal (extensionRing M P H)).ramificationIdx (baseRing M P) =
      (P.under (𝓞 (originalFixedField M H))).ramificationIdx ℤ := by
  rw [NumberFieldLocalization.ramificationIdx_atPrime_eq
    (decompositionFixedField M P) (transportedFixedField M P H)
    (basePrime M P) (extensionPrime M P H)
    (numberField_under_prime_ne_bot (transportedFixedField M P H) M P hP)]
  exact ramificationIdx_transportedRelative_eq_originalAbsolute M P H hP

/-- The actual local F/E different coefficient is the original global L/ℚ different coefficient. -/
theorem extensionRing_differentMultiplicity_eq_original :
    multiplicity (maximalIdeal (extensionRing M P H)) (differentIdeal (baseRing M P) (extensionRing M P H)) =
      multiplicity (P.under (𝓞 (originalFixedField M H)))
        (differentIdeal ℤ (𝓞 (originalFixedField M H))) :=
  multiplicity_localizedTransportedDifferent_eq_originalAbsolute M P H hP

end GlobalDifferentTransport.FixedFieldLocalTower
