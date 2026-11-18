import InertiaRingUnramifiedV002
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.ResidueField.Separable
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Subfields of the inertia field are unramified (Dedekind setting)

Let `A` be a Dedekind domain with fraction field `K`, `L/K` a finite Galois extension, `S` the
integral closure of `A` in `L` with its Galois action, `p` a maximal ideal of `A` with finite
quotient, and `P` a prime of `S` over `p`. Let `E` be the fixed field of the inertia group of `P`
and `F ≤ E` an intermediate field. Then the prime of the integral closure of `A` in `F` below `P`
has ramification index `1` over `A`.

All Galois-ring instances are constructed here: the action of `Gal(L/K)` on `S`,
`IsGaloisGroup Gal(L/K) A S` (from the field-level Galois property), finiteness and flatness of
`S` over `A` (Noetherian integrally closed base, separable extension; Dedekind and torsion-free),
the inertia ring `T` = integral closure of `A` in `E` with `IsGaloisGroup (inertia) T S`, flatness of
`S` over `T` and of `T` over the integral closure of `A` in `F`, and separability of residue field
extensions (finite residue field of `p`).
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open Ideal MulAction

section Generic

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

theorem integral_galAct (σ : L ≃ₐ[K] L) (s : integralClosure A L) :
    σ (s : L) ∈ integralClosure A L :=
  (mem_integralClosure_iff A L).mpr
    (((mem_integralClosure_iff A L).mp s.2).map (σ.toAlgHom.restrictScalars A))

/-- The Galois action on the integral closure. -/
instance galActIntegralClosure : MulSemiringAction (L ≃ₐ[K] L) (integralClosure A L) where
  smul σ s := ⟨σ (s : L), integral_galAct A K L σ s⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (show σ (0 : L) = 0 from map_zero σ)
  smul_add σ s t := Subtype.ext (show σ ((s : L) + t) = σ s + σ t from map_add σ _ _)
  smul_one σ := Subtype.ext (show σ (1 : L) = 1 from map_one σ)
  smul_mul σ s t := Subtype.ext (show σ ((s : L) * t) = σ s * σ t from map_mul σ _ _)

theorem coe_galAct (σ : L ≃ₐ[K] L) (s : integralClosure A L) :
    ((σ • s : integralClosure A L) : L) = σ (s : L) :=
  rfl

instance smulDistribClass_galAct :
    SMulDistribClass (L ≃ₐ[K] L) (integralClosure A L) L where
  smul_distrib_smul σ s x := by
    rw [Algebra.smul_def, Algebra.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_mul]
    rfl

/-- The inclusion of integral closures along an inclusion of intermediate fields. -/
def inclLE {F E : IntermediateField K L} (h : F ≤ E) :
    integralClosure A F →+* integralClosure A E where
  toFun x := ⟨IntermediateField.inclusion h (x : F), (mem_integralClosure_iff A E).mpr
    (((mem_integralClosure_iff A F).mp x.2).map ((IntermediateField.inclusion h).restrictScalars A))⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion of the integral closure in an intermediate field into that in `L`. -/
def inclF (F : IntermediateField K L) : integralClosure A F →+* integralClosure A L where
  toFun x := ⟨((x : F) : L), (mem_integralClosure_iff A L).mpr
    (((mem_integralClosure_iff A F).mp x.2).map (F.val.restrictScalars A))⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inertia field of a prime of the integral closure. -/
abbrev inertiaField (P : Ideal (integralClosure A L)) : IntermediateField K L :=
  FixedPoints.intermediateField (P.inertia (L ≃ₐ[K] L))

variable [FiniteDimensional K L] [IsGalois K L]

theorem isGaloisGroup_integralClosure :
    IsGaloisGroup (L ≃ₐ[K] L) A (integralClosure A L) := by
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K L
  exact IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A (integralClosure A L) K L

theorem faithfulSMul_integralClosure (F : IntermediateField K L) :
    FaithfulSMul A (integralClosure A F) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b hab
  have h := congrArg (fun z : integralClosure A F => ((z : F) : L)) hab
  change algebraMap A L a = algebraMap A L b at h
  rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h
  exact IsFractionRing.injective A K ((algebraMap K L).injective h)

/-- **Subfields of the inertia field are unramified.** -/
theorem ramificationIdx_eq_one_of_le_inertiaField (p : Ideal A) [p.IsMaximal] [Finite (A ⧸ p)]
    (P : Ideal (integralClosure A L)) [P.IsPrime] [P.LiesOver p] (F : IntermediateField K L)
    (hF : F ≤ inertiaField A K L P) :
    (P.comap (inclF A K L F)).ramificationIdx A = 1 := by
  classical
  let E := inertiaField A K L P
  let S := integralClosure A L
  let T := integralClosure A E
  let T' := integralClosure A F
  let G := L ≃ₐ[K] L
  let H : Subgroup G := P.inertia G
  have hGal : IsGaloisGroup G A S := isGaloisGroup_integralClosure A K L
  have hfrS : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have hfrT : IsFractionRing T E := integralClosure.isFractionRing_of_finite_extension (A := A) K E
  have hfrT' : IsFractionRing T' F :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K F
  have hsepE : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  have hsepF : Algebra.IsSeparable K F := Algebra.isSeparable_tower_bot_of_isSeparable K F L
  have hdT : IsDedekindDomain T := integralClosure.isDedekindDomain A K E
  have hdT' : IsDedekindDomain T' := integralClosure.isDedekindDomain A K F
  -- `S` over `A`
  have hfinS : Module.Finite A S := IsIntegralClosure.finite A K L S
  have hfaithS : FaithfulSMul A S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h := congrArg (fun z : S => (z : L)) hab
    change algebraMap A L a = algebraMap A L b at h
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h
    exact IsFractionRing.injective A K ((algebraMap K L).injective h)
  -- the inertia ring
  let _ : Algebra T S := (inclF A K L E).toAlgebra
  have hstAT : IsScalarTower A T S := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    rfl
  have hstTSL : IsScalarTower T S L := IsScalarTower.of_algebraMap_eq fun t => by
    rfl
  have hintTS : Algebra.IsIntegral T S := Algebra.IsIntegral.tower_top A
  have hfinTS : Module.Finite T S := Module.Finite.of_restrictScalars_finite A T S
  have hfaithTS : FaithfulSMul T S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h := congrArg (fun z : S => (z : L)) hab
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hsmulH : SMulDistribClass H S L :=
    ⟨fun h s x => smul_distrib_smul (h : G) s x⟩
  have hGalE : IsGaloisGroup H E L := IsGaloisGroup.subgroup G K L H
  have hGalT : IsGaloisGroup H T S := IsGaloisGroup.of_isFractionRing H T S E L
  -- residue fields
  have hfinRes : Finite p.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField p).2
  have : Fintype p.ResidueField := Fintype.ofFinite _
  have hsepS : Algebra.HasSeparableResidueFieldsAt A S p := inferInstance
  have hlies : (P.under T).LiesOver p := Ideal.LiesOver.tower_bot P (P.under T) p
  have hsepT : Algebra.HasSeparableResidueFieldsAt T S (P.under T) :=
    Algebra.HasSeparableResidueFieldsAt.tower_top p (P.under T)
  -- the lower ring `T'`
  let _ : Algebra T' T := (inclLE A K L hF).toAlgebra
  have hstAT' : IsScalarTower A T' T := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hfaithT'T : FaithfulSMul T' T := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h := congrArg (fun z : T => ((z : E) : L)) hab
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have key := ramificationIdx_under_eq_one_of_le_inertiaRing (R := A) (T := T) (S := S)
    (G := G) (T' := T') p P
  have hcomp : (P.under T).under T' = P.comap (inclF A K L F) := by
    ext x
    rfl
  rw [hcomp] at key
  exact key

end Generic

end InertiaPointDescent
