/-
# Canonical rational-completion/padic field model

This module consumes the native Mathlib continuous Q-algebra and Z-algebra
completion equivalences for the actual affine base Z/Q. The new padic scalar
maps are their actual inverses followed by the proved completion maps. All
integer/field/base inclusion squares are proved; no isometry or local field
model is assumed, and no local Kronecker-Weber theorem is used.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.CompletedAbelian
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Actual Qp and Zp scalar models for the completed number field

The rational and integer equivalences below are pinned native suppliers, not an
identification of the ring of integers of Q with Z. Their inverse-direction
inclusion square is consumed to prove the actual padic scalar tower.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField GlobalDifferentTransportCompletion

namespace GlobalDifferentTransport

/-- The actual rational prime associated with the chosen height-one ideal of Z. -/
abbrev completionPrime (v : HeightOneSpectrum ℤ) : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv v

-- This is the native arithmetic prime tag, derived from a proved Nat.Primes value;
-- it contains no Galois, comparison, or local-model assertion.
local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The actual native continuous Q-algebra equivalence for the rational affine completion. -/
def rationalCompletionPadicEquiv (v : HeightOneSpectrum ℤ) :
    v.adicCompletion ℚ ≃A[ℚ] ℚ_[completionPrime v] :=
  Rat.HeightOneSpectrum.adicCompletion.padicEquiv v

/-- Its actual native continuous Z-algebra integer-ring equivalence. -/
def rationalCompletionIntegersPadicEquiv (v : HeightOneSpectrum ℤ) :
    v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[completionPrime v] := by
  let E : v.adicCompletionIntegers ℚ ≃+* ℤ_[completionPrime v] := by
    let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
    exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  let H : v.adicCompletionIntegers ℚ ≃ₜ ℤ_[completionPrime v] := by
    let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
    exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph
  exact
    { __ := AlgEquiv.ofRingEquiv (f := E) fun z ↦ by
        rw [show algebraMap ℤ (v.adicCompletionIntegers ℚ) z = (z : v.adicCompletionIntegers ℚ)
            from map_intCast (algebraMap ℤ (v.adicCompletionIntegers ℚ)) z,
          show algebraMap ℤ ℤ_[completionPrime v] z = (z : ℤ_[completionPrime v])
            from map_intCast (algebraMap ℤ ℤ_[completionPrime v]) z]
        exact map_intCast E z
      continuous_toFun := H.continuous_toFun
      continuous_invFun := H.continuous_invFun }

/-- The two actual native equivalences commute with the integer-to-field inclusions. -/
theorem rationalPadic_integer_field_square (v : HeightOneSpectrum ℤ)
    (x : v.adicCompletionIntegers ℚ) :
    (rationalCompletionIntegersPadicEquiv v x : ℚ_[completionPrime v]) =
      rationalCompletionPadicEquiv v (x : v.adicCompletion ℚ) :=
  Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_apply v x

/-- The actual inverse equivalences commute with the same inclusions. -/
theorem rationalPadic_integer_field_inverse_square (v : HeightOneSpectrum ℤ)
    (x : ℤ_[completionPrime v]) :
    ((rationalCompletionIntegersPadicEquiv v).symm x : v.adicCompletion ℚ) =
      (rationalCompletionPadicEquiv v).symm (x : ℚ_[completionPrime v]) :=
  Rat.HeightOneSpectrum.adicCompletionIntegers.coe_padicIntEquiv_symm_apply v x

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The actual Qp-algebra of the completed extension: inverse rational equivalence followed
by the original canonical completion map. It is named and scoped, not a model default. -/
@[reducible] def padicCompletionAlgebra : Algebra ℚ_[completionPrime v] (w.adicCompletion L) :=
  ((completionRingHom ℚ L v w).comp
    (rationalCompletionPadicEquiv v).symm.toAlgEquiv.toRingHom).toAlgebra

/-- The actual Zp-algebra of completed integers, using the native inverse integer equivalence. -/
@[reducible] def padicCompletionIntegersAlgebra :
    Algebra ℤ_[completionPrime v] (w.adicCompletionIntegers L) :=
  ((completionIntegersRingHom ℚ L v w).comp
    (rationalCompletionIntegersPadicEquiv v).symm.toAlgEquiv.toRingHom).toAlgebra

scoped[GlobalDifferentTransportPadicCompletion] attribute [instance 50]
  GlobalDifferentTransport.padicCompletionAlgebra
  GlobalDifferentTransport.padicCompletionIntegersAlgebra

open scoped GlobalDifferentTransportPadicCompletion

/-- The exact Qp field map is the named inverse equivalence followed by completion. -/
theorem algebraMap_padicCompletionAlgebra :
    algebraMap ℚ_[completionPrime v] (w.adicCompletion L) =
      (completionRingHom ℚ L v w).comp
        (rationalCompletionPadicEquiv v).symm.toAlgEquiv.toRingHom := rfl

/-- The exact Zp integer map is the named inverse integer equivalence followed by completion. -/
theorem algebraMap_padicCompletionIntegersAlgebra :
    algebraMap ℤ_[completionPrime v] (w.adicCompletionIntegers L) =
      (completionIntegersRingHom ℚ L v w).comp
        (rationalCompletionIntegersPadicEquiv v).symm.toAlgEquiv.toRingHom := rfl

/-- The actual padic scalar maps commute with the target integer-to-field inclusion. -/
theorem padicCompletion_integer_field_square (x : ℤ_[completionPrime v]) :
    algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
        (algebraMap ℤ_[completionPrime v] (w.adicCompletionIntegers L) x) =
      algebraMap ℚ_[completionPrime v] (w.adicCompletion L) (x : ℚ_[completionPrime v]) := by
  change completionRingHom ℚ L v w
      ((rationalCompletionIntegersPadicEquiv v).symm x : v.adicCompletion ℚ) =
    completionRingHom ℚ L v w ((rationalCompletionPadicEquiv v).symm (x : ℚ_[completionPrime v]))
  rw [rationalPadic_integer_field_inverse_square]

/-- The induced Zp-to-completed-field algebra is the same actual Qp field inclusion. -/
@[reducible] def padicIntegersToCompletedFieldAlgebra : Algebra ℤ_[completionPrime v] (w.adicCompletion L) :=
  ((algebraMap ℚ_[completionPrime v] (w.adicCompletion L)).comp
    (algebraMap ℤ_[completionPrime v] ℚ_[completionPrime v])).toAlgebra

scoped[GlobalDifferentTransportPadicCompletion] attribute [instance 50]
  GlobalDifferentTransport.padicIntegersToCompletedFieldAlgebra

/-- The actual Zp/Qp/completed-field scalar tower. -/
theorem padicIntegersFieldIsScalarTower :
    IsScalarTower ℤ_[completionPrime v] ℚ_[completionPrime v] (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The actual Zp/completed-integers/completed-field tower uses the identical scalar map. -/
theorem padicIntegersCompletedIsScalarTower :
    IsScalarTower ℤ_[completionPrime v] (w.adicCompletionIntegers L) (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (padicCompletion_integer_field_square L v w x).symm

/-- The rational scalars agree with the actual Qp field map. -/
theorem rationalPadicCompletedIsScalarTower :
    IsScalarTower ℚ ℚ_[completionPrime v] (w.adicCompletion L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap L (w.adicCompletion L) (algebraMap ℚ L x) =
    completionRingHom ℚ L v w
      ((rationalCompletionPadicEquiv v).symm (algebraMap ℚ ℚ_[completionPrime v] x))
  have he : (rationalCompletionPadicEquiv v).symm (algebraMap ℚ ℚ_[completionPrime v] x) =
      algebraMap ℚ (v.adicCompletion ℚ) x := (rationalCompletionPadicEquiv v).symm.commutes x
  rw [he]
  exact (completionRingHom_coe ℚ L v w x).symm

/-- The rational completion acts on Qp through the actual native algebra equivalence. -/
@[reducible] def rationalCompletionToPadicAlgebra : Algebra (v.adicCompletion ℚ) ℚ_[completionPrime v] :=
  (rationalCompletionPadicEquiv v).toAlgEquiv.toRingHom.toAlgebra

scoped[GlobalDifferentTransportPadicCompletion] attribute [instance 50]
  GlobalDifferentTransport.rationalCompletionToPadicAlgebra

/-- The original completed rational base, Qp, and completed extension form the actual tower.
This is the square used to rebase Galoisness and the automorphism group. -/
theorem completionPadicCompletedIsScalarTower :
    IsScalarTower (v.adicCompletion ℚ) ℚ_[completionPrime v] (w.adicCompletion L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change completionRingHom ℚ L v w x =
    completionRingHom ℚ L v w ((rationalCompletionPadicEquiv v).symm (rationalCompletionPadicEquiv v x))
  rw [ContinuousAlgEquiv.symm_apply_apply]

scoped[GlobalDifferentTransportPadicCompletion] attribute [instance]
  GlobalDifferentTransport.padicIntegersFieldIsScalarTower
  GlobalDifferentTransport.padicIntegersCompletedIsScalarTower
  GlobalDifferentTransport.rationalPadicCompletedIsScalarTower
  GlobalDifferentTransport.completionPadicCompletedIsScalarTower

/-- Genuine Galoisness on the actual Qp-based field model, rebased through the proved square. -/
theorem isGalois_padicNumberFieldCompletion [IsGalois ℚ L] :
    IsGalois ℚ_[completionPrime v] (w.adicCompletion L) := by
  let := isGalois_numberFieldCompletion L v w
  exact IsGalois.tower_top_of_isGalois (v.adicCompletion ℚ) ℚ_[completionPrime v] (w.adicCompletion L)

/-- Genuine native abelian-Galoisness on that identical Qp-based completed field model. -/
theorem isAbelianGalois_padicNumberFieldCompletion [IsAbelianGalois ℚ L] :
    IsAbelianGalois ℚ_[completionPrime v] (w.adicCompletion L) := by
  let := isAbelianGalois_numberFieldCompletion L v w
  exact IsAbelianGalois.tower_top (v.adicCompletion ℚ) ℚ_[completionPrime v] (w.adicCompletion L)

/-- Rebase the actual completed field automorphism group through the native Qp equivalence,
without changing its action on any field element. -/
def padicCompletedFieldAutMulEquiv :
    (w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) ≃*
      (w.adicCompletion L ≃ₐ[ℚ_[completionPrime v]] w.adicCompletion L) where
  toFun τ := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x ↦ by
    change τ (completionRingHom ℚ L v w ((rationalCompletionPadicEquiv v).symm x)) =
      completionRingHom ℚ L v w ((rationalCompletionPadicEquiv v).symm x)
    exact τ.commutes _
  invFun τ := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x ↦ by
    have h : algebraMap (v.adicCompletion ℚ) (w.adicCompletion L) x =
        algebraMap ℚ_[completionPrime v] (w.adicCompletion L) (rationalCompletionPadicEquiv v x) := by
      change completionRingHom ℚ L v w x =
        completionRingHom ℚ L v w ((rationalCompletionPadicEquiv v).symm (rationalCompletionPadicEquiv v x))
      rw [ContinuousAlgEquiv.symm_apply_apply]
    rw [h]
    exact τ.commutes _
  left_inv τ := AlgEquiv.ext fun _ ↦ rfl
  right_inv τ := AlgEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ rfl

/-- The actual global decomposition group is the actual Qp-based completed Galois group. -/
def decompositionPadicFieldMulEquiv [Normal ℚ L] : decompositionGroup L w ≃*
    (w.adicCompletion L ≃ₐ[ℚ_[completionPrime v]] w.adicCompletion L) :=
  (decompositionFieldMulEquiv L v w).trans (padicCompletedFieldAutMulEquiv L v w)

/-- This group rebase preserves the named original action on every global field element. -/
theorem decompositionPadicFieldMulEquiv_algebraMap [Normal ℚ L]
    (σ : decompositionGroup L w) (x : L) :
    decompositionPadicFieldMulEquiv L v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/ℚ)) x) :=
  decompositionFieldHom_algebraMap L v w σ x

/-- The actual Qp-based completed extension is finite, transported through the proved
canonical scalar tower from the existing finite completed-rational-base extension. -/
theorem moduleFinite_padicNumberFieldCompletion :
    Module.Finite ℚ_[completionPrime v] (w.adicCompletion L) := by
  let := moduleFinite_numberFieldCompletion L v w
  exact Module.Finite.right (v.adicCompletion ℚ) ℚ_[completionPrime v] (w.adicCompletion L)

/-- Continuity of the actual Qp field map is the continuity of its two named factors. -/
theorem continuous_padicCompletionAlgebra :
    Continuous (algebraMap ℚ_[completionPrime v] (w.adicCompletion L)) := by
  change Continuous (fun x ↦ completionRingHom ℚ L v w ((rationalCompletionPadicEquiv v).symm x))
  exact (continuous_completionRingHom ℚ L v w).comp (rationalCompletionPadicEquiv v).symm.continuous

/-- The canonical Qp scalar action is continuous; no isometric normalized-base assertion is used. -/
theorem continuousSMul_padicNumberFieldCompletion :
    ContinuousSMul ℚ_[completionPrime v] (w.adicCompletion L) := by
  apply continuousSMul_of_algebraMap
  exact continuous_padicCompletionAlgebra L v w

scoped[GlobalDifferentTransportPadicCompletion] attribute [instance]
  GlobalDifferentTransport.moduleFinite_padicNumberFieldCompletion
  GlobalDifferentTransport.continuousSMul_padicNumberFieldCompletion

end GlobalDifferentTransport
