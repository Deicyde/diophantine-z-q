/-
Multiplication-etale construction: CotangentDerivationNaturality.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped TensorProduct

noncomputable section

namespace H101DirectFieldRoute

/-- The ordinary native tensor/Kaehler universal property, with all scalar
actions explicit: residue cotangent functionals are relative derivations. -/
def cotangentDualDerivationEquiv
    (R S κ : Type*) [CommRing R] [CommRing S] [CommRing κ]
    [Algebra R S] [Algebra S κ] [Algebra R κ] [IsScalarTower R S κ] :
    (κ ⊗[S] Ω[S⁄R] →ₗ[κ] κ) ≃ Derivation R S κ where
  toFun l := KaehlerDifferential.linearMapEquivDerivation R S (M := κ)
    ((l.restrictScalars S).comp (TensorProduct.mk S κ Ω[S⁄R] 1))
  invFun d := (TensorProduct.isBaseChange S Ω[S⁄R] κ).lift d.liftKaehlerDifferential
  left_inv l := by
    apply (TensorProduct.isBaseChange S Ω[S⁄R] κ).algHom_ext
    intro ω
    change (TensorProduct.isBaseChange S Ω[S⁄R] κ).lift
      ((KaehlerDifferential.linearMapEquivDerivation R S (M := κ)).symm
        (KaehlerDifferential.linearMapEquivDerivation R S (M := κ)
          ((l.restrictScalars S).comp (TensorProduct.mk S κ Ω[S⁄R] 1))))
      (TensorProduct.mk S κ Ω[S⁄R] 1 ω) = l (TensorProduct.mk S κ Ω[S⁄R] 1 ω)
    rw [IsBaseChange.lift_eq]
    exact LinearMap.congr_fun
      ((KaehlerDifferential.linearMapEquivDerivation R S (M := κ)).symm_apply_apply
        ((l.restrictScalars S).comp (TensorProduct.mk S κ Ω[S⁄R] 1))) ω
  right_inv d := by
    apply Derivation.ext
    intro a
    change (KaehlerDifferential.linearMapEquivDerivation R S (M := κ)
      (((TensorProduct.isBaseChange S Ω[S⁄R] κ).lift d.liftKaehlerDifferential).restrictScalars S
        ∘ₗ TensorProduct.mk S κ Ω[S⁄R] 1)) a = d a
    rw [KaehlerDifferential.linearMapEquivDerivation_apply_apply]
    change (TensorProduct.isBaseChange S Ω[S⁄R] κ).lift
      d.liftKaehlerDifferential
      (TensorProduct.mk S κ Ω[S⁄R] 1 (KaehlerDifferential.D R S a)) = d a
    rw [IsBaseChange.lift_eq, Derivation.liftKaehlerDifferential_comp_D]

@[simp]
theorem cotangentDualDerivationEquiv_apply_D
    (R S κ : Type*) [CommRing R] [CommRing S] [CommRing κ]
    [Algebra R S] [Algebra S κ] [Algebra R κ] [IsScalarTower R S κ]
    (l : κ ⊗[S] Ω[S⁄R] →ₗ[κ] κ) (a : S) :
    cotangentDualDerivationEquiv R S κ l a =
      l (1 ⊗ₜ[S] KaehlerDifferential.D R S a) := by
  change (KaehlerDifferential.linearMapEquivDerivation R S (M := κ)
    ((l.restrictScalars S).comp (TensorProduct.mk S κ Ω[S⁄R] 1))) a = _
  rw [KaehlerDifferential.linearMapEquivDerivation_apply_apply]
  rfl

section Tower

variable (R S T κ : Type*) [CommRing R] [CommRing S] [CommRing T] [Field κ]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable [Algebra T κ] [Algebra S κ] [Algebra R κ]
variable [IsScalarTower S T κ] [IsScalarTower R T κ] [IsScalarTower R S κ]

/-- The ACTUAL residue-base-change of the native relative differential map,
with its source tensor product cancelled through the actual S -> T -> κ tower. -/
def residueCotangentMap : κ ⊗[S] Ω[S⁄R] →ₗ[κ] κ ⊗[T] Ω[T⁄R] :=
  (KaehlerDifferential.mapBaseChange R S T).baseChange κ ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S T κ κ Ω[S⁄R]).symm.toLinearMap

@[simp]
theorem residueCotangentMap_one_tmul_D (a : S) :
    residueCotangentMap R S T κ (1 ⊗ₜ[S] KaehlerDifferential.D R S a) =
      1 ⊗ₜ[T] KaehlerDifferential.D R T (algebraMap S T a) := by
  have hcancel :
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S T κ κ Ω[S⁄R]).symm
        ((1 : κ) ⊗ₜ[S] KaehlerDifferential.D R S a) =
      (1 : κ) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] KaehlerDifferential.D R S a) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul
      S T κ (1 : κ) (KaehlerDifferential.D R S a)
  change (KaehlerDifferential.mapBaseChange R S T).baseChange κ
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S T κ κ Ω[S⁄R]).symm
      ((1 : κ) ⊗ₜ[S] KaehlerDifferential.D R S a)) = _
  rw [hcancel, LinearMap.baseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul R S T, one_smul,
    KaehlerDifferential.map_D R R S T]

/-- The concrete cotangent/derivation square COMMUTES by the native map's
value on the universal differentials. No square hypothesis is introduced. -/
theorem residueCotangentMap_dual_naturality
    (l : κ ⊗[T] Ω[T⁄R] →ₗ[κ] κ) :
    cotangentDualDerivationEquiv R S κ
      ((residueCotangentMap R S T κ).dualMap l) =
    (cotangentDualDerivationEquiv R T κ l).compAlgebraMap S := by
  apply Derivation.ext
  intro a
  rw [cotangentDualDerivationEquiv_apply_D,
    Derivation.compAlgebraMap_apply, cotangentDualDerivationEquiv_apply_D,
    LinearMap.dualMap_apply, residueCotangentMap_one_tmul_D]

/-- A bijection of the actual restriction map on derivations gives a bijection
of the actual residue cotangent map. For H101 the restriction hypothesis must
be derived from the actual origin-tangent calculation and its canonical
stalk/residue-field identifications; this lemma does not assume full stalk
bijectivity, Flat, or Etale. -/
theorem residueCotangentMap_bijective_of_derivationRestriction
    [FiniteDimensional κ (κ ⊗[S] Ω[S⁄R])]
    [FiniteDimensional κ (κ ⊗[T] Ω[T⁄R])]
    (h : Function.Bijective
      (fun d : Derivation R T κ => d.compAlgebraMap S)) :
    Function.Bijective (residueCotangentMap R S T κ) := by
  apply LinearMap.dualMap_bijective_iff.mp
  constructor
  · intro l₁ l₂ hdual
    apply (cotangentDualDerivationEquiv R T κ).injective
    apply h.1
    change (cotangentDualDerivationEquiv R T κ l₁).compAlgebraMap S =
      (cotangentDualDerivationEquiv R T κ l₂).compAlgebraMap S
    exact (residueCotangentMap_dual_naturality R S T κ l₁).symm.trans
      ((congrArg (cotangentDualDerivationEquiv R S κ) hdual).trans
        (residueCotangentMap_dual_naturality R S T κ l₂))
  · intro l
    obtain ⟨d, hd⟩ := h.2 (cotangentDualDerivationEquiv R S κ l)
    refine ⟨(cotangentDualDerivationEquiv R T κ).symm d,
      (cotangentDualDerivationEquiv R S κ).injective ?_⟩
    calc
      cotangentDualDerivationEquiv R S κ
          ((residueCotangentMap R S T κ).dualMap
            ((cotangentDualDerivationEquiv R T κ).symm d)) =
          (cotangentDualDerivationEquiv R T κ
            ((cotangentDualDerivationEquiv R T κ).symm d)).compAlgebraMap S :=
        residueCotangentMap_dual_naturality R S T κ _
      _ = d.compAlgebraMap S :=
        congrArg (fun d' : Derivation R T κ => d'.compAlgebraMap S)
          ((cotangentDualDerivationEquiv R T κ).apply_symm_apply d)
      _ = cotangentDualDerivationEquiv R S κ l := hd

end Tower

end H101DirectFieldRoute
