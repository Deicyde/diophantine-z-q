module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Finite group invariants and arbitrary scalar extension -/

@[expose] public section

namespace RC.ModelInvariants

open scoped BigOperators TensorProduct

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- Mathlib's orbit polynomial proves integrality without an invertibility hypothesis. -/
theorem fixedPoints_isIntegral [Finite G] :
    Algebra.IsIntegral (FixedPoints.subalgebra R S G) S :=
  Algebra.IsInvariant.isIntegral _ _ G

section Reynolds

variable [Fintype G]

/-- Averaging over the action using the inverse of the group order in the base ring.
The coefficients can be taken in the invariant algebra itself. -/
noncomputable def reynolds (G : Type*) [Group G] [Fintype G]
    [MulSemiringAction G S] [SMulCommClass G R S] (h : IsUnit (Fintype.card G : R)) :
    S →ₗ[FixedPoints.subalgebra R S G] FixedPoints.subalgebra R S G where
  toFun x := ⟨(↑h.unit⁻¹ : R) • ∑ g : G, g • x, fun g => by
    rw [smul_comm, Finset.smul_sum]
    simp only [smul_smul]
    exact congrArg ((↑h.unit⁻¹ : R) • ·)
      (Equiv.sum_comp (Equiv.mulLeft g) fun t : G => t • x)⟩
  map_add' x y := Subtype.ext (by simp [smul_add, Finset.sum_add_distrib])
  map_smul' a x := Subtype.ext (by
    change (↑h.unit⁻¹ : R) • (∑ g : G, g • (a • x)) =
      a • ((↑h.unit⁻¹ : R) • ∑ g : G, g • x)
    simp only [smul_comm _ a, ← Finset.smul_sum])

theorem reynolds_apply_coe (h : IsUnit (Fintype.card G : R)) (x : S) :
    ((reynolds (S := S) G h x : FixedPoints.subalgebra R S G) : S) =
      (↑h.unit⁻¹ : R) • ∑ g : G, g • x := rfl

theorem reynolds_fixed (h : IsUnit (Fintype.card G : R))
    (x : FixedPoints.subalgebra R S G) : reynolds (S := S) G h (x : S) = x := by
  apply Subtype.ext
  rw [reynolds_apply_coe]
  have hx (g : G) : g • (x : S) = x := x.property g
  simp only [hx, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, h.val_inv_mul, one_smul]

/-- The invariant algebra is an `R`-linear retract of the original algebra. -/
theorem reynolds_retract (h : IsUnit (Fintype.card G : R)) :
    (reynolds G h |>.restrictScalars R).comp
      (FixedPoints.subalgebra R S G).val.toLinearMap = LinearMap.id := by
  exact LinearMap.ext (reynolds_fixed h)

theorem fixedPoints_flat (h : IsUnit (Fintype.card G : R)) [Module.Flat R S] :
    Module.Flat R (FixedPoints.subalgebra R S G) :=
  Module.Flat.of_retract _ _ (reynolds_retract h)

end Reynolds

section BaseChange

variable (R' : Type*) [CommRing R'] [Algebra R R']

/-- The action on a scalar extension fixes the scalars and acts on the original algebra.
Mathlib puts the scalar factor first so that its algebra structure is inferred canonically. -/
noncomputable instance scalarExtensionAction : MulSemiringAction G (R' ⊗[R] S) where
  smul g x := Algebra.TensorProduct.map (AlgHom.id R' R')
    (MulSemiringAction.toAlgHom R S g) x
  one_smul x := by
    have he : MulSemiringAction.toAlgHom R S (1 : G) = AlgHom.id R S :=
      AlgHom.ext (one_smul G)
    change Algebra.TensorProduct.map _ _ x = x
    rw [he, Algebra.TensorProduct.map_id, AlgHom.id_apply]
  mul_smul g t x := by
    have he : MulSemiringAction.toAlgHom R S (g * t) =
        (MulSemiringAction.toAlgHom R S g).comp (MulSemiringAction.toAlgHom R S t) :=
      AlgHom.ext (mul_smul g t)
    change Algebra.TensorProduct.map _ _ x = Algebra.TensorProduct.map _ _
      (Algebra.TensorProduct.map _ _ x)
    rw [he, ← AlgHom.id_comp (AlgHom.id R' R'), Algebra.TensorProduct.map_comp]
    simp
  smul_zero g := map_zero (Algebra.TensorProduct.map (AlgHom.id R' R')
    (MulSemiringAction.toAlgHom R S g))
  smul_add g := map_add (Algebra.TensorProduct.map (AlgHom.id R' R')
    (MulSemiringAction.toAlgHom R S g))
  smul_one g := map_one (Algebra.TensorProduct.map (AlgHom.id R' R')
    (MulSemiringAction.toAlgHom R S g))
  smul_mul g := map_mul (Algebra.TensorProduct.map (AlgHom.id R' R')
    (MulSemiringAction.toAlgHom R S g))

instance : SMulCommClass G R' (R' ⊗[R] S) where
  smul_comm g a x := (Algebra.TensorProduct.map (AlgHom.id R' R')
    (MulSemiringAction.toAlgHom R S g)).toLinearMap.map_smul a x

theorem scalarExtension_smul_tmul (g : G) (a : R') (x : S) :
    g • (a ⊗ₜ[R] x) = a ⊗ₜ[R] (g • x) := rfl

/-- The canonical map from the tensor product of invariants to the invariants of the tensor
product. Its formula is `a ⊗ x ↦ a ⊗ x` through the invariant subalgebra inclusions. -/
noncomputable def fixedPointsBaseChangeHom :
    (R' ⊗[R] FixedPoints.subalgebra R S G) →ₐ[R']
      FixedPoints.subalgebra R' (R' ⊗[R] S) G :=
  (Algebra.TensorProduct.map (AlgHom.id R' R') (FixedPoints.subalgebra R S G).val).codRestrict _
    (fun x g => by
      refine TensorProduct.inductionOn x ?_ ?_
      · intro a x
        simp [scalarExtension_smul_tmul, x.property g]
      · intro x y hx hy
        simp [hx, hy])

variable {R'}

theorem fixedPointsBaseChangeHom_tmul (a : R') (x : FixedPoints.subalgebra R S G) :
    (fixedPointsBaseChangeHom (G := G) (S := S) R' (a ⊗ₜ[R] x) : R' ⊗[R] S) =
      a ⊗ₜ[R] (x : S) := rfl

variable (R') [Fintype G]

/-- A finite group of invertible order has invariants commuting with arbitrary base change. -/
noncomputable def fixedPointsBaseChange (h : IsUnit (Fintype.card G : R)) :
    (R' ⊗[R] FixedPoints.subalgebra R S G) ≃ₐ[R']
      FixedPoints.subalgebra R' (R' ⊗[R] S) G := by
  let inc := (FixedPoints.subalgebra R S G).val.toLinearMap
  let rho := (reynolds (S := S) G h).restrictScalars R
  have hsplit : (rho.baseChange R').comp (inc.baseChange R') = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, reynolds_retract h, LinearMap.baseChange_id]
  have hcoe (x : R' ⊗[R] FixedPoints.subalgebra R S G) :
      (fixedPointsBaseChangeHom (G := G) (S := S) R' x : R' ⊗[R] S) = inc.baseChange R' x := rfl
  have haverage : inc.comp rho = (↑h.unit⁻¹ : R) •
      ∑ g : G, (MulSemiringAction.toAlgHom R S g).toLinearMap := by
    ext x
    simp [inc, rho, reynolds_apply_coe]
  refine AlgEquiv.ofBijective (fixedPointsBaseChangeHom (G := G) (S := S) R') ⟨?_, ?_⟩
  · intro x y he
    have he' := congrArg (rho.baseChange R') (congrArg Subtype.val he)
    rw [hcoe, hcoe, ← LinearMap.comp_apply, ← LinearMap.comp_apply, hsplit] at he'
    exact he'
  · intro x
    refine ⟨rho.baseChange R' x, Subtype.ext ?_⟩
    rw [hcoe, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, haverage]
    change LinearMap.baseChangeHom R R' S S _ (x : R' ⊗[R] S) = (x : R' ⊗[R] S)
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.baseChangeHom_apply]
    have hact (g : G) :
        ((MulSemiringAction.toAlgHom R S g).toLinearMap.baseChange R') (x : R' ⊗[R] S) =
          g • (x : R' ⊗[R] S) := rfl
    have hx (g : G) : g • (x : R' ⊗[R] S) = x := x.property g
    simp only [hact, hx, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul R, smul_smul, h.val_inv_mul, one_smul]

theorem fixedPointsBaseChange_tmul (h : IsUnit (Fintype.card G : R)) (a : R')
    (x : FixedPoints.subalgebra R S G) :
    (fixedPointsBaseChange (S := S) R' h (a ⊗ₜ[R] x) : R' ⊗[R] S) = a ⊗ₜ[R] (x : S) := rfl

end BaseChange

#print axioms fixedPoints_isIntegral
#print axioms reynolds
#print axioms scalarExtensionAction
#print axioms fixedPointsBaseChangeHom
#print axioms fixedPointsBaseChange
#print axioms reynolds_apply_coe
#print axioms reynolds_fixed
#print axioms reynolds_retract
#print axioms fixedPoints_flat
#print axioms scalarExtension_smul_tmul
#print axioms fixedPointsBaseChangeHom_tmul
#print axioms fixedPointsBaseChange_tmul

end RC.ModelInvariants
