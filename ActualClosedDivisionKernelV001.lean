import ActualDivisionFieldV004

/-!
# The original torsion-action kernel is closed without a finite-point premise

Every individual actual geometric point has an open stabilizer, because
its genuine finite point field has an open fixing group. Intersecting
these closed stabilizers proves the original kernel closed even before
geometric finiteness is used. The canonical division field therefore has
exactly the original action kernel, without a supplied factoring model.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

namespace ActualClosedDivisionKernel
open ActualFiniteLevel ActualDivisionField
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

def pointStabilizer (A : PkgI3.AbVar K) (x : A.Pt Ω) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | A.galAct σ x = x}
  one_mem' := galAct_one A x
  mul_mem' := by
    intro σ τ hσ hτ
    change A.galAct (σ * τ) x = x
    rw [galAct_mul, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    change A.galAct σ⁻¹ x = x
    have h := congrArg (A.galAct σ⁻¹) hσ
    rw [← galAct_mul, inv_mul_cancel, galAct_one] at h
    exact h.symm

lemma pointStabilizer_isOpen [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (x : A.Pt Ω) :
    IsOpen (pointStabilizer A x : Set (Ω ≃ₐ[K] Ω)) := by
  obtain ⟨L, y, hy⟩ := SchemePointField.exists_finiteGalois_point A.X x
  have hL : L.fixingSubgroup ≤ pointStabilizer A x := by
    intro σ hσ
    exact point_fixed_of_field A L x y hy σ hσ
  exact Subgroup.isOpen_mono hL L.toIntermediateField.fixingSubgroup_isOpen

lemma pointStabilizer_isClosed [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (x : A.Pt Ω) :
    IsClosed (pointStabilizer A x : Set (Ω ≃ₐ[K] Ω)) :=
  Subgroup.isClosed_of_isOpen _ (pointStabilizer_isOpen A x)

lemma kernel_eq_stabilizer_intersection (A : PkgI3.AbVar K) (m : ℕ) :
    (action (Ω := Ω) A m).ker = ⨅ x : torsionSubgroup A Ω m, pointStabilizer A x.1 := by
  apply Subgroup.ext
  intro σ
  rw [Subgroup.mem_iInf]
  constructor
  · intro h x
    exact (mem_action_ker A m σ).mp h x.1 x.2
  · intro h
    apply (mem_action_ker A m σ).mpr
    intro x hx
    exact h ⟨x, hx⟩

lemma kernel_closed [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) :
    IsClosed ((action (Ω := Ω) A m).ker : Set (Ω ≃ₐ[K] Ω)) := by
  rw [kernel_eq_stabilizer_intersection, Subgroup.coe_iInf]
  exact isClosed_iInter (fun x => pointStabilizer_isClosed A x.1)

lemma fixingSubgroup_eq_original_kernel [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) :
    (divisionField (Ω := Ω) A m).fixingSubgroup = (action (Ω := Ω) A m).ker :=
  InfiniteGalois.fixingSubgroup_fixedField
    (⟨(action A m).ker, kernel_closed A m⟩ : ClosedSubgroup (Ω ≃ₐ[K] Ω))

lemma restriction_kernel_exact [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) :
    (restriction (Ω := Ω) A m).ker = (action (Ω := Ω) A m).ker :=
  (divisionField A m).restrictNormalHom_ker.trans (fixingSubgroup_eq_original_kernel A m)

def canonicalAction [CharZero K] [IsAlgClosure K Ω] (A : PkgI3.AbVar K) (m : ℕ) :
    (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m) →*
      MulAut (torsionSubgroup A Ω m) :=
  (restriction A m).liftOfSurjective (restriction_surjective A m)
    ⟨action A m, (restriction_kernel_exact A m).le⟩

lemma canonicalAction_restriction [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) (σ : Ω ≃ₐ[K] Ω) :
    canonicalAction A m (restriction A m σ) = action A m σ :=
  (restriction A m).liftOfRightInverse_comp_apply _ _ _ σ

lemma canonicalAction_agrees_finite [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    canonicalAction (Ω := Ω) A m = factoredAction (Ω := Ω) A m := by
  apply MonoidHom.ext
  intro τ
  obtain ⟨σ, rfl⟩ := restriction_surjective A m τ
  rw [canonicalAction_restriction, factoredAction_restriction]

end ActualClosedDivisionKernel
