import ActualFiniteLevelActionV003
import SchemePointFieldV002
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The division field defined by the original torsion action

A common field is built from the actual point fields. The division field
is the fixed field of the kernel of the original action, rather than a
chosen representation model. The finite-level results in this module
have the explicitly local finite-torsion instance; geometry supplies that
instance separately.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

namespace ActualDivisionField
open ActualFiniteLevel
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma point_fixed_of_field (A : PkgI3.AbVar K) (L : FiniteGaloisIntermediateField K Ω)
    (x : A.Pt Ω) (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ A.X)
    (hy : Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫ y.left = x.left)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ L.fixingSubgroup) : A.galAct σ x = x := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left = x.left
  rw [← hy, ← Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom L.toIntermediateField.val.toRingHom ≫
      CommRingCat.ofHom σ.toRingHom = CommRingCat.ofHom L.toIntermediateField.val.toRingHom := by
    ext a
    exact (IntermediateField.mem_fixingSubgroup_iff L.toIntermediateField σ).mp hσ a a.2
  rw [he]

lemma exists_common_field [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    ∃ L : FiniteGaloisIntermediateField K Ω, L.fixingSubgroup ≤ (action (Ω := Ω) A m).ker := by
  classical
  letI := Fintype.ofFinite (torsionSubgroup A Ω m)
  choose L y hy using fun x : torsionSubgroup A Ω m =>
    SchemePointField.exists_finiteGalois_point A.X x.1
  let E : FiniteGaloisIntermediateField K Ω := Finset.univ.sup L
  refine ⟨E, ?_⟩
  intro σ hσ
  apply (mem_action_ker A m σ).mpr
  intro x hx
  let z : torsionSubgroup A Ω m := ⟨x, hx⟩
  have hz : L z ≤ E := Finset.le_sup (Finset.mem_univ z)
  exact point_fixed_of_field A (L z) x (y z) (hy z) σ
    ((L z).toIntermediateField.fixingSubgroup_le hz hσ)

def divisionField (A : PkgI3.AbVar K) (m : ℕ) : IntermediateField K Ω :=
  IntermediateField.fixedField (action (Ω := Ω) A m).ker

instance divisionField_isGalois [IsGalois K Ω] (A : PkgI3.AbVar K) (m : ℕ) :
    IsGalois K (divisionField (Ω := Ω) A m) := by
  change IsGalois K (IntermediateField.fixedField (action (Ω := Ω) A m).ker)
  infer_instance

lemma kernel_isOpen [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    IsOpen ((action (Ω := Ω) A m).ker : Set (Ω ≃ₐ[K] Ω)) := by
  obtain ⟨L, hL⟩ := exists_common_field (Ω := Ω) A m
  exact Subgroup.isOpen_mono hL L.toIntermediateField.fixingSubgroup_isOpen

lemma kernel_isClosed [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    IsClosed ((action (Ω := Ω) A m).ker : Set (Ω ≃ₐ[K] Ω)) :=
  Subgroup.isClosed_of_isOpen _ (kernel_isOpen A m)

lemma fixingSubgroup_eq_kernel [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    (divisionField (Ω := Ω) A m).fixingSubgroup = (action (Ω := Ω) A m).ker := by
  exact InfiniteGalois.fixingSubgroup_fixedField
    (⟨(action A m).ker, kernel_isClosed A m⟩ : ClosedSubgroup (Ω ≃ₐ[K] Ω))

instance divisionField_finiteDimensional [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    FiniteDimensional K (divisionField (Ω := Ω) A m) := by
  apply (InfiniteGalois.isOpen_iff_finite (divisionField A m)).mp
  rw [fixingSubgroup_eq_kernel]
  exact kernel_isOpen A m

def finiteDivisionField [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    FiniteGaloisIntermediateField K Ω := .mk (divisionField A m)

def restriction [IsGalois K Ω] (A : PkgI3.AbVar K) (m : ℕ) :
    (Ω ≃ₐ[K] Ω) →* (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m) :=
  AlgEquiv.restrictNormalHom (divisionField A m)

lemma restriction_surjective [IsGalois K Ω] (A : PkgI3.AbVar K) (m : ℕ) :
    Function.Surjective (restriction (Ω := Ω) A m) := AlgEquiv.restrictNormalHom_surjective Ω

lemma restriction_continuous [IsGalois K Ω] (A : PkgI3.AbVar K) (m : ℕ) :
    Continuous (restriction (Ω := Ω) A m) := InfiniteGalois.restrictNormalHom_continuous _

lemma restriction_ker [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    (restriction (Ω := Ω) A m).ker = (action (Ω := Ω) A m).ker :=
  (divisionField A m).restrictNormalHom_ker.trans (fixingSubgroup_eq_kernel A m)

def factoredAction [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m) →*
      MulAut (torsionSubgroup A Ω m) :=
  (restriction A m).liftOfSurjective (restriction_surjective A m)
    ⟨action A m, (restriction_ker A m).le⟩

lemma factoredAction_restriction [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] (σ : Ω ≃ₐ[K] Ω) :
    factoredAction A m (restriction A m σ) = action A m σ := by
  exact (restriction A m).liftOfRightInverse_comp_apply _ _ _ σ

lemma factoredAction_comp [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    (factoredAction (Ω := Ω) A m).comp (restriction A m) = action A m :=
  MonoidHom.ext (factoredAction_restriction (Ω := Ω) A m)

lemma factoredAction_injective [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    Function.Injective (factoredAction (Ω := Ω) A m) := by
  intro σ τ h
  obtain ⟨s, rfl⟩ := restriction_surjective A m σ
  obtain ⟨t, rfl⟩ := restriction_surjective A m τ
  rw [factoredAction_restriction, factoredAction_restriction] at h
  have hk : s⁻¹ * t ∈ (action A m).ker := by
    change action A m (s⁻¹ * t) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hr : s⁻¹ * t ∈ (restriction A m).ker := by
    rw [restriction_ker]
    exact hk
  change restriction A m (s⁻¹ * t) = 1 at hr
  rw [map_mul, map_inv, inv_mul_eq_one] at hr
  exact hr

end ActualDivisionField
