import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.AlgebraicGeometry.Properties
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.GlobalSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Pullback
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import ZInQKernel.Contrib.OneProof.SGA3IdComp
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Geometrically.Smooth
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Pullback
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR

/-!
# Restriction of line bundles on smooth DVR schemes

A line bundle on a smooth integral DVR scheme is trivial if its generic
restriction and its pullback to a section of a smooth geometrically integral
projection are both trivial. A generic frame determines the exponent of the
uniformizer on each affine chart where the parameter is prime. The section
normalizes these exponents, and the resulting local frames glue.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace Topology Scheme.Modules
open MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

namespace NeronDVR

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
  {π : A} [IsLocalization.Away π B]

/-- A unit in the localization away from a prime element is a power of that element
times a unit of the original ring. -/
theorem exists_unit_mul_selfZPow_of_isUnit {b : B} (hb : IsUnit b) (hπ : Prime π) :
    ∃ (n : ℤ) (u : Aˣ), b = algebraMap A B (u : A) * selfZPow π B n := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj π b
  have hau : IsUnit (algebraMap A B a) := ha ▸ hb.mul (IsLocalization.Away.algebraMap_pow_isUnit π m)
  obtain ⟨N, hN⟩ := (IsLocalization.Away.algebraMap_isUnit_iff π).mp hau
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow hπ N).mp hN
  obtain ⟨u, hu⟩ := hk.symm
  refine ⟨(k : ℤ) - m, u, ?_⟩
  apply ((IsLocalization.Away.algebraMap_pow_isUnit π m).mul_left_inj).mp
  rw [ha, mul_assoc, ← selfZPow_natCast π B m,
    ← selfZPow_add, sub_add_cancel, selfZPow_natCast,
    ← map_pow, ← map_mul, mul_comm (u : A), hu]

/-- The exponent of a prime element in a unit of its localization is unique. -/
theorem selfZPow_exponent_eq_of_unit_mul_eq (hnz : π ≠ 0) (hnu : ¬ IsUnit π)
    (u v : Aˣ) (m n : ℤ)
    (h : algebraMap A B (u : A) * selfZPow π B m =
      algebraMap A B (v : A) * selfZPow π B n) : m = n := by
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors hnz)
  have eq_of_ge (u v : Aˣ) {m n : ℤ} (hle : n ≤ m)
      (h : algebraMap A B (u : A) * selfZPow π B m =
        algebraMap A B (v : A) * selfZPow π B n) : m = n := by
    have h' := congrArg (fun b : B => b * selfZPow π B (-n)) h
    change (_ * _) * _ = (_ * _) * _ at h'
    rw [mul_assoc, mul_assoc, ← selfZPow_add,
      ← selfZPow_add, add_neg_cancel, selfZPow_zero,
      mul_one, ← sub_eq_add_neg, selfZPow_of_nonneg _ _ (sub_nonneg.mpr hle),
      ← map_pow, ← map_mul] at h'
    have hunit : IsUnit (π ^ (m - n).natAbs) := by
      have he := hinj h'
      exact isUnit_of_mul_isUnit_right (he.symm ▸ v.isUnit)
    have hzero : (m - n).natAbs = 0 := by
      by_contra hne
      exact hnu ((isUnit_pow_iff hne).mp hunit)
    exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hzero)
  rcases le_total n m with hle | hle
  · exact eq_of_ge u v hle h
  · exact (eq_of_ge v u hle h.symm).symm

/-- The localization away from a prime element gives each unit a unique integer exponent
when factored into a power of the prime and a unit of the original ring. -/
theorem existsUnique_unit_mul_selfZPow_of_isUnit {b : B} (hb : IsUnit b) (hπ : Prime π) :
    ∃! n : ℤ, ∃ u : Aˣ, b = algebraMap A B (u : A) * selfZPow π B n := by
  obtain ⟨n, u, hu⟩ := exists_unit_mul_selfZPow_of_isUnit hb hπ
  refine ⟨n, ⟨u, hu⟩, ?_⟩
  rintro m ⟨v, hv⟩
  exact selfZPow_exponent_eq_of_unit_mul_eq hπ.ne_zero hπ.not_isUnit v u m n (hv.symm.trans hu)

omit [IsDomain A] in
/-- Integer powers of the element being inverted commute with maps of localization squares. -/
theorem map_selfZPow {C D : Type*} [CommRing C] [CommRing D] [Algebra C D]
    (f : A →+* C) [IsLocalization.Away (f π) D] (g : B →+* D)
    (hg : g (algebraMap A B π) = algebraMap C D (f π)) (n : ℤ) :
    g (selfZPow π B n) = selfZPow (f π) D n := by
  by_cases hn : 0 ≤ n
  · rw [selfZPow_of_nonneg _ _ hn, selfZPow_of_nonneg _ _ hn, map_pow, hg]
  · have hpos : 0 ≤ -n := neg_nonneg.mpr (le_of_not_ge hn)
    have heq : g (selfZPow π B (-n)) = selfZPow (f π) D (-n) := by
      rw [selfZPow_of_nonneg _ _ hpos, selfZPow_of_nonneg _ _ hpos, map_pow, hg]
    have hu : IsUnit (selfZPow (f π) D (-n)) :=
      IsUnit.of_mul_eq_one _ (selfZPow_mul_neg (f π) D (-n))
    apply hu.mul_left_inj.mp
    rw [← heq, ← map_mul, selfZPow_mul_neg, map_one, heq, selfZPow_mul_neg]

end NeronDVR

namespace NeronDVR
namespace GenericFrame

variable {X : Scheme.{0}} (π : Γ(X, ⊤))

/-- The global uniformizer on this chart. -/
abbrev parameter (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op π

private theorem basicOpen_parameter (U : X.Opens) :
    X.basicOpen (parameter π U) = U ⊓ X.basicOpen π :=
  X.basicOpen_res π _

/-- The integer power of the uniformizer on the generic part of the chart. -/
abbrev power (U : X.Opens) (hU : IsAffineOpen U) (n : ℤ) :
    Γ(X, U ⊓ X.basicOpen π) :=
  let : Algebra Γ(X, U) Γ(X, U ⊓ X.basicOpen π) :=
    (X.presheaf.map (homOfLE inf_le_left : U ⊓ X.basicOpen π ⟶ U).op).hom.toAlgebra
  let : IsLocalization.Away (parameter π U) Γ(X, U ⊓ X.basicOpen π) :=
    hU.isLocalization_of_eq_basicOpen (parameter π U) (homOfLE inf_le_left)
      (basicOpen_parameter π U).symm
  selfZPow (parameter π U) Γ(X, U ⊓ X.basicOpen π) n

theorem power_restrict {U V : X.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ) :
    X.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen π) h)).op (power π U hU n) =
      power π V hV n := by
  let DU := U ⊓ X.basicOpen π
  let DV := V ⊓ X.basicOpen π
  let α : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom
  let β : Γ(X, DU) →+* Γ(X, DV) :=
    (X.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen π) h)).op).hom
  let : Algebra Γ(X, U) Γ(X, DU) :=
    (X.presheaf.map (homOfLE inf_le_left : DU ⟶ U).op).hom.toAlgebra
  let : Algebra Γ(X, V) Γ(X, DV) :=
    (X.presheaf.map (homOfLE inf_le_left : DV ⟶ V).op).hom.toAlgebra
  let : IsLocalization.Away (parameter π U) Γ(X, DU) :=
    hU.isLocalization_of_eq_basicOpen (parameter π U) (homOfLE inf_le_left)
      (basicOpen_parameter π U).symm
  let : IsLocalization.Away (parameter π V) Γ(X, DV) :=
    hV.isLocalization_of_eq_basicOpen (parameter π V) (homOfLE inf_le_left)
      (basicOpen_parameter π V).symm
  have hα : α (parameter π U) = parameter π V := by
    change X.presheaf.map (homOfLE h).op (parameter π U) = parameter π V
    exact Scheme.presheaf_map_map_apply (X := X) (homOfLE le_top) (homOfLE h) π
  have : IsLocalization.Away (α (parameter π U)) Γ(X, DV) := hα.symm ▸ inferInstance
  have hβ : β (algebraMap Γ(X, U) Γ(X, DU) (parameter π U)) =
      algebraMap Γ(X, V) Γ(X, DV) (α (parameter π U)) := by
    change (X.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen π) h)).op)
        (X.presheaf.map (homOfLE inf_le_left : DU ⟶ U).op (parameter π U)) =
      (X.presheaf.map (homOfLE inf_le_left : DV ⟶ V).op)
        (X.presheaf.map (homOfLE h).op (parameter π U))
    exact (Scheme.presheaf_map_map_apply (X := X)
      (homOfLE inf_le_left : DU ⟶ U)
      (homOfLE (inf_le_inf_right (X.basicOpen π) h) : DV ⟶ DU) (parameter π U)).trans
      (Scheme.presheaf_map_map_apply (X := X) (homOfLE h)
        (homOfLE inf_le_left : DV ⟶ V) (parameter π U)).symm
  exact (map_selfZPow α β hβ n).trans (by congr 1)

variable {M : X.Modules} (s : Γ(M, X.basicOpen π))

/-- A chart has a specified exponent if the generic frame differs from its chosen frame
by that power times a unit of the chart. -/
def HasExponent {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(M, U)) (n : ℤ) : Prop :=
  ∃ u : Γ(X, U)ˣ,
    M.presheaf.map (homOfLE inf_le_right : U ⊓ X.basicOpen π ⟶ X.basicOpen π).op s =
      (X.presheaf.map (homOfLE inf_le_left : U ⊓ X.basicOpen π ⟶ U).op u.val * power π U hU n) •
        M.presheaf.map (homOfLE inf_le_left : U ⊓ X.basicOpen π ⟶ U).op e

/-- In a local frame, the generic frame is a unit times a power of the uniformizer. -/
theorem exists_unit_mul_power [IsIntegral X]
    {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U)
    (hπ : Prime (parameter π U)) {e : Γ(M, U)} (he : IsFreeGenerator e)
    (hs : IsFreeGenerator s) :
    ∃ n : ℤ, HasExponent π s hU e n := by
  let V := U ⊓ X.basicOpen π
  let : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE inf_le_left : V ⟶ U).op).hom.toAlgebra
  let : IsLocalization.Away (parameter π U) Γ(X, V) :=
    hU.isLocalization_of_eq_basicOpen (parameter π U) (homOfLE inf_le_left)
      (basicOpen_parameter π U).symm
  obtain ⟨u, hu⟩ := (he.map (inf_le_left : V ≤ U)).exists_unit_smul_eq
    (hs.map (inf_le_right : V ≤ X.basicOpen π))
  obtain ⟨n, v, hv⟩ := exists_unit_mul_selfZPow_of_isUnit u.isUnit hπ
  exact ⟨n, v, hu.trans (by rw [hv]; rfl)⟩

/-- The exponent zero means the generic frame extends over this chart. -/
theorem exists_extension_of_exponent_zero
    {U : X.Opens} (hU : IsAffineOpen U) {e : Γ(M, U)} (he : IsFreeGenerator e)
    (hu : HasExponent π s hU e 0) :
    ∃ t : Γ(M, U), IsFreeGenerator t ∧
      M.presheaf.map (homOfLE inf_le_left : U ⊓ X.basicOpen π ⟶ U).op t =
        M.presheaf.map (homOfLE inf_le_right : U ⊓ X.basicOpen π ⟶ X.basicOpen π).op s := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨u.val • e, he.units_smul u, ?_⟩
  rw [map_smul, hu]
  simp [power]

theorem hasExponent_restrict {U V : X.Opens} (h : V ≤ U)
    {hU : IsAffineOpen U} (hV : IsAffineOpen V) {e : Γ(M, U)} {n : ℤ}
    (hn : HasExponent π s hU e n) :
    HasExponent π s hV (M.presheaf.map (homOfLE h).op e) n := by
  obtain ⟨u, hu⟩ := hn
  let α : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom
  refine ⟨Units.map α.toMonoidHom u, ?_⟩
  have hh := congrArg (M.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen π) h)).op) hu
  simp only [map_smul, map_mul, power_restrict π h hU hV] at hh
  change _ = (X.presheaf.map (homOfLE inf_le_left : V ⊓ X.basicOpen π ⟶ V).op
      (X.presheaf.map (homOfLE h).op u.val) * power π V hV n) • _
  rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE,
    Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at hh
  rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE]
  have hmul :
      X.presheaf.map (homOfLE (inf_le_inf_right (X.basicOpen π) h)).op
        (X.presheaf.map (homOfLE inf_le_left : U ⊓ X.basicOpen π ⟶ U).op u.val) =
      X.presheaf.map (homOfLE inf_le_left : V ⊓ X.basicOpen π ⟶ V).op
        (X.presheaf.map (homOfLE h).op u.val) := by
    exact (Scheme.presheaf_map_map_apply (X := X)
      (homOfLE inf_le_left : U ⊓ X.basicOpen π ⟶ U)
      (homOfLE (inf_le_inf_right (X.basicOpen π) h)) u.val).trans
      (Scheme.presheaf_map_map_apply (X := X) (homOfLE h)
        (homOfLE inf_le_left : V ⊓ X.basicOpen π ⟶ V) u.val).symm
  rwa [hmul] at hh

set_option backward.isDefEq.respectTransparency false in
theorem hasExponent_unique [IsIntegral X] {U : X.Opens} [Nonempty U]
    {hU : IsAffineOpen U} (hπ0 : parameter π U ≠ 0) (hπu : ¬ IsUnit (parameter π U))
    {e e' : Γ(M, U)} (he : IsFreeGenerator e) (he' : IsFreeGenerator e')
    {n m : ℤ} (hn : HasExponent π s hU e n) (hm : HasExponent π s hU e' m) : n = m := by
  let V := U ⊓ X.basicOpen π
  let : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE inf_le_left : V ⟶ U).op).hom.toAlgebra
  let : IsLocalization.Away (parameter π U) Γ(X, V) :=
    hU.isLocalization_of_eq_basicOpen (parameter π U) (homOfLE inf_le_left)
      (basicOpen_parameter π U).symm
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, hv⟩ := hm
  obtain ⟨w, hw⟩ := he.exists_unit_smul_eq he'
  rw [hw, map_smul, smul_smul] at hv
  have hab := (he.map (inf_le_left : V ≤ U)).smul_left_injective (hu.symm.trans hv)
  let r := X.presheaf.map (homOfLE inf_le_left : V ⟶ U).op
  have hEq : r u.val * power π U hU n = r (v * w).val * power π U hU m := calc
    _ = r v.val * power π U hU m * r w.val := hab
    _ = r v.val * r w.val * power π U hU m := mul_right_comm _ _ _
    _ = _ := by rw [Units.val_mul, map_mul]
  exact selfZPow_exponent_eq_of_unit_mul_eq (B := Γ(X, V)) hπ0 hπu u (v * w) n m hEq

end GenericFrame
end NeronDVR

namespace NeronDVR
namespace GenericFrame

variable {X : Scheme.{0}} [IsIntegral X] {M : X.Modules}

theorem restriction_injective_of_isFreeGenerator {U V : X.Opens} (h : V ≤ U)
    [Nonempty V] {e : Γ(M, U)} (he : IsFreeGenerator e) :
    Function.Injective (M.presheaf.map (homOfLE h).op) := by
  intro a b hab
  have h' := congrArg (he.map h).coeff hab
  rw [he.coeff_map, he.coeff_map] at h'
  have hc := map_injective_of_isIntegral X (homOfLE h) h'
  rw [← he.coeff_smul a, ← he.coeff_smul b, hc]

/-- Free local extensions of a frame over a dense open glue to a global free extension. -/
theorem exists_isFreeGenerator_of_locally_extends (D : X.Opens) (hD : (D : Set X).Nonempty)
    (s : Γ(M, D))
    (hloc : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ e : Γ(M, U), IsFreeGenerator e ∧
      M.presheaf.map (homOfLE inf_le_left : U ⊓ D ⟶ U).op e =
        M.presheaf.map (homOfLE inf_le_right : U ⊓ D ⟶ D).op s) :
    ∃ e : Γ(M, ⊤), IsFreeGenerator e ∧
      M.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op e = s := by
  classical
  choose U hU e he hs using hloc
  let F : TopCat.Sheaf AddCommGrpCat.{0} X := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, U x := fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 U e := by
    intro i j
    let V := U i ⊓ U j
    change M.presheaf.map (homOfLE inf_le_left : V ⟶ U i).op (e i) =
      M.presheaf.map (homOfLE inf_le_right : V ⟶ U j).op (e j)
    by_cases hV : (V : Set X).Nonempty
    · let W := V ⊓ D
      have hW : (W : Set X).Nonempty :=
        nonempty_preirreducible_inter V.isOpen D.isOpen hV hD
      have : Nonempty W := hW.to_subtype
      apply restriction_injective_of_isFreeGenerator (inf_le_left : W ≤ V)
        ((he i).map (inf_le_left : V ≤ U i))
      have hi : W ≤ U i ⊓ D :=
        le_inf (inf_le_left.trans inf_le_left) inf_le_right
      have hj : W ≤ U j ⊓ D :=
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have hi' := congrArg (M.presheaf.map (homOfLE hi).op) (hs i)
      have hj' := congrArg (M.presheaf.map (homOfLE hj).op) (hs j)
      simp only [presheaf_map_homOfLE_map_homOfLE] at hi' hj' ⊢
      exact hi'.trans hj'.symm
    · have hbot : V = ⊥ := eq_bot_iff.mpr fun z hz => (hV ⟨z, hz⟩).elim
      have : Subsingleton Γ(M, V) := AddCommGrpCat.subsingleton_of_isZero
        (TopCat.Sheaf.isTerminalOfEqEmpty F hbot).isZero
      exact Subsingleton.elim _ _
  obtain ⟨g, hg₀, -⟩ := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover e hcompat
  change Γ(M, ⊤) at g
  have hg (i : X) : M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op g = e i := hg₀ i
  refine ⟨g, ?_, ?_⟩
  · let cover : Sieve (⊤ : X.Opens) :=
      { arrows := fun V _ => ∃ i, V ≤ U i
        downward_closed := fun ⟨i, hi⟩ f => ⟨i, (leOfHom f).trans hi⟩ }
    apply isFreeGenerator_of_mem g (coveringSieve := cover)
    · intro x _
      exact ⟨U x, homOfLE le_top, ⟨x, le_rfl⟩, hU x⟩
    · intro V f hf
      obtain ⟨i, hi⟩ := hf
      change IsFreeGenerator (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op g)
      rw [← presheaf_map_homOfLE_map_homOfLE (le_top : U i ≤ ⊤) hi, hg]
      exact (he i).map hi
  · let C (i : X) := U i ⊓ D
    have hCD (i : X) : C i ≤ D := inf_le_right
    let sf (i : X) : Γ(M, C i) := M.presheaf.map (homOfLE (hCD i)).op s
    have hC : D ≤ ⨆ i, C i := fun x hx =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x, hx⟩
    have hc : TopCat.Presheaf.IsCompatible F.1 C sf := by
      intro i j
      change M.presheaf.map (homOfLE inf_le_left : C i ⊓ C j ⟶ C i).op (sf i) =
        M.presheaf.map (homOfLE inf_le_right : C i ⊓ C j ⟶ C j).op (sf j)
      simp only [sf, presheaf_map_homOfLE_map_homOfLE]
    obtain ⟨a, -, ha⟩ := F.existsUnique_gluing' C D (fun i => homOfLE (hCD i)) hC sf hc
    change Γ(M, D) at a
    have hga : M.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op g = a := by
      refine ha _ ?_
      intro i
      change M.presheaf.map (homOfLE (hCD i)).op
        (M.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op g) = _
      rw [presheaf_map_homOfLE_map_homOfLE,
        ← presheaf_map_homOfLE_map_homOfLE (le_top : U i ≤ ⊤) (inf_le_left : C i ≤ U i), hg]
      exact hs i
    exact hga.trans (ha s fun _ => rfl).symm

end GenericFrame
end NeronDVR

namespace NeronDVR
namespace GenericFrame

variable {X Y : Scheme.{0}} (π : Γ(X, ⊤)) (f : Y ⟶ X)

private theorem genericPreimage_le :
    Y.basicOpen (f.appTop π) ≤ f ⁻¹ᵁ X.basicOpen π :=
  (f.preimage_basicOpen_top π).symm.le

private theorem generic_le_preimage {U : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) :
    V ⊓ Y.basicOpen (f.appTop π) ≤ f ⁻¹ᵁ (U ⊓ X.basicOpen π) := by
  intro y hy
  exact ⟨h hy.1, genericPreimage_le π f hy.2⟩

private lemma appLE_map_apply {U : X.Opens} {V W : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (hWV : W ≤ V) (a : Γ(X, U)) :
    Y.presheaf.map (homOfLE hWV).op (f.appLE U V h a) = f.appLE U W (hWV.trans h) a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private lemma map_appLE_apply {U U' : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (hUU' : U ≤ U') (a : Γ(X, U')) :
    f.appLE U V h (X.presheaf.map (homOfLE hUU').op a) =
      f.appLE U' V (h.trans (f.preimage_mono hUU')) a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- A ring map of affine charts carries integer powers of the generic parameter to the
corresponding powers of the pulled-back parameter. -/
theorem power_appLE {U : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (n : ℤ) :
    f.appLE (U ⊓ X.basicOpen π) (V ⊓ Y.basicOpen (f.appTop π))
      (generic_le_preimage π f h) (power π U hU n) = power (f.appTop π) V hV n := by
  let DU := U ⊓ X.basicOpen π
  let DV := V ⊓ Y.basicOpen (f.appTop π)
  let α : Γ(X, U) →+* Γ(Y, V) := (f.appLE U V h).hom
  let β : Γ(X, DU) →+* Γ(Y, DV) := (f.appLE DU DV (generic_le_preimage π f h)).hom
  let : Algebra Γ(X, U) Γ(X, DU) :=
    (X.presheaf.map (homOfLE inf_le_left : DU ⟶ U).op).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(Y, DV) :=
    (Y.presheaf.map (homOfLE inf_le_left : DV ⟶ V).op).hom.toAlgebra
  have hDU : DU = X.basicOpen (parameter π U) := (X.basicOpen_res π _).symm
  have hDV : DV = Y.basicOpen (parameter (f.appTop π) V) := (Y.basicOpen_res (f.appTop π) _).symm
  have : IsLocalization.Away (parameter π U) Γ(X, DU) :=
    hU.isLocalization_of_eq_basicOpen _ _ hDU
  have : IsLocalization.Away (parameter (f.appTop π) V) Γ(Y, DV) :=
    hV.isLocalization_of_eq_basicOpen _ _ hDV
  have hα : α (parameter π U) = parameter (f.appTop π) V := by
    change f.appLE U V h (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op π) =
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (f.appTop π)
    have ht : f.appLE ⊤ ⊤ le_top = f.appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (map_appLE_apply f h le_top π).trans (by rw [← ht, appLE_map_apply])
  have : IsLocalization.Away (α (parameter π U)) Γ(Y, DV) := hα.symm ▸ inferInstance
  have hβ : β (algebraMap Γ(X, U) Γ(X, DU) (parameter π U)) =
      algebraMap Γ(Y, V) Γ(Y, DV) (α (parameter π U)) := by
    change f.appLE DU DV _ (X.presheaf.map (homOfLE inf_le_left : DU ⟶ U).op (parameter π U)) =
      Y.presheaf.map (homOfLE inf_le_left : DV ⟶ V).op (f.appLE U V h (parameter π U))
    exact (map_appLE_apply f (generic_le_preimage π f h) inf_le_left (parameter π U)).trans
      (appLE_map_apply f h inf_le_left (parameter π U)).symm
  exact (map_selfZPow α β hβ n).trans (by congr 1)

variable {M : X.Modules} (s : Γ(M, X.basicOpen π))

/-- The pullback of a generic section, regarded as a section over the basic open of
the pulled-back parameter. -/
abbrev pullbackGeneric : Γ((Scheme.Modules.pullback f).obj M, Y.basicOpen (f.appTop π)) :=
  ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE (genericPreimage_le π f)).op
    (pullbackSection f s)

theorem hasExponent_pullback {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    {hU : IsAffineOpen U} (hV : IsAffineOpen V) {e : Γ(M, U)} {n : ℤ}
    (hn : HasExponent π s hU e n) :
    HasExponent (f.appTop π) (pullbackGeneric π f s) hV
      (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op (pullbackSection f e)) n := by
  let Q := (Scheme.Modules.pullback f).obj M
  let DU := U ⊓ X.basicOpen π
  let DV := V ⊓ Y.basicOpen (f.appTop π)
  let a := f.appLE U V h
  let b := f.appLE DU DV (generic_le_preimage π f h)
  obtain ⟨u, hu⟩ := hn
  refine ⟨Units.map a.hom.toMonoidHom u, ?_⟩
  have h₁ := congrArg (pullbackSection f) hu
  rw [pullbackSection_map, pullbackSection_smul, pullbackSection_map] at h₁
  have hh := congrArg (Q.presheaf.map (homOfLE (generic_le_preimage π f h)).op) h₁
  rw [map_smul, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at hh
  change _ = b (X.presheaf.map (homOfLE inf_le_left : DU ⟶ U).op u.val * power π U hU n) • _ at hh
  change Q.presheaf.map (homOfLE (inf_le_right : DV ≤ Y.basicOpen (f.appTop π))).op
      (Q.presheaf.map (homOfLE (genericPreimage_le π f)).op (pullbackSection f s)) =
      (Y.presheaf.map (homOfLE (inf_le_left : DV ≤ V)).op (a u.val) *
        power (f.appTop π) V hV n) •
      Q.presheaf.map (homOfLE (inf_le_left : DV ≤ V)).op
        (Q.presheaf.map (homOfLE h).op (pullbackSection f e))
  rw [presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE]
  have hb : b (X.presheaf.map (homOfLE inf_le_left : DU ⟶ U).op u.val) =
      Y.presheaf.map (homOfLE (inf_le_left : DV ≤ V)).op (a u.val) := by
    exact (map_appLE_apply f (generic_le_preimage π f h) inf_le_left u.val).trans
      (appLE_map_apply f h inf_le_left u.val).symm
  rw [map_mul, hb, show b (power π U hU n) = _ from power_appLE π f h hU hV n] at hh
  exact hh

/-- If a generic frame pulls back to the restriction of a global frame, its exponent
vanishes on every tested chart whose image meets the zero locus of the parameter. -/
theorem exponent_eq_zero_of_normalized_pullback [IsIntegral Y]
    {U : X.Opens} {V : Y.Opens} [Nonempty V] (h : V ≤ f ⁻¹ᵁ U)
    {hU : IsAffineOpen U} (hV : IsAffineOpen V)
    (hπ0 : parameter (f.appTop π) V ≠ 0) (hπu : ¬ IsUnit (parameter (f.appTop π) V))
    {e : Γ(M, U)} (he : IsFreeGenerator e) {n : ℤ} (hn : HasExponent π s hU e n)
    (r : Γ((Scheme.Modules.pullback f).obj M, ⊤)) (hr : IsFreeGenerator r)
    (hnorm : pullbackSection f s =
      ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE le_top).op r) :
    n = 0 := by
  let Q := (Scheme.Modules.pullback f).obj M
  let eV := Q.presheaf.map (homOfLE h).op (pullbackSection f e)
  let rV := Q.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r
  have heV : IsFreeGenerator eV := (he.pullbackSection f).map h
  have hrV : IsFreeGenerator rV := hr.map le_top
  have hne : HasExponent (f.appTop π) (pullbackGeneric π f s) hV eV n :=
    hasExponent_pullback π f s h hV hn
  have h0 : HasExponent (f.appTop π) (pullbackGeneric π f s) hV rV 0 := by
    refine ⟨1, ?_⟩
    simp only [Units.val_one, map_one, power, selfZPow_zero, mul_one, one_smul]
    dsimp only [pullbackGeneric, rV]
    rw [hnorm, presheaf_map_homOfLE_map_homOfLE,
      presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE]
  exact hasExponent_unique _ _ hπ0 hπu heV hrV hne h0

end GenericFrame
end NeronDVR

namespace NeronDVR
namespace GenericFrame

variable {X : Scheme.{0}} (π : Γ(X, ⊤))

private theorem parameter_ne_zero [IsIntegral X] {U : X.Opens} [Nonempty U]
    (hπ : π ≠ 0) : parameter π U ≠ 0 :=
  (map_ne_zero_iff _ (map_injective_of_isIntegral X (homOfLE (le_top : U ≤ ⊤)))).mpr hπ

private theorem parameter_not_isUnit {U : X.Opens} {x : X} (hx : x ∈ U)
    (hxs : x ∉ X.basicOpen π) : ¬ IsUnit (parameter π U) := by
  intro h
  have he : U ⊓ X.basicOpen π = U :=
    (X.basicOpen_res π _).symm.trans (X.basicOpen_of_isUnit h)
  exact hxs (show x ∈ U ⊓ X.basicOpen π from he.symm ▸ hx).2

private theorem exists_prime_frame {M : X.Modules} [M.IsInvertible]
    (hcharts : ∀ (x : X), x ∉ X.basicOpen π → ∀ (U : X.Opens), x ∈ U →
      ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U ∧ Prime (parameter π V.1))
    {x : X} (hx : x ∉ X.basicOpen π) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ Prime (parameter π U.1) ∧
      ∃ e : Γ(M, U.1), IsFreeGenerator e := by
  obtain ⟨U, hxU, -, e, he⟩ := exists_isFreeGenerator M (X := X) (W := ⊤) (Opens.mem_top x)
  obtain ⟨V, hxV, hVU, hπV⟩ := hcharts x hx U.1 hxU
  exact ⟨V, hxV, hπV, _, he.map hVU⟩

variable {Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
variable {M : X.Modules} [M.IsInvertible]

/-- A free section on the complement of a parameter extends when its pullback to a
test scheme is normalized, each special component is met by the test scheme, and
the parameter is prime on sufficiently small charts at every special point. -/
theorem exists_global_frame_of_normalized_pullback
    (hπ : π ≠ 0) (hπY : f.appTop π ≠ 0)
    (s : Γ(M, X.basicOpen π)) (hs : IsFreeGenerator s)
    (r : Γ((Scheme.Modules.pullback f).obj M, ⊤)) (hr : IsFreeGenerator r)
    (hnorm : pullbackSection f s =
      ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE le_top).op r)
    (hcharts : ∀ (x : X), x ∉ X.basicOpen π → ∀ (U : X.Opens), x ∈ U →
      ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U ∧ Prime (parameter π V.1))
    (hmeets : ∀ (x : X), x ∉ X.basicOpen π → ∃ C : Set X,
      IsPreirreducible C ∧ x ∈ C ∧ C ⊆ (X.basicOpen π : Set X)ᶜ ∧ ∃ y : Y, f y ∈ C) :
    ∃ e : Γ(M, ⊤), IsFreeGenerator e ∧
      M.presheaf.map (homOfLE (le_top : X.basicOpen π ≤ ⊤)).op e = s := by
  have hD : (X.basicOpen π : Set X).Nonempty := by
    by_contra h
    rw [Opens.not_nonempty_iff_eq_bot, basicOpen_eq_bot_iff π] at h
    exact hπ h
  apply exists_isFreeGenerator_of_locally_extends _ hD s
  intro x
  by_cases hx : x ∈ X.basicOpen π
  · exact ⟨_, hx, s, hs, rfl⟩
  obtain ⟨C, hC, hxC, hCD, y, hyC⟩ := hmeets x hx
  have hy : f y ∉ X.basicOpen π := hCD hyC
  obtain ⟨U, hxU, hπU, e, he⟩ := exists_prime_frame π (M := M) hcharts hx
  obtain ⟨U₀, hyU₀, hπU₀, e₀, he₀⟩ := exists_prime_frame π (M := M) hcharts hy
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have : Nonempty U₀.1 := ⟨⟨f y, hyU₀⟩⟩
  obtain ⟨n, hn⟩ := exists_unit_mul_power π s U.2 hπU he hs
  obtain ⟨n₀, hn₀⟩ := exists_unit_mul_power π s U₀.2 hπU₀ he₀ hs
  obtain ⟨V, hV, hyV, hVU₀⟩ := exists_isAffineOpen_mem_and_subset
    (x := y) (U := f ⁻¹ᵁ U₀.1) hyU₀
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  have hyD : y ∉ Y.basicOpen (f.appTop π) := by
    rw [← f.preimage_basicOpen_top π]
    exact hy
  have hn₀zero : n₀ = 0 :=
    exponent_eq_zero_of_normalized_pullback π f s hVU₀ hV
      (parameter_ne_zero _ hπY) (parameter_not_isUnit _ hyV hyD) he₀ hn₀ r hr hnorm
  obtain ⟨z, hzC, hzU, hzU₀⟩ := hC (U.1 : Set X) (U₀.1 : Set X) U.1.isOpen U₀.1.isOpen
    ⟨x, hxC, hxU⟩ ⟨f y, hyC, hyU₀⟩
  obtain ⟨W, hW, hzW, hWW⟩ := exists_isAffineOpen_mem_and_subset
    (x := z) (U := U.1 ⊓ U₀.1) ⟨hzU, hzU₀⟩
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have hWU : W ≤ U.1 := hWW.trans inf_le_left
  have hWU₀ : W ≤ U₀.1 := hWW.trans inf_le_right
  have hn_eq : n = n₀ :=
    hasExponent_unique π s (parameter_ne_zero π hπ) (parameter_not_isUnit π hzW (hCD hzC))
      (he.map hWU) (he₀.map hWU₀) (hasExponent_restrict π s hWU hW hn)
      (hasExponent_restrict π s hWU₀ hW hn₀)
  exact ⟨U.1, hxU, exists_extension_of_exponent_zero π s U.2 he ((hn_eq.trans hn₀zero) ▸ hn)⟩

end GenericFrame
end NeronDVR

namespace NeronDVR
namespace GenericFrame

variable {X Y : Scheme.{0}} (p : X ⟶ Y) (j : Y ⟶ X) (hj : j ≫ p = 𝟙 Y)

include hj
private theorem appLE_leftInverse_app {D : X.Opens} (hD : D ≤ p ⁻¹ᵁ j ⁻¹ᵁ D) :
    p.appLE (j ⁻¹ᵁ D) D hD ≫ j.app D = 𝟙 _ := by
  rw [j.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE, Scheme.Hom.congr_app hj]
  simp [← Functor.map_comp]
  exact CategoryTheory.Functor.map_id _ _

/-- A generic frame can be normalized to agree with a chosen frame along a section,
provided the generic open is pulled back from the base of that section. -/
theorem exists_normalized_generator {M : X.Modules} {D : X.Opens}
    (hD : D ≤ p ⁻¹ᵁ j ⁻¹ᵁ D) (s : Γ(M, D)) (hs : IsFreeGenerator s)
    (r : Γ((Scheme.Modules.pullback j).obj M, ⊤)) (hr : IsFreeGenerator r) :
    ∃ t : Γ(M, D), IsFreeGenerator t ∧ pullbackSection j t =
      ((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE le_top).op r := by
  obtain ⟨u, hu⟩ := (hs.pullbackSection j).exists_unit_smul_eq
    (hr.map (le_top : j ⁻¹ᵁ D ≤ ⊤))
  let a := p.appLE (j ⁻¹ᵁ D) D hD
  let v := Units.map a.hom.toMonoidHom u
  refine ⟨v.val • s, hs.units_smul v, ?_⟩
  have hv : j.app D v.val = u.val := by
    change j.app D (a u.val) = _
    rw [← CommRingCat.comp_apply, appLE_leftInverse_app p j hj hD]
    rfl
  rw [pullbackSection_smul, hv]
  exact hu.symm

/-- Each point in the closed complement of a saturated open lies in a preirreducible
subset of that complement meeting the image of a section with irreducible fibres. -/
theorem special_preirreducible_meets_section [GeometricallyIntegral p]
    (hp : IsOpenMap p) {D : X.Opens} (hD : D = p ⁻¹ᵁ j ⁻¹ᵁ D)
    (x : X) (hx : x ∉ D) :
    ∃ C : Set X, IsPreirreducible C ∧ x ∈ C ∧ C ⊆ (D : Set X)ᶜ ∧ ∃ y : Y, j y ∈ C := by
  let C := p ⁻¹' {p x}
  have hC : IsIrreducible C := p.isIrreducible_preimage hp isIrreducible_singleton
  have hjx : p (j (p x)) = p x := by
    rw [← Scheme.Hom.comp_apply, hj]
    rfl
  refine ⟨C, hC.isPreirreducible, rfl, ?_, p x, hjx⟩
  intro z hz hzD
  have hz' : p z = p x := hz
  apply hx
  rw [hD] at hzD ⊢
  change p z ∈ j ⁻¹ᵁ D at hzD
  change p x ∈ j ⁻¹ᵁ D
  rwa [hz'] at hzD

end GenericFrame
end NeronDVR

namespace NeronDVR
namespace GenericFrame

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The chosen base parameter as a global function on the model. -/
abbrev pullbackParameter (π : R) : Γ(X, ⊤) :=
  f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)

abbrev chartRingMap (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op

private theorem fromSpec_comp_eq {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ f = Spec.map (chartRingMap f U) := by
  rw [← cancel_mono (Spec (CommRingCat.of R)).toSpecΓ, Category.assoc,
    Scheme.toSpecΓ_naturality, hU.fromSpec_toSpecΓ_assoc, ← Spec.map_comp,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  simp [chartRingMap]

private theorem range_spec_quotient_singleton (π : R) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({π} : Set R))))) =
      (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R))ᶜ := by
  let I : Ideal R := Ideal.span {π}
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
    (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R))ᶜ
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]
  exact PrimeSpectrum.zeroLocus_span _

/-- A flat nonempty scheme over a domain detects nonzero base parameters. -/
theorem pullbackParameter_ne_zero [IsDomain R] [Nonempty X] [Flat f] {π : R}
    (hπ : π ≠ 0) : pullbackParameter f π ≠ 0 := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hbot : (⊥ : PrimeSpectrum R) ⤳ f x :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, -, hy⟩ := Flat.generalizingMap f hbot
  have hyD : y ∈ X.basicOpen (pullbackParameter f π) := by
    rw [show X.basicOpen (pullbackParameter f π) =
      f ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
        from (f.preimage_basicOpen_top _).symm, basicOpen_eq_of_affine]
    change f y ∈ PrimeSpectrum.basicOpen π
    rw [hy, PrimeSpectrum.mem_basicOpen]
    exact hπ
  intro h0
  rw [h0, X.basicOpen_zero] at hyD
  exact hyD

/-- Every special point of a smooth integral scheme over a DVR has arbitrarily small
affine open neighbourhoods on which the uniformizer is a prime element. -/
theorem exists_prime_parameter_chart [IsDomain R] [IsDiscreteValuationRing R] [IsIntegral X]
    [Smooth f] (π : R) (hπ : Irreducible π)
    (x : X) (hx : x ∉ X.basicOpen (pullbackParameter f π)) (U : X.Opens) (hxU : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U ∧ Prime (parameter (pullbackParameter f π) V.1) := by
  let I : Ideal R := Ideal.span {π}
  have hI : I.IsMaximal := by
    change (Ideal.span {π}).IsMaximal
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    infer_instance
  let k := R ⧸ I
  let : Field k := Ideal.Quotient.field I
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let F := pullback f q
  let v : F ⟶ X := pullback.fst f q
  let g : F ⟶ Spec (CommRingCat.of k) := pullback.snd f q
  have hq : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hv : IsClosedImmersion v := MorphismProperty.pullback_fst f q hq
  have hg : Smooth g := by dsimp [g]; infer_instance
  have hrange : Set.range v = (X.basicOpen (pullbackParameter f π) : Set X)ᶜ := by
    change Set.range (pullback.fst f q) = _
    rw [Scheme.Pullback.range_fst, range_spec_quotient_singleton π, Set.preimage_compl]
    congr 1
    change ((f ⁻¹ᵁ (PrimeSpectrum.basicOpen π : (Spec (CommRingCat.of R)).Opens)) : Set X) = _
    rw [← basicOpen_eq_of_affine (R := CommRingCat.of R) π, Scheme.preimage_basicOpen_top]
  obtain ⟨y, rfl⟩ := (hrange.symm.subset hx)
  obtain ⟨C, hCopen, -, hCirred, hyC⟩ := SGA3IdComp.exists_irred_nbhd_of_smooth g y
  obtain ⟨W, hWopen, hW⟩ := v.isEmbedding.isInducing.isOpen_iff.mp hCopen
  let W' : X.Opens := ⟨W, hWopen⟩
  have hyW : v y ∈ W' := by
    change y ∈ v ⁻¹' W
    rwa [hW]
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (x := v y) (U := U ⊓ W') ⟨hxU, hyW⟩
  refine ⟨⟨V, hV⟩, hyV, hVU.trans inf_le_left, ?_⟩
  let P := pullback v hV.fromSpec
  let j : P ⟶ F := pullback.fst v hV.fromSpec
  have hj : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hP : Set.range j = v ⁻¹' (V : Set X) := by
    change Set.range (pullback.fst v hV.fromSpec) = _
    rw [Scheme.Pullback.range_fst, hV.range_fromSpec]
  have hPv : IsIrreducible (v ⁻¹' (V : Set X)) := by
    refine ⟨⟨y, hyV⟩, hCirred.2.open_subset (V.isOpen.preimage v.continuous) ?_⟩
    intro z hz
    rw [← hW]
    exact (hVU hz).2
  have : IrreducibleSpace P := j.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
    (isIrreducible_iff_irreducibleSpace.mp (hP.symm ▸ hPv : IsIrreducible (Set.range j)))
  have : IsReduced F := Smooth.isReduced_of_field g
  have : IsReduced P := isReduced_of_isOpenImmersion j
  have : IsIntegral P := isIntegral_of_irreducibleSpace_of_isReduced P
  let A := Γ(X, V)
  let : Algebra R A := (chartRingMap f V).hom.toAlgebra
  let J := I.map (algebraMap R A)
  let eQ : Spec (.of (A ⊗[R] k)) ≅ Spec (.of (A ⧸ J)) :=
    Scheme.Spec.mapIso (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toRingEquiv.toCommRingCatIso.op
  let e : P ≅ Spec (.of (A ⧸ J)) :=
    pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f q hV.fromSpec ≪≫
      pullback.congrHom (fromSpec_comp_eq f hV) rfl ≪≫ pullbackSpecIso R A k ≪≫ eQ
  have : Nonempty ↥(Spec (.of (A ⧸ J))) := Nonempty.map e.hom inferInstance
  have hDQ : IsDomain (A ⧸ J) := (affine_isIntegral_iff (.of (A ⧸ J))).mp
    (isIntegral_of_isOpenImmersion e.inv)
  have hJ : J = Ideal.span {parameter (pullbackParameter f π) V} := by
    change (Ideal.span {π}).map (algebraMap R A) = _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have : Nonempty V := ⟨⟨v y, hyV⟩⟩
  have hne : parameter (pullbackParameter f π) V ≠ 0 :=
    (map_ne_zero_iff _ (map_injective_of_isIntegral X (homOfLE (le_top : V ≤ ⊤)))).mpr (pullbackParameter_ne_zero f hπ.ne_zero)
  exact (Ideal.span_singleton_prime hne).mp (hJ ▸ ((Ideal.Quotient.isDomain_iff_prime J).mp hDQ))

end GenericFrame
end NeronDVR

namespace NeronDVR
namespace GenericFrame

private theorem exists_frame_of_pullback_open_iso_unit {X : Scheme.{0}} (D : X.Opens)
    (M : X.Modules) (h : Nonempty ((Scheme.Modules.pullback D.ι).obj M ≅ 𝟙_ D.toScheme.Modules)) :
    ∃ s : Γ(M, D), IsFreeGenerator s := by
  obtain ⟨e⟩ := h
  let α : 𝟙_ D.toScheme.Modules ≅ M.restrict D.ι :=
    e.symm ≪≫ ((restrictFunctorIsoPullback D.ι).app M).symm
  have hs := (isFreeGenerator_iff_isIso D.ι α.hom).mpr inferInstance
  have he : D.ι ''ᵁ (⊤ : D.toScheme.Opens) = D := D.ι_image_top
  exact he ▸ ⟨_, hs⟩

private theorem iso_unit_of_global_frame {X : Scheme.{0}} (M : X.Modules) {s : Γ(M, ⊤)}
    (hs : IsFreeGenerator s) : Nonempty (M ≅ 𝟙_ X.Modules) := by
  have : IsIso (homOfGlobalSection M s) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    have hfun : (fun a : Γ(X, U) => (homOfGlobalSection M s).app U a) =
        (fun a : Γ(X, U) => a • M.presheaf.map (homOfLE le_top).op s) :=
      funext (homOfGlobalSection_app M s U)
    change Function.Bijective (fun a : Γ(X, U) => (homOfGlobalSection M s).app U a)
    rw [hfun]
    exact hs U le_top
  exact ⟨(asIso (homOfGlobalSection M s)).symm⟩

/-- For a smooth, geometrically integral projection of smooth integral DVR schemes
with a section, a line trivial on the generic fibre and along the section is trivial. -/
theorem nonempty_iso_unit_of_generic_and_section
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ Spec (CommRingCat.of R)) [Smooth g]
    (p : X ⟶ Y) [Smooth p] [GeometricallyIntegral p]
    (j : Y ⟶ X) (hj : j ≫ p = 𝟙 Y)
    (π : R) (hπ : Irreducible π) (M : X.Modules) [M.IsInvertible]
    (hK : let D := X.basicOpen (pullbackParameter (p ≫ g) π)
      Nonempty ((Scheme.Modules.pullback D.ι).obj M ≅ 𝟙_ D.toScheme.Modules))
    (hJ : Nonempty ((Scheme.Modules.pullback j).obj M ≅ 𝟙_ Y.Modules)) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by
  let πX := pullbackParameter (p ≫ g) π
  let πY := pullbackParameter g π
  let D := X.basicOpen πX
  have hD : D = p ⁻¹ᵁ Y.basicOpen πY := (p.preimage_basicOpen_top πY).symm
  have hsaturated : D = p ⁻¹ᵁ j ⁻¹ᵁ D := by
    rw [hD, ← Scheme.Hom.comp_preimage j p, hj, Scheme.Hom.id_preimage]
  have hπJ : j.appTop πX = πY := by
    change j.appTop ((p ≫ g).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)) =
      g.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, hj, Category.id_comp]
  obtain ⟨s, hs⟩ := exists_frame_of_pullback_open_iso_unit D M hK
  obtain ⟨eJ⟩ := hJ
  let r := eJ.inv.app ⊤ (1 : Γ(Y, ⊤))
  have hr : IsFreeGenerator r := (isFreeGenerator_one (⊤ : Y.Opens)).app_hom eJ.symm
  obtain ⟨t, ht, htJ⟩ := exists_normalized_generator p j hj hsaturated.le s hs r hr
  have hπ0 : πX ≠ 0 := pullbackParameter_ne_zero (p ≫ g) hπ.ne_zero
  have hπ0J : j.appTop πX ≠ 0 := hπJ.symm ▸ pullbackParameter_ne_zero g hπ.ne_zero
  obtain ⟨z, hz, -⟩ := exists_global_frame_of_normalized_pullback πX j hπ0 hπ0J t ht r hr htJ
    (exists_prime_parameter_chart (p ≫ g) π hπ)
    (special_preirreducible_meets_section p j hj p.isOpenMap hsaturated)
  exact iso_unit_of_global_frame M hz

/-- Restriction to the generic fibre and the section jointly detect trivial Picard
classes along a smooth geometrically integral projection over a DVR. -/
theorem pic_eq_one_of_generic_and_section
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ Spec (CommRingCat.of R)) [Smooth g]
    (p : X ⟶ Y) [Smooth p] [GeometricallyIntegral p]
    (j : Y ⟶ X) (hj : j ≫ p = 𝟙 Y)
    (π : R) (hπ : Irreducible π) (L : X.Pic)
    (hK : Scheme.Pic.map (X.basicOpen (pullbackParameter (p ≫ g) π)).ι L = 1)
    (hJ : Scheme.Pic.map j L = 1) : L = 1 := by
  let M := (fromSkeleton X.Modules).obj L.val
  have eK := (Scheme.Pic.mk_eq_mk_iff _ _).mp hK
  have eJ := (Scheme.Pic.mk_eq_mk_iff _ _).mp hJ
  have e := nonempty_iso_unit_of_generic_and_section g p j hj π hπ M eK eJ
  exact (Scheme.Pic.mk_fromSkeleton L).symm.trans ((Scheme.Pic.mk_eq_mk_iff _ _).mpr e)

end GenericFrame
end NeronDVR

namespace NeronDVR
namespace GenericFrame

open ZInQ.Contrib.CloudR2NeronExistence.Henselian.NeronModelInfra
  (isLocalizationAway_of_irreducible)

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) {π : R} (hπ : Irreducible π)

include hπ
/-- The basic open of a uniformizer is the generic fibre, with the same map to the model. -/
theorem exists_iso_genericBasicOpen :
    ∃ e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅
      (X.basicOpen (pullbackParameter f π)).toScheme,
      e.hom ≫ (X.basicOpen (pullbackParameter f π)).ι =
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let D := X.basicOpen (pullbackParameter f π)
  let i : pullback f j ⟶ X := pullback.fst f j
  have : IsLocalization.Away π K := isLocalizationAway_of_irreducible K hπ
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization π
  have : IsOpenImmersion i := MorphismProperty.pullback_fst f j inferInstance
  have hj : Set.range j = (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range K π
  have hi : Set.range i = Set.range D.ι := by
    change Set.range (pullback.fst f j) = Set.range D.ι
    rw [Scheme.Pullback.range_fst, hj, Scheme.Opens.range_ι]
    change ((f ⁻¹ᵁ (PrimeSpectrum.basicOpen π : (Spec (CommRingCat.of R)).Opens)) : Set X) = _
    rw [← basicOpen_eq_of_affine (R := CommRingCat.of R) π, Scheme.preimage_basicOpen_top]
  exact ⟨IsOpenImmersion.isoOfRangeEq i D.ι hi, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

/-- Pulling back a Picard class to the basic open of the uniformizer is trivial
exactly when pulling it back to the fraction-field fibre is trivial. -/
theorem pic_map_genericBasicOpen_eq_one_iff (L : X.Pic) :
    Scheme.Pic.map (X.basicOpen (pullbackParameter f π)).ι L = 1 ↔
      Scheme.Pic.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) L = 1 := by
  obtain ⟨e, he⟩ := exists_iso_genericBasicOpen (K := K) f hπ
  rw [← he, Scheme.Pic.map_comp]
  constructor
  · rintro h
    rw [h, Scheme.Pic.one_eq_mk_unit, Scheme.Pic.map_mk_unit]
    rfl
  · intro h
    calc
      _ = Scheme.Pic.map e.inv (Scheme.Pic.map e.hom
          (Scheme.Pic.map (X.basicOpen (pullbackParameter f π)).ι L)) := by
        rw [← Scheme.Pic.map_comp, e.inv_hom_id, Scheme.Pic.map_id]
      _ = 1 := by
        rw [h, Scheme.Pic.one_eq_mk_unit, Scheme.Pic.map_mk_unit]
        rfl

end GenericFrame
end NeronDVR


namespace NeronDVR.GenericFrame

/-- The generic fibre and the section jointly detect trivial Picard classes. -/
theorem pic_eq_one_of_fractionField_and_section
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ Spec (CommRingCat.of R)) [Smooth g]
    (p : X ⟶ Y) [Smooth p] [GeometricallyIntegral p]
    (j : Y ⟶ X) (hj : j ≫ p = 𝟙 Y)
    (π : R) (hπ : Irreducible π) (L : X.Pic)
    (hK : Scheme.Pic.map (pullback.fst (p ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) L = 1)
    (hJ : Scheme.Pic.map j L = 1) : L = 1 :=
  pic_eq_one_of_generic_and_section g p j hj π hπ L
    ((pic_map_genericBasicOpen_eq_one_iff (K := K) (p ≫ g) hπ L).mpr hK) hJ

end NeronDVR.GenericFrame
