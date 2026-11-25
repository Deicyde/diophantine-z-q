import ZInQKernel.Contrib.OneProof.RC.Adelic.Ideal
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.ComputeDegree

/-! Left lattices and left ideals of an order, and the standard involution.
Orders are stable under the involution: their elements are integral, so the
reduced trace is an integer by Gauss's lemma, and `star x = trd x − x`. The
involution sends locally principal left ideals to locally principal right
ideals of the same order and exchanges right and left multiplication by units,
so the left ideal classes are equivalent to `ClassSet`. This is the proved
mirror used to read Voight's left-ideal convention (Ch. 42) in the right-ideal
class set of tex 8466–8468. Voight's Rem. 42.3.3 is not used. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic Polynomial

variable {a b : ℚ}

/-- The reduced trace `2 re x` of an element integral over `ℤ` is an integer. -/
theorem two_re_int_of_isIntegral {x : B a b} (hx : IsIntegral ℤ x) :
    ∃ t : ℤ, (t : ℚ) = 2 * x.re := by
  classical
  have hx' := hx
  set t : ℚ := 2 * x.re with ht
  set n : ℚ := (x * star x).re with hn
  have hstar : star x = algebraMap ℚ (B a b) t - x := by
    rw [QuaternionAlgebra.star_eq_two_re_sub, QuaternionAlgebra.coe_algebraMap]
    simp [ht]
  have hnorm : x * star x = algebraMap ℚ (B a b) n := by
    rw [QuaternionAlgebra.coe_algebraMap]
    exact QuaternionAlgebra.mul_star_eq_coe (a := x)
  let m : ℚ[X] := X ^ 2 - C t * X + C n
  have hmonic : m.Monic := by
    unfold m
    monicity!
  have hdeg : m.natDegree = 2 := by
    unfold m
    compute_degree!
  have hm0 : aeval x m = 0 := by
    simp only [m, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
    rw [← hnorm, hstar, Algebra.commutes]
    noncomm_ring
  obtain ⟨P, hPm, hP⟩ := hx
  let Q : ℚ[X] := P.map (algebraMap ℤ ℚ)
  have hQ : aeval x Q = 0 := by
    rw [aeval_map_algebraMap, aeval_def, hP]
  let r := Q %ₘ m
  have hr : aeval x r = 0 := by
    change aeval x (Q %ₘ m) = 0
    rw [modByMonic_eq_sub_mul_div, map_sub, map_mul, hQ, hm0, zero_mul, sub_zero]
  have hrdeg : r.natDegree ≤ 1 := by
    have hne : m ≠ 1 := by
      intro h
      rw [h, natDegree_one] at hdeg
      exact absurd hdeg (by norm_num)
    have := natDegree_modByMonic_lt Q hmonic hne
    rw [hdeg] at this
    show (Q %ₘ m).natDegree ≤ 1
    omega
  have hrform := eq_X_add_C_of_natDegree_le_one hrdeg
  rw [hrform] at hr
  simp only [map_add, map_mul, aeval_C, aeval_X] at hr
  have hinjQ : Function.Injective (algebraMap ℚ (B a b)) := (algebraMap ℚ (B a b)).injective
  by_cases h1 : r.coeff 1 = 0
  · have h0 : r.coeff 0 = 0 := by
      rw [h1, map_zero, zero_mul, zero_add] at hr
      exact hinjQ (by rw [hr, map_zero])
    have hr0 : r = 0 := by
      rw [hrform, h1, h0]
      simp
    have hdvd : m ∣ Q := (modByMonic_eq_zero_iff_dvd hmonic).mp hr0
    obtain ⟨g', hg'⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hPm hdvd
    rw [hmonic.leadingCoeff, C_1, mul_one] at hg'
    have hc := congrArg (fun f : ℚ[X] => f.coeff 1) hg'
    simp only [coeff_map] at hc
    have hm1 : m.coeff 1 = -t := by
      simp [m, coeff_X, coeff_C]
    refine ⟨-(g'.coeff 1), ?_⟩
    rw [Int.cast_neg]
    change -(algebraMap ℤ ℚ (g'.coeff 1)) = t
    rw [hc, hm1, neg_neg]
  · set c : ℚ := -(r.coeff 0) / r.coeff 1 with hcdef
    have hxr : x = algebraMap ℚ (B a b) c := by
      have he : algebraMap ℚ (B a b) (r.coeff 1) * x = -algebraMap ℚ (B a b) (r.coeff 0) :=
        eq_neg_of_add_eq_zero_left hr
      calc x = algebraMap ℚ (B a b) (r.coeff 1)⁻¹ * (algebraMap ℚ (B a b) (r.coeff 1) * x) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h1, map_one, one_mul]
        _ = algebraMap ℚ (B a b) c := by
            rw [he, mul_neg, ← map_mul, ← map_neg, hcdef]
            congr 1
            field_simp
    have hci : IsIntegral ℤ c := by
      let f : ℚ →ₐ[ℤ] B a b := (Algebra.ofId ℚ (B a b)).restrictScalars ℤ
      have hf : Function.Injective f := hinjQ
      apply (isIntegral_algHom_iff f hf).mp
      change IsIntegral ℤ (algebraMap ℚ (B a b) c)
      rw [← hxr]
      exact hx'
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hci
    refine ⟨2 * y, ?_⟩
    have hre : x.re = c := by
      rw [hxr, QuaternionAlgebra.coe_algebraMap]
      rfl
    rw [ht, hre, ← hy, algebraMap_int_eq, eq_intCast]
    push_cast
    ring

/-- The standard involution as a rational linear equivalence. -/
def starQ : B a b ≃ₗ[ℚ] B a b where
  toFun := star
  invFun := star
  map_add' := star_add
  map_smul' r x := QuaternionAlgebra.star_smul r x
  left_inv := star_star
  right_inv := star_star

/-- The standard involution as an integral linear map. -/
abbrev starZ : B a b →ₗ[ℤ] B a b := ((starQ (a := a) (b := b)).restrictScalars ℤ).toLinearMap

@[simp] theorem starZ_apply (x : B a b) : starZ x = star x := rfl

/-- Elements of an order are stable under the standard involution. -/
theorem order_star_mem (R : Order a b) {x : B a b} (hx : x ∈ R.ring) : star x ∈ R.ring := by
  let S : Subalgebra ℤ (B a b) :=
    { R.ring with algebraMap_mem' := fun n => by simpa using R.ring.intCast_mem n }
  have hS : S.toSubmodule.FG := by
    have he : S.toSubmodule = R.lattice := Submodule.ext fun _ => Iff.rfl
    rw [he]
    exact R.full.fg
  obtain ⟨t, ht⟩ := two_re_int_of_isIntegral (IsIntegral.of_mem_of_fg S hS x hx)
  have hst : star x = algebraMap ℚ (B a b) (t : ℚ) - x := by
    rw [QuaternionAlgebra.star_eq_two_re_sub, ht, QuaternionAlgebra.coe_algebraMap]
    simp
  rw [hst, map_intCast]
  exact R.ring.sub_mem (intCast_mem R.ring t) hx

theorem order_lattice_map_star (R : Order a b) : R.lattice.map starZ = R.lattice := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact order_star_mem R hy
  · intro hx
    exact ⟨star x, order_star_mem R hx, star_star x⟩

section Local

variable (p : ℕ) [Fact p.Prime]

theorem toLocal_star (x : B a b) : toLocal p (star x) = star (toLocal p x) := by
  ext <;> simp [toLocal]

/-- The local standard involution as an integral linear map. -/
def starZp : Bp p a b →ₗ[ℤ_[p]] Bp p a b where
  toFun := star
  map_add' := star_add
  map_smul' r y := by
    change star ((r : ℚ_[p]) • y) = (r : ℚ_[p]) • star y
    exact QuaternionAlgebra.star_smul _ _

@[simp] theorem starZp_apply (y : Bp p a b) : starZp p y = star y := rfl

theorem localLattice_map_star (L : Submodule ℤ (B a b)) :
    localLattice p (L.map starZ) = (localLattice p L).map (starZp p) := by
  unfold localLattice
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 2

theorem star_mem_completion (R : Order a b) {y : Bp p a b} (hy : y ∈ R.completion p) :
    star y ∈ R.completion p := by
  have h1 : y ∈ localLattice p R.lattice := by
    rw [← R.completion_toSubmodule]
    exact hy
  have h2 : star y ∈ (localLattice p R.lattice).map (starZp p) := ⟨y, h1, rfl⟩
  rw [← localLattice_map_star, order_lattice_map_star] at h2
  rw [← R.completion_toSubmodule] at h2
  exact h2

end Local

/-- A full lattice stays full under a rational linear automorphism. -/
theorem fullLattice_map_equiv {L : Submodule ℤ (B a b)} (hL : FullLattice L)
    (e : B a b ≃ₗ[ℚ] B a b) : FullLattice (L.map (e.restrictScalars ℤ).toLinearMap) where
  fg := hL.fg.map _
  span_eq_top := by
    rw [Submodule.map_coe]
    change Submodule.span ℚ (e.toLinearMap '' (L : Set (B a b))) = ⊤
    rw [← Submodule.map_span, hL.span_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective

/-- Right multiplication by a rational unit as a rational linear equivalence. -/
def mulRightEquiv (u : (B a b)ˣ) : B a b ≃ₗ[ℚ] B a b where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  map_add' x y := add_mul _ _ _
  map_smul' r x := smul_mul_assoc _ _ _
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]

/-- A full left ideal of an order. -/
structure LeftIdeal (R : Order a b) where
  lattice : Submodule ℤ (B a b)
  full : FullLattice lattice
  mul_mem : ∀ ⦃r x : B a b⦄, r ∈ R.ring → x ∈ lattice → r * x ∈ lattice

namespace LeftIdeal

variable {R : Order a b}

@[ext]
theorem ext {I J : LeftIdeal R} (h : I.lattice = J.lattice) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- The order itself as a left ideal. -/
def self (R : Order a b) : LeftIdeal R where
  lattice := R.lattice
  full := R.full
  mul_mem := fun {_ _} hr hx => R.ring.mul_mem hr hx

/-- Local principality as a left ideal, with a generator in the local unit group. -/
def LocallyPrincipal (I : LeftIdeal R) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ u : (Bp p a b)ˣ,
    (localLattice p I.lattice : Set (Bp p a b)) =
      (fun x : Bp p a b => x * (u : Bp p a b)) '' (R.completion p : Set (Bp p a b))

/-- The right order of a left ideal. -/
def rightRing (I : LeftIdeal R) : Subring (B a b) where
  carrier := {u | ∀ x ∈ I.lattice, x * u ∈ I.lattice}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hu hv x hx := by rw [mul_add]; exact I.lattice.add_mem (hu x hx) (hv x hx)
  neg_mem' hu x hx := by rw [mul_neg]; exact I.lattice.neg_mem (hu x hx)
  mul_mem' {u v} hu hv x hx := by rw [← mul_assoc]; exact hv _ (hu x hx)

/-- Right translation of a left ideal by a rational quaternion unit. -/
def translate (u : (B a b)ˣ) (I : LeftIdeal R) : LeftIdeal R where
  lattice := I.lattice.map ((mulRightEquiv u).restrictScalars ℤ).toLinearMap
  full := fullLattice_map_equiv I.full _
  mul_mem := by
    rintro r _ hr ⟨x, hx, rfl⟩
    exact ⟨r * x, I.mul_mem hr hx, (mul_assoc _ _ _)⟩

theorem mem_translate (u : (B a b)ˣ) (I : LeftIdeal R) (x : B a b) :
    x ∈ (I.translate u).lattice ↔ x * (↑u⁻¹ : B a b) ∈ I.lattice := by
  change (∃ y ∈ I.lattice, y * (u : B a b) = x) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mul_assoc, Units.mul_inv, mul_one] using hy
  · intro h
    exact ⟨_, h, by simp only [mul_assoc, Units.inv_mul, mul_one]⟩

theorem translate_one (I : LeftIdeal R) : I.translate 1 = I := by
  apply LeftIdeal.ext
  ext x
  simp [mem_translate]

theorem translate_translate (u v : (B a b)ˣ) (I : LeftIdeal R) :
    (I.translate u).translate v = I.translate (u * v) := by
  apply LeftIdeal.ext
  ext x
  simp [mem_translate, mul_assoc]

/-- The image of a left ideal under the standard involution. -/
def mirror (I : LeftIdeal R) : RightIdeal R where
  lattice := I.lattice.map starZ
  full := fullLattice_map_equiv I.full starQ
  mul_mem := by
    rintro _ r ⟨y, hy, rfl⟩ hr
    refine ⟨star r * y, I.mul_mem (order_star_mem R hr) hy, ?_⟩
    change star (star r * y) = star y * r
    rw [star_mul, star_star]

theorem mem_mirror (I : LeftIdeal R) (x : B a b) :
    x ∈ I.mirror.lattice ↔ star x ∈ I.lattice := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change star (star y) ∈ I.lattice
    rwa [star_star]
  · intro h
    exact ⟨star x, h, star_star x⟩

theorem mirror_translate (u : (B a b)ˣ) (I : LeftIdeal R) :
    (I.translate u).mirror = I.mirror.translate (star u) := by
  apply RightIdeal.ext
  ext x
  rw [RightIdeal.mem_translate, mem_mirror, mem_mirror, mem_translate, star_mul, ← star_inv,
    Units.coe_star, star_star]

theorem mirror_locallyPrincipal (I : LeftIdeal R) (hI : I.LocallyPrincipal) :
    I.mirror.LocallyPrincipal := by
  intro p _
  obtain ⟨u, hu⟩ := hI p
  refine ⟨star u, ?_⟩
  change (localLattice p (I.lattice.map starZ) : Set (Bp p a b)) = _
  rw [localLattice_map_star, Submodule.map_coe, hu]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Units.coe_star, starZp_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨star x, star_mem_completion p R hx, by rw [star_mul]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨star x * (u : Bp p a b), ⟨star x, star_mem_completion p R hx, rfl⟩, ?_⟩
    rw [star_mul, star_star]

/-- The rational right order of a left ideal and the left order of its mirror
correspond under the standard involution. -/
theorem mem_leftRing_mirror (I : LeftIdeal R) (x : B a b) :
    x ∈ I.mirror.leftRing ↔ star x ∈ I.rightRing := by
  constructor
  · intro hx y hy
    have h := hx (star y) ((mem_mirror I _).mpr (by rwa [star_star]))
    rw [mem_mirror, star_mul, star_star] at h
    exact h
  · intro hx y hy
    rw [mem_mirror] at hy ⊢
    rw [star_mul]
    exact hx _ hy

end LeftIdeal

namespace RightIdeal

variable {R : Order a b}

/-- The image of a right ideal under the standard involution. -/
def unmirror (I : RightIdeal R) : LeftIdeal R where
  lattice := I.lattice.map starZ
  full := fullLattice_map_equiv I.full starQ
  mul_mem := by
    rintro r _ hr ⟨y, hy, rfl⟩
    refine ⟨y * star r, I.mul_mem hy (order_star_mem R hr), ?_⟩
    change star (y * star r) = r * star y
    rw [star_mul, star_star]

theorem mem_unmirror (I : RightIdeal R) (x : B a b) :
    x ∈ (unmirror I).lattice ↔ star x ∈ I.lattice := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change star (star y) ∈ I.lattice
    rwa [star_star]
  · intro h
    exact ⟨star x, h, star_star x⟩

theorem unmirror_translate (u : (B a b)ˣ) (I : RightIdeal R) :
    unmirror (I.translate u) = (unmirror I).translate (star u) := by
  apply LeftIdeal.ext
  ext x
  rw [LeftIdeal.mem_translate, mem_unmirror, mem_unmirror, Eichler.RightIdeal.mem_translate, star_mul,
    ← star_inv, Units.coe_star, star_star]

theorem unmirror_locallyPrincipal (I : RightIdeal R) (hI : I.LocallyPrincipal) :
    (unmirror I).LocallyPrincipal := by
  intro p _
  obtain ⟨u, hu⟩ := hI p
  refine ⟨star u, ?_⟩
  change (localLattice p (I.lattice.map starZ) : Set (Bp p a b)) = _
  rw [localLattice_map_star, Submodule.map_coe, hu]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Units.coe_star, starZp_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨star x, star_mem_completion p R hx, by rw [star_mul]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(u : Bp p a b) * star x, ⟨star x, star_mem_completion p R hx, rfl⟩, ?_⟩
    rw [star_mul, star_star]

theorem mirror_unmirror (I : RightIdeal R) : (unmirror I).mirror = I := by
  apply RightIdeal.ext
  ext x
  rw [LeftIdeal.mem_mirror, mem_unmirror, star_star]

end RightIdeal

theorem LeftIdeal.unmirror_mirror {R : Order a b} (I : LeftIdeal R) : RightIdeal.unmirror I.mirror = I := by
  apply LeftIdeal.ext
  ext x
  rw [RightIdeal.mem_unmirror, LeftIdeal.mem_mirror, star_star]

/-- Locally principal left ideals of an order. -/
abbrev LPLeftIdeal (R : Order a b) := {I : LeftIdeal R // I.LocallyPrincipal}

/-- Isomorphism classes of locally principal left ideals, via rational right multiplication. -/
def leftIdealRel (R : Order a b) : Setoid (LPLeftIdeal R) where
  r I J := ∃ u : (B a b)ˣ, I.val.translate u = J.val
  iseqv := {
    refl I := ⟨1, I.val.translate_one⟩
    symm := by
      rintro I J ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      rw [← hu, LeftIdeal.translate_translate, mul_inv_cancel, LeftIdeal.translate_one]
    trans := by
      rintro I J K ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨u * v, by rw [← LeftIdeal.translate_translate, hu, hv]⟩ }

/-- The left ideal class set. -/
abbrev LeftClassSet (R : Order a b) := Quotient (leftIdealRel R)

/-- The mirror of a locally principal left ideal. -/
def LPLeftIdeal.mirror {R : Order a b} (I : LPLeftIdeal R) : LPIdeal R :=
  ⟨I.val.mirror, I.val.mirror_locallyPrincipal I.prop⟩

/-- The standard involution identifies left ideal classes with the class set. -/
def leftClassSetEquiv (R : Order a b) : LeftClassSet R ≃ ClassSet R where
  toFun := Quotient.map LPLeftIdeal.mirror (by
    rintro I J ⟨u, hu⟩
    exact ⟨star u, by
      change I.val.mirror.translate (star u) = J.val.mirror
      rw [← hu, LeftIdeal.mirror_translate]⟩)
  invFun := Quotient.map (fun I : LPIdeal R => ⟨RightIdeal.unmirror I.val, RightIdeal.unmirror_locallyPrincipal I.val I.prop⟩)
    (by
      rintro I J ⟨u, hu⟩
      exact ⟨star u, by
        change (RightIdeal.unmirror I.val).translate (star u) = RightIdeal.unmirror J.val
        rw [← hu, RightIdeal.unmirror_translate]⟩)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ I => exact congrArg (Quotient.mk _) (Subtype.ext I.val.unmirror_mirror)
  right_inv x := by
    induction x using Quotient.inductionOn with
    | _ I => exact congrArg (Quotient.mk _) (Subtype.ext (RightIdeal.mirror_unmirror I.val))

theorem leftClassSetEquiv_mk {R : Order a b} (I : LPLeftIdeal R) :
    leftClassSetEquiv R (Quotient.mk _ I) = Quotient.mk _ I.mirror := rfl

theorem LeftIdeal.mirror_self (R : Order a b) : (LeftIdeal.self R).mirror = RightIdeal.self R := by
  apply RightIdeal.ext
  exact order_lattice_map_star R

end ZInQ.Manuscript.RC.HCMV21
