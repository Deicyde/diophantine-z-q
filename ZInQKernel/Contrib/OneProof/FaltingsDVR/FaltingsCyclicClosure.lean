import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Monomial relations describe the Zariski closure of a cyclic subgroup of a split torus. -/

noncomputable section

set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

open scoped BigOperators
open Function

namespace ZInQ.FaltingsRestate

variable {k : Type} [Field k] {r : ℕ}

private def powerCharacter (a : k) : Multiplicative ℕ →* k where
  toFun n := a ^ n.toAdd
  map_one' := pow_zero _
  map_mul' _ _ := pow_add _ _ _

private theorem powerCharacter_injective : Injective (powerCharacter (k := k)) := by
  intro a b h
  simpa [powerCharacter] using DFunLike.congr_fun h (Multiplicative.ofAdd (1 : ℕ))

private theorem linearIndependent_powerCharacter :
    LinearIndependent k (fun a : k => (powerCharacter a : Multiplicative ℕ → k)) :=
  (linearIndependent_monoidHom (Multiplicative ℕ) k).comp _ powerCharacter_injective

/-- A polynomial that vanishes on all powers of `x` vanishes at any `y` satisfying
all multiplicative monomial relations among the coordinates of `x`. -/
theorem mvPolynomial_eval_eq_zero_of_powers
    (x y : Fin r → k)
    (hrel : ∀ a b : Fin r →₀ ℕ, (∏ i, x i ^ a i) = (∏ i, x i ^ b i) →
      (∏ i, y i ^ a i) = (∏ i, y i ^ b i))
    (P : MvPolynomial (Fin r) k)
    (hP : ∀ n : ℕ, MvPolynomial.eval (fun i => x i ^ n) P = 0) :
    MvPolynomial.eval y P = 0 := by
  classical
  let vx (a : Fin r →₀ ℕ) := ∏ i, x i ^ a i
  let vy (a : Fin r →₀ ℕ) := ∏ i, y i ^ a i
  let s := P.support.image vx
  let c (z : k) := ∑ a ∈ P.support.filter (fun a => vx a = z), P.coeff a
  have hcoeff : ∀ z ∈ s, c z = 0 := by
    have hli := (linearIndependent_iff'.mp
      (linearIndependent_powerCharacter (k := k))) s c
    apply hli
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, powerCharacter]
    change (∑ z ∈ s, c z * z ^ n.toAdd) = 0
    have h := hP n.toAdd
    rw [MvPolynomial.eval_eq'] at h
    have he (a : Fin r →₀ ℕ) :
        (∏ i, (x i ^ n.toAdd) ^ a i) = vx a ^ n.toAdd := by
      unfold vx
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      simp only [← pow_mul, Nat.mul_comm]
    rw [← h]
    simp_rw [he]
    rw [← Finset.sum_fiberwise_of_maps_to (s := P.support) (t := s) (g := vx)
      (fun a ha => Finset.mem_image_of_mem _ ha)]
    apply Finset.sum_congr rfl
    intro z hz
    unfold c
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [(Finset.mem_filter.mp ha).2]
  rw [MvPolynomial.eval_eq']
  change ∑ a ∈ P.support, P.coeff a * vy a = 0
  rw [← Finset.sum_fiberwise_of_maps_to (s := P.support) (t := s) (g := vx)
    (fun a ha => Finset.mem_image_of_mem _ ha)]
  refine Finset.sum_eq_zero (fun z hz => ?_)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
  calc
    _ = (c (vx b)) * vy b := by
      unfold c
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      have hab : vy a = vy b := hrel a b (Finset.mem_filter.mp ha).2
      rw [hab]
    _ = 0 := by rw [hcoeff _ hz, zero_mul]

private theorem exists_bounded_character (D : Type) [CommGroup D]
    [Group.FG D] [Infinite D] [IsAlgClosed k] {m : ℕ} (hm : 1 < m) (hmk : (m : k) ≠ 0) :
    ∃ χ : D →* kˣ, χ ≠ 1 ∧ ∀ d, χ d ^ m = 1 := by
  classical
  obtain ⟨ι, j, hι, hj, p, hp, e, ⟨iso⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod D
  have hne : Nonempty j := by
    by_contra h
    haveI : IsEmpty j := not_nonempty_iff.mp h
    haveI : ∀ i : ι, NeZero (p i ^ e i) := fun i =>
      ⟨pow_ne_zero _ (hp i).ne_zero⟩
    haveI : Finite D := Finite.of_injective iso iso.injective
    exact not_finite D
  obtain ⟨j₀⟩ := hne
  haveI : NeZero (m : k) := ⟨hmk⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k m
  let u : kˣ := (hζ.isUnit (by omega)).unit
  have hu : (u : k) = ζ := IsUnit.unit_spec _
  have hum : u ^ m = 1 := by exact Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one, hu] using hζ.pow_eq_one)
  have hu1 : u ≠ 1 := by
    intro h
    have h' : ζ = 1 := by simp only [← hu, h, Units.val_one]
    have hx : ζ ^ 1 = 1 := by rw [pow_one, h']
    exact (not_le_of_gt hm) (Nat.le_of_dvd (by decide) (hζ.dvd_of_pow_eq_one 1 hx))
  let a : D →* Multiplicative ℤ :=
    (Pi.evalMonoidHom (fun _ : j => Multiplicative ℤ) j₀).comp
      ((MonoidHom.fst _ _).comp iso.toMonoidHom)
  let b : Multiplicative ℤ →* kˣ :=
    { toFun := fun v => u ^ v.toAdd
      map_one' := zpow_zero _
      map_mul' := fun x y => zpow_add _ _ _ }
  let χ := b.comp a
  refine ⟨χ, ?_, fun d => ?_⟩
  · intro h
    let d := iso.symm (fun _ => Multiplicative.ofAdd 1, 1)
    have he := DFunLike.congr_fun h d
    change u ^ ((iso d).1 j₀).toAdd = 1 at he
    rw [iso.apply_symm_apply] at he
    exact hu1 (by simpa using he)
  · change (u ^ (a d).toAdd) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hum, one_zpow]

private theorem tuple_character_of_infinite
    [IsAlgClosed k] (x : Fin r → kˣ) {m : ℕ} (hm : 1 < m) (hmk : (m : k) ≠ 0)
    [Infinite (Subgroup.closure (Set.range x))] :
    ∃ y : Fin r → kˣ, y ≠ 1 ∧ y ^ m = 1 ∧
      ∀ a b : Fin r →₀ ℕ, (∏ i, (x i : k) ^ a i) = (∏ i, (x i : k) ^ b i) →
        (∏ i, (y i : k) ^ a i) = (∏ i, (y i : k) ^ b i) := by
  let D := Subgroup.closure (Set.range x)
  haveI : Group.FG D := (Group.fg_iff_subgroup_fg D).mpr
    ((Subgroup.fg_iff D).mpr ⟨Set.range x, rfl, Set.finite_range x⟩)
  let t (i : Fin r) : D := ⟨x i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  obtain ⟨χ, hχ, hp⟩ := exists_bounded_character (k := k) D hm hmk
  let y := fun i => χ (t i)
  refine ⟨y, ?_, funext fun i => hp (t i), ?_⟩
  · intro he
    apply hχ
    ext d
    let E := Subgroup.map D.subtype χ.ker
    have hED : D ≤ E := (Subgroup.closure_le E).mpr (by
      rintro _ ⟨i, rfl⟩
      exact ⟨t i, congrFun he i, rfl⟩)
    obtain ⟨d', hd', heq⟩ := hED d.property
    have hh : d' = d := Subtype.ext heq
    have hd'' : χ d' = 1 := hd'
    change (χ d : k) = 1
    rw [← hh, hd'', Units.val_one]
  · intro a b h
    have hab : (∏ i, t i ^ a i) = ∏ i, t i ^ b i := by
      apply Subtype.ext
      apply Units.ext
      change ((D.subtype (∏ i, t i ^ a i) : kˣ) : k) =
        ((D.subtype (∏ i, t i ^ b i) : kˣ) : k)
      simpa only [map_prod, map_pow, Units.coe_prod, Units.val_pow_eq_pow_val, Subgroup.subtype_apply, t] using h
    have he := congrArg χ hab
    simp only [map_prod, map_pow] at he
    simpa only [Units.coe_prod, Units.val_pow_eq_pow_val] using congrArg Units.val he

/-- A subgroup of a split torus specified by polynomial equations is trivial
if it contains no nontrivial torsion of order invertible in the field. -/
theorem eq_one_of_polynomial_torus_subgroup_no_torsion
    [IsAlgClosed k] (H : Subgroup (Fin r → kˣ))
    (F : Set (MvPolynomial (Fin r) k))
    (hF : ∀ x, x ∈ H ↔ ∀ P ∈ F, MvPolynomial.eval (fun i => (x i : k)) P = 0)
    (hT : ∀ m : ℕ, (m : k) ≠ 0 → ∀ x ∈ H, x ^ m = 1 → x = 1)
    (x : Fin r → kˣ) (hx : x ∈ H) : x = 1 := by
  let D := Subgroup.closure (Set.range x)
  by_cases hD : Finite D
  · letI := Fintype.ofFinite D
    let m := Fintype.card D
    have hm : (m : k) ≠ 0 := FiniteField.card_cast_subgroup_card_ne_zero D
    apply hT m hm x hx
    funext i
    let d : D := ⟨x i, Subgroup.subset_closure (Set.mem_range_self i)⟩
    exact congrArg Subtype.val (pow_card_eq_one (x := d))
  · haveI : Infinite (Subgroup.closure (Set.range x)) := not_finite_iff_infinite.mp hD
    obtain ⟨m, hm, hmk⟩ : ∃ m : ℕ, 1 < m ∧ (m : k) ≠ 0 := by
      by_cases h : (2 : k) = 0
      · refine ⟨3, by decide, ?_⟩
        change (3 : k) ≠ 0
        have h3 : (3 : k) = 1 := by rw [show (3 : k) = 1 + 2 by norm_num, h, add_zero]
        rw [h3]; exact one_ne_zero
      · exact ⟨2, by decide, by simpa using h⟩
    obtain ⟨y, hy, hyp, hrel⟩ := tuple_character_of_infinite x hm hmk
    have hyH : y ∈ H := (hF y).mpr (fun P hP =>
      mvPolynomial_eval_eq_zero_of_powers (fun i => (x i : k)) (fun i => (y i : k)) hrel P
        (fun n => by simpa only [Pi.pow_apply, Units.val_pow_eq_pow_val] using
          (hF (x ^ n)).mp (H.pow_mem hx n) P hP))
    exact (hy (hT m hmk y hyH hyp)).elim

end ZInQ.FaltingsRestate
