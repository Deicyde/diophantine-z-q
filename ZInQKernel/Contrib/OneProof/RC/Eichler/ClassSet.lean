import ZInQKernel.Contrib.OneProof.RC.Eichler.Local

/-!
# The ideal class set and shortest-vector normalization

Tex 8466–8468. The ideal model uses locally principal full fractional right ideals.
The shortest-vector argument is on-the-spot (c).
-/

open Module

namespace ZInQ.Manuscript.RC.Eichler

variable {a b : ℚ} {R : Order a b}

namespace RightIdeal

/-- Left translation of a right ideal by a rational quaternion unit. -/
def translate (u : (B a b)ˣ) (I : RightIdeal R) : RightIdeal R where
  lattice := I.lattice.map ((u.mulLeftLinearEquiv ℚ (B a b)).restrictScalars ℤ).toLinearMap
  full := {
    fg := I.full.fg.map _
    span_eq_top := by
      rw [Submodule.map_coe]
      change Submodule.span ℚ ((u.mulLeftLinearEquiv ℚ (B a b)).toLinearMap ''
        (I.lattice : Set (B a b))) = ⊤
      rw [← Submodule.map_span, I.full.span_eq_top, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr (u.mulLeftLinearEquiv ℚ (B a b)).surjective }
  mul_mem := by
    rintro _ r ⟨x, hx, rfl⟩ hr
    exact ⟨x * r, I.mul_mem hx hr, (mul_assoc _ _ _).symm⟩

@[simp]
theorem mem_translate (u : (B a b)ˣ) (I : RightIdeal R) (x : B a b) :
    x ∈ (I.translate u).lattice ↔ (↑u⁻¹ : B a b) * x ∈ I.lattice := by
  change (∃ y ∈ I.lattice, (u : B a b) * y = x) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hy
  · intro h
    exact ⟨_, h, by simp only [← mul_assoc, Units.mul_inv, one_mul]⟩

theorem translate_one (I : RightIdeal R) : I.translate 1 = I := by
  apply RightIdeal.ext
  ext x
  simp

theorem translate_mul (u v : (B a b)ˣ) (I : RightIdeal R) :
    I.translate (u * v) = (I.translate v).translate u := by
  apply RightIdeal.ext
  ext x
  simp [mul_assoc]

theorem locallyPrincipal_translate (I : RightIdeal R) (hI : I.LocallyPrincipal)
    (u : (B a b)ˣ) : (I.translate u).LocallyPrincipal := by
  intro p hp
  obtain ⟨v, hv⟩ := hI p
  let up := Units.map (toLocal p).toMonoidHom u
  refine ⟨up * v, ?_⟩
  let f := (up.mulLeftLinearEquiv ℤ_[p] (Bp p a b)).toLinearMap
  have he : localLattice p (I.translate u).lattice = (localLattice p I.lattice).map f := by
    change Submodule.span ℤ_[p] (toLocal p ''
      (I.lattice.map ((u.mulLeftLinearEquiv ℚ (B a b)).restrictScalars ℤ).toLinearMap :
        Set (B a b))) = (Submodule.span ℤ_[p] (toLocal p '' (I.lattice : Set (B a b)))).map f
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    congr 2
  rw [he, Submodule.map_coe, hv, Set.image_image]
  simp only [Units.val_mul, mul_assoc]
  rfl

/-- Choose a nonzero element of least reduced norm in a definite right ideal. -/
theorem exists_min_norm (I : RightIdeal R) (ha : a < 0) (hb : b < 0) :
    ∃ x ∈ I.lattice, x ≠ 0 ∧
      ∀ y ∈ I.lattice, y ≠ 0 → Visibility.nrd x ≤ Visibility.nrd y := by
  obtain ⟨w, hw, hw0⟩ := I.exists_ne_zero
  let s := {x : B a b | x ∈ I.lattice ∧ Visibility.nrd x ≤ Visibility.nrd w} \ {0}
  have hs : s.Finite := (finite_norm_le ha hb _ I.full.fg _).sdiff
  obtain ⟨x, ⟨⟨hx, hxw⟩, hx0⟩, hmin⟩ :=
    Set.exists_min_image s Visibility.nrd hs ⟨w, ⟨hw, le_rfl⟩, hw0⟩
  refine ⟨x, hx, hx0, fun y hy hy0 => ?_⟩
  by_cases h : Visibility.nrd y ≤ Visibility.nrd w
  · exact hmin y ⟨⟨hy, h⟩, hy0⟩
  · exact hxw.trans (le_of_not_ge h)

/-- Each class contains an over-lattice of the order whose nonzero vectors have norm at least one. -/
theorem exists_normalized (I : RightIdeal R) (ha : a < 0) (hb : b < 0) :
    ∃ u : (B a b)ˣ, R.lattice ≤ (I.translate u).lattice ∧
      ∀ y ∈ (I.translate u).lattice, y ≠ 0 → 1 ≤ Visibility.nrd y := by
  obtain ⟨x, hx, hx0, hmin⟩ := I.exists_min_norm ha hb
  let u := unitOfNeZero ha hb x hx0
  refine ⟨u⁻¹, ?_, ?_⟩
  · intro r hr
    rw [mem_translate, inv_inv]
    exact I.mul_mem hx hr
  · intro y hy hy0
    rw [mem_translate, inv_inv] at hy
    have hxy0 : (u : B a b) * y ≠ 0 := by
      intro he
      apply hy0
      simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using
        congrArg (fun z => (↑u⁻¹ : B a b) * z) he
    have h := hmin _ hy hxy0
    change Visibility.nrd (u : B a b) ≤ Visibility.nrd ((u : B a b) * y) at h
    rw [Visibility.nrd_mul] at h
    have hp : 0 < Visibility.nrd (u : B a b) := nrd_pos ha hb hx0
    exact le_of_mul_le_mul_left (by simpa only [mul_one] using h) hp

end RightIdeal

/-- Locally principal fractional right ideals of the fixed order. -/
abbrev LPIdeal (R : Order a b) := {I : RightIdeal R // I.LocallyPrincipal}

/-- Isomorphism classes of locally principal right ideals, via rational left multiplication. -/
def idealRel (R : Order a b) : Setoid (LPIdeal R) where
  r I J := ∃ u : (B a b)ˣ, I.val.translate u = J.val
  iseqv := {
    refl I := ⟨1, I.val.translate_one⟩
    symm := by
      rintro I J ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      rw [← hu, ← RightIdeal.translate_mul, inv_mul_cancel, RightIdeal.translate_one]
    trans := by
      rintro I J K ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨v * u, by rw [RightIdeal.translate_mul, hu, hv]⟩ }

abbrev ClassSet (R : Order a b) := Quotient (idealRel R)

/-- A representative right ideal chosen once for each class. -/
noncomputable def representative (z : ClassSet R) : LPIdeal R := z.out

/-- The unit group of a chosen representative's left order, in the ambient quaternion group. -/
noncomputable def classG (ha : a < 0) (hb : b < 0) (z : ClassSet R) : Subgroup (B a b)ˣ :=
  ((representative z).val.leftOrder ha hb).G

theorem class_card_G_dvd (ha : a < 0) (hb : b < 0) (z : ClassSet R) :
    Nat.card (classG ha hb z) ∣ Odd.c0 :=
  ((representative z).val.leftOrder ha hb).card_G_dvd ha hb

end ZInQ.Manuscript.RC.Eichler
