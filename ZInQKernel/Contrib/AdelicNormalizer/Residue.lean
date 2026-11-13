import ZInQKernel.Contrib.AdelicNormalizer.Objects

/-!
# The residue ring of the local order at three

`Residue3` is a new type wrapping order coordinates `Fin 4 → ZMod 3` in the ordered basis
`(1, i, (1+j)/2, (i+ij)/2)`. Its addition is coordinatewise, while its multiplication and one are
`GlueRepo.A1.mul3` and `GlueRepo.A1.one3`, the reductions of the integral structure constants.
The pointwise ring structure on `Fin 4 → ZMod 3` is not used.

* `localReduction : localOrder 3 →+* Residue3` reduces the `ℤ_3`-coordinates
  (`GlueVigneras.coord`) through `PadicInt.toZMod`.
* `localReduction_eq_iff`: two order elements have the same reduction iff all coordinate
  differences lie in `3 ℤ_3`. `mem_ker_localReduction_iff`: the kernel is `3 𝒪_3`.
* `unitReduction : localOrderUnits 3 →* Residue3ˣ` is surjective. The lift uses integral
  coordinate representatives, `GlueRepo.A1.isUnit3_iff` and `GlueVigneras.mem_OpUnits_iff`.
* `card_units : Nat.card Residue3ˣ = 72`, from `GlueRepo.A1.card_units_mod3`.
* `scalarUnits : (ZMod 3)ˣ →* Residue3ˣ` has central range of order `2`, and the quotient has
  order `36`. Local scalars of `ℤ_3` reduce to these scalars.

This is a contribution, not an acceptance record.
-/

open Quaternion

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat
  QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

namespace G1.Residue

open GlueRepo.A1

/-- `𝒪/3𝒪` in order coordinates, as a new type. -/
@[ext]
structure Residue3 where
  /-- Coordinates in the ordered basis `(1, i, (1+j)/2, (i+ij)/2)`. -/
  coords : Fin 4 → ZMod 3

namespace Residue3

instance : Zero Residue3 := ⟨⟨0⟩⟩
instance : One Residue3 := ⟨⟨one3⟩⟩
instance : Add Residue3 := ⟨fun x y => ⟨x.coords + y.coords⟩⟩
instance : Neg Residue3 := ⟨fun x => ⟨-x.coords⟩⟩
instance : Sub Residue3 := ⟨fun x y => ⟨x.coords - y.coords⟩⟩
instance : SMul ℕ Residue3 := ⟨fun n x => ⟨n • x.coords⟩⟩
instance : SMul ℤ Residue3 := ⟨fun n x => ⟨n • x.coords⟩⟩
instance : Mul Residue3 := ⟨fun x y => ⟨mul3 x.coords y.coords⟩⟩

@[simp] theorem coords_zero : (0 : Residue3).coords = 0 := rfl
@[simp] theorem coords_one : (1 : Residue3).coords = one3 := rfl
@[simp] theorem coords_add (x y : Residue3) : (x + y).coords = x.coords + y.coords := rfl
@[simp] theorem coords_neg (x : Residue3) : (-x).coords = -x.coords := rfl
@[simp] theorem coords_sub (x y : Residue3) : (x - y).coords = x.coords - y.coords := rfl
@[simp] theorem coords_mul (x y : Residue3) : (x * y).coords = mul3 x.coords y.coords := rfl

/-- The coordinate bijection (of types only; the multiplication is not pointwise). -/
def equivCoords : Residue3 ≃ (Fin 4 → ZMod 3) where
  toFun := coords
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Residue3 := Fintype.ofEquiv _ equivCoords.symm
instance : DecidableEq Residue3 := equivCoords.decidableEq

theorem coords_injective : Function.Injective coords := fun _ _ h => Residue3.ext h

instance : AddCommGroup Residue3 :=
  Function.Injective.addCommGroup coords coords_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem mul3_assoc (a b c : Fin 4 → ZMod 3) : mul3 (mul3 a b) c = mul3 a (mul3 b c) := by
  funext k; fin_cases k <;> simp [mul3] <;> ring

theorem one3_mul3 (a : Fin 4 → ZMod 3) : mul3 one3 a = a := by
  funext k; fin_cases k <;> simp [mul3, one3]

theorem mul3_one3 (a : Fin 4 → ZMod 3) : mul3 a one3 = a := by
  funext k; fin_cases k <;> simp [mul3, one3]

theorem zero_mul3 (a : Fin 4 → ZMod 3) : mul3 0 a = 0 := by
  funext k; fin_cases k <;> simp [mul3]

theorem mul3_zero (a : Fin 4 → ZMod 3) : mul3 a 0 = 0 := by
  funext k; fin_cases k <;> simp [mul3]

theorem mul3_add (a b c : Fin 4 → ZMod 3) : mul3 a (b + c) = mul3 a b + mul3 a c := by
  funext k; fin_cases k <;> simp [mul3] <;> ring

theorem add_mul3 (a b c : Fin 4 → ZMod 3) : mul3 (a + b) c = mul3 a c + mul3 b c := by
  funext k; fin_cases k <;> simp [mul3] <;> ring

instance : Ring Residue3 where
  __ := (inferInstance : AddCommGroup Residue3)
  mul_assoc a b c := Residue3.ext (mul3_assoc a.coords b.coords c.coords)
  one_mul a := Residue3.ext (one3_mul3 a.coords)
  mul_one a := Residue3.ext (mul3_one3 a.coords)
  zero_mul a := Residue3.ext (zero_mul3 a.coords)
  mul_zero a := Residue3.ext (mul3_zero a.coords)
  left_distrib a b c := Residue3.ext (mul3_add a.coords b.coords c.coords)
  right_distrib a b c := Residue3.ext (add_mul3 a.coords b.coords c.coords)

/-- Units of `Residue3` are exactly the coordinate vectors with a two-sided `mul3` inverse. -/
noncomputable def unitsEquiv :
    Residue3ˣ ≃ {x : Fin 4 → ZMod 3 // ∃ y, mul3 x y = one3 ∧ mul3 y x = one3} where
  toFun u := ⟨u.val.coords, u.inv.coords, congrArg coords u.val_inv, congrArg coords u.inv_val⟩
  invFun x := ⟨⟨x.1⟩, ⟨x.2.choose⟩, Residue3.ext x.2.choose_spec.1,
    Residue3.ext x.2.choose_spec.2⟩
  left_inv _ := Units.ext rfl
  right_inv _ := rfl

theorem isUnit_iff (x : Residue3) : IsUnit x ↔ nrd3 x.coords ≠ 0 := by
  rw [← isUnit3_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact (unitsEquiv u).2
  · intro h
    exact ⟨unitsEquiv.symm ⟨x.coords, h⟩, rfl⟩

/-- `|(𝒪/3𝒪)ˣ| = 72`. -/
theorem card_units : Nat.card Residue3ˣ = 72 := by
  rw [Nat.card_congr unitsEquiv, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert card_units_mod3

end Residue3

open Residue3

/-! ### Reduction of the local order at three -/

section Local

open GlueVigneras

theorem coord_combp (n : Fin 4 → ℤ_[3]) (k : Fin 4) :
    coord 3 (combp 3 n) k = (n k : ℚ_[3]) := by
  fin_cases k <;> simp [coord, combp] <;> ring

/-- The `ℤ_3`-coordinates of an element of the local order. -/
noncomputable def localCoord (x : localOrder 3) (k : Fin 4) : ℤ_[3] :=
  ⟨coord 3 (x : Bp 3) k, (mem_Op_iff_coord 3 (x : Bp 3)).1 x.2 k⟩

@[simp] theorem coe_localCoord (x : localOrder 3) (k : Fin 4) :
    (localCoord x k : ℚ_[3]) = coord 3 (x : Bp 3) k :=
  rfl

theorem localCoord_eq_of (x : localOrder 3) (n : Fin 4 → ℤ_[3])
    (h : (x : Bp 3) = combp 3 n) : localCoord x = n := by
  funext k
  apply PadicInt.ext
  rw [coe_localCoord, h, coord_combp]

theorem combp_localCoord (x : localOrder 3) : combp 3 (localCoord x) = x := by
  obtain ⟨n, hn⟩ := x.2
  have h : localCoord x = n := localCoord_eq_of x n hn.symm
  rw [h, hn]

theorem combp_add (n m : Fin 4 → ℤ_[3]) : combp 3 (n + m) = combp 3 n + combp 3 m := by
  ext <;> simp [combp] <;> ring

theorem coe_three : ((3 : ℤ_[3]) : ℚ_[3]) = 3 := by
  have := PadicInt.coe_natCast (p := 3) 3; simpa using this

theorem combp_three_mul (n : Fin 4 → ℤ_[3]) :
    combp 3 (fun k => 3 * n k) = 3 * combp 3 n := by
  ext <;> simp [combp, coe_three] <;> ring

theorem one_eq_combp : (1 : Bp 3) = combp 3 ![1, 0, 0, 0] := by
  ext <;> simp [combp]

theorem localCoord_mul (x y : localOrder 3) :
    localCoord (x * y) = coordMul (localCoord x) (localCoord y) := by
  apply localCoord_eq_of
  rw [← combp_mul, combp_localCoord, combp_localCoord]
  rfl

theorem localCoord_add (x y : localOrder 3) :
    localCoord (x + y) = localCoord x + localCoord y := by
  apply localCoord_eq_of
  rw [combp_add, combp_localCoord, combp_localCoord]
  rfl

theorem localCoord_one : localCoord 1 = ![1, 0, 0, 0] :=
  localCoord_eq_of 1 _ one_eq_combp

theorem localCoord_zero : localCoord 0 = 0 :=
  localCoord_eq_of 0 0 (by ext <;> simp [combp])

/-- Coordinatewise reduction of integral coordinates. -/
noncomputable def red (n : Fin 4 → ℤ_[3]) : Residue3 := ⟨fun k => PadicInt.toZMod (n k)⟩

@[simp] theorem coords_red (n : Fin 4 → ℤ_[3]) (k : Fin 4) :
    (red n).coords k = PadicInt.toZMod (n k) :=
  rfl

theorem red_coordMul (n m : Fin 4 → ℤ_[3]) : red (coordMul n m) = red n * red m := by
  ext k
  fin_cases k <;> simp [red, coordMul, mul3, map_ofNat]

/-- Reduction of the actual local order at three. -/
noncomputable def localReduction : localOrder 3 →+* Residue3 where
  toFun x := red (localCoord x)
  map_one' := by
    rw [localCoord_one]
    ext k
    fin_cases k <;> simp [red, one3]
  map_mul' x y := by
    rw [localCoord_mul, red_coordMul]
  map_zero' := by
    rw [localCoord_zero]
    ext k
    simp [red]
  map_add' x y := by
    rw [localCoord_add]
    ext k
    simp [red]

@[simp] theorem coords_localReduction (x : localOrder 3) (k : Fin 4) :
    (localReduction x).coords k = PadicInt.toZMod (localCoord x k) :=
  rfl

theorem localReduction_combp (n : Fin 4 → ℤ_[3]) (h : combp 3 n ∈ localOrder 3) :
    localReduction ⟨combp 3 n, h⟩ = red n := by
  change red (localCoord _) = red n
  rw [localCoord_eq_of _ n rfl]

/-- Integral coordinate representatives `0, 1, 2`. -/
noncomputable def liftCoords (r : Fin 4 → ZMod 3) : Fin 4 → ℤ_[3] :=
  fun k => ((r k).val : ℤ_[3])

theorem red_liftCoords (r : Fin 4 → ZMod 3) : red (liftCoords r) = ⟨r⟩ := by
  ext k
  simp [red, liftCoords]

/-- The order element with the chosen integral representative coordinates. -/
noncomputable def liftOrder (r : Fin 4 → ZMod 3) : localOrder 3 :=
  ⟨combp 3 (liftCoords r), ⟨liftCoords r, rfl⟩⟩

theorem localReduction_liftOrder (r : Fin 4 → ZMod 3) :
    localReduction (liftOrder r) = ⟨r⟩ := by
  change red (localCoord _) = _
  rw [localCoord_eq_of _ (liftCoords r) rfl, red_liftCoords]

theorem localReduction_surjective : Function.Surjective localReduction :=
  fun x => ⟨liftOrder x.coords, localReduction_liftOrder x.coords⟩

theorem toZMod_eq_iff (a b : ℤ_[3]) :
    PadicInt.toZMod a = PadicInt.toZMod b ↔ ∃ c : ℤ_[3], a - b = 3 * c := by
  rw [← RingHom.sub_mem_ker_iff, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  simp only [Nat.cast_ofNat]
  rfl

/-- Kernel relation in coordinates: equal reductions iff coordinatewise congruence mod `3`. -/
theorem localReduction_eq_iff (x y : localOrder 3) :
    localReduction x = localReduction y ↔
      ∀ k, ∃ c : ℤ_[3], localCoord x k - localCoord y k = 3 * c := by
  rw [Residue3.ext_iff, funext_iff]
  exact forall_congr' fun k => toZMod_eq_iff _ _

/-- The kernel of the reduction is `3 𝒪_3`. -/
theorem mem_ker_localReduction_iff (x : localOrder 3) :
    x ∈ RingHom.ker localReduction ↔ ∃ y ∈ localOrder 3, (x : Bp 3) = 3 * y := by
  rw [RingHom.mem_ker, ← map_zero localReduction, localReduction_eq_iff, localCoord_zero]
  constructor
  · intro h
    choose c hc using h
    refine ⟨combp 3 c, ⟨c, rfl⟩, ?_⟩
    rw [← combp_three_mul, ← combp_localCoord x]
    congr 1
    funext k
    simpa using hc k
  · rintro ⟨y, ⟨m, rfl⟩, hx⟩
    rw [← combp_three_mul] at hx
    rw [localCoord_eq_of x _ hx]
    exact fun k => ⟨m k, by simp⟩

theorem localReduction_eq_iff_sub (x y : localOrder 3) :
    localReduction x = localReduction y ↔
      ∃ z ∈ localOrder 3, (x : Bp 3) - y = 3 * z := by
  rw [← RingHom.sub_mem_ker_iff, mem_ker_localReduction_iff]
  rfl

/-! ### Unit reduction -/

/-- Reduction of order units, induced by `localReduction`. -/
noncomputable def unitReduction : localOrderUnits 3 →* Residue3ˣ :=
  (Units.map localReduction.toMonoidHom).comp
    (localOrder 3).toSubmonoid.unitsEquivUnitsType.toMonoidHom

theorem coe_unitReduction (u : localOrderUnits 3) :
    ((unitReduction u : Residue3ˣ) : Residue3) =
      localReduction ⟨((u : (Bp 3)ˣ) : Bp 3), u.2.1⟩ :=
  rfl

theorem star_mul_eq (x : Bp 3) :
    star x * x = algebraMap ℚ_[3] (Bp 3) (GlueVigneras.nrd 3 x) := by
  ext <;> simp [GlueVigneras.nrd] <;> ring

/-- A local quaternion with nonzero reduced norm, as a unit. -/
noncomputable def unitOfNrd (x : Bp 3) (hx : GlueVigneras.nrd 3 x ≠ 0) : (Bp 3)ˣ where
  val := x
  inv := (GlueVigneras.nrd 3 x)⁻¹ • star x
  val_inv := by
    rw [mul_smul_comm, GlueVigneras.mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hx, map_one]
  inv_val := by
    rw [smul_mul_assoc, star_mul_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hx, map_one]

theorem nrd_combp (n : Fin 4 → ℤ_[3]) :
    GlueVigneras.nrd 3 (combp 3 n) =
      (((n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2) + (-2) * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2) : ℤ_[3]) :
        ℚ_[3]) := by
  rw [GlueVigneras.nrd_coord]
  simp only [coord_combp]
  push_cast [GlueVigneras.coe_two]
  ring

theorem toZMod_nrd_liftCoords (r : Fin 4 → ZMod 3) :
    PadicInt.toZMod ((liftCoords r 0 ^ 2 + liftCoords r 0 * liftCoords r 2 + liftCoords r 2 ^ 2) +
      (-2) * (liftCoords r 1 ^ 2 + liftCoords r 1 * liftCoords r 3 + liftCoords r 3 ^ 2)) =
      nrd3 r := by
  simp [liftCoords, nrd3, map_ofNat]
  ring

theorem norm_nrd_liftOrder (r : Fin 4 → ZMod 3) (hr : nrd3 r ≠ 0) :
    ‖GlueVigneras.nrd 3 (liftOrder r : Bp 3)‖ = 1 := by
  change ‖GlueVigneras.nrd 3 (combp 3 (liftCoords r))‖ = 1
  rw [nrd_combp, ← PadicInt.norm_def]
  apply norm_eq_one_of_toZMod_ne
  rw [toZMod_nrd_liftCoords]
  exact hr

theorem nrd_liftOrder_ne_zero (r : Fin 4 → ZMod 3) (hr : nrd3 r ≠ 0) :
    GlueVigneras.nrd 3 (liftOrder r : Bp 3) ≠ 0 := by
  intro h
  have := norm_nrd_liftOrder r hr
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The integral lift of a residue unit, as a local order unit. -/
noncomputable def liftUnit (w : Residue3ˣ) : localOrderUnits 3 :=
  have hr : nrd3 (w : Residue3).coords ≠ 0 := (isUnit_iff _).1 w.isUnit
  ⟨unitOfNrd (liftOrder (w : Residue3).coords : Bp 3) (nrd_liftOrder_ne_zero _ hr),
    (mem_localOrderUnits 3 _).2
      ((mem_OpUnits_iff 3 (Or.inr rfl) _).2 (norm_nrd_liftOrder _ hr))⟩

theorem unitReduction_liftUnit (w : Residue3ˣ) : unitReduction (liftUnit w) = w := by
  apply Units.ext
  rw [coe_unitReduction]
  exact localReduction_liftOrder (w : Residue3).coords

theorem unitReduction_surjective : Function.Surjective unitReduction :=
  fun w => ⟨liftUnit w, unitReduction_liftUnit w⟩

end Local

/-! ### Scalars -/

/-- Scalars `c ↦ c · 1` in the residue ring. -/
def scalarRes : ZMod 3 →+* Residue3 where
  toFun c := ⟨![c, 0, 0, 0]⟩
  map_one' := rfl
  map_mul' c d := by
    ext k
    fin_cases k <;> simp [mul3, mul_comm]
  map_zero' := by
    ext k
    fin_cases k <;> rfl
  map_add' c d := by
    ext k
    fin_cases k <;> simp

@[simp] theorem coords_scalarRes (c : ZMod 3) : (scalarRes c).coords = ![c, 0, 0, 0] := rfl

theorem scalarRes_injective : Function.Injective scalarRes := by
  intro c d h
  have := congrArg (fun x : Residue3 => x.coords 0) h
  simpa using this

theorem scalarRes_comm (c : ZMod 3) (x : Residue3) : scalarRes c * x = x * scalarRes c := by
  ext k
  fin_cases k <;> simp [mul3] <;> ring

/-- Scalar residue units `(ZMod 3)ˣ → Residue3ˣ`. -/
def scalarUnits : (ZMod 3)ˣ →* Residue3ˣ := Units.map scalarRes.toMonoidHom

@[simp] theorem coe_scalarUnits (c : (ZMod 3)ˣ) :
    ((scalarUnits c : Residue3ˣ) : Residue3) = scalarRes (c : ZMod 3) :=
  rfl

theorem scalarUnits_injective : Function.Injective scalarUnits := by
  intro c d h
  apply Units.ext
  apply scalarRes_injective
  rw [← coe_scalarUnits, ← coe_scalarUnits, h]

instance scalarUnits_range_normal : scalarUnits.range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, rfl⟩ := hn
  refine ⟨c, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_scalarUnits, ← scalarRes_comm, mul_assoc,
    Units.mul_inv, mul_one]

theorem card_scalarUnits_range : Nat.card scalarUnits.range = 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective scalarUnits_injective).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units]

theorem card_quotient_scalarUnits : Nat.card (Residue3ˣ ⧸ scalarUnits.range) = 36 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup scalarUnits.range
  rw [card_units, card_scalarUnits_range] at h
  omega

/-! ### Local scalars reduce to residue scalars -/

section LocalScalar

open GlueVigneras

theorem algebraMap_eq_combp (z : ℤ_[3]) :
    algebraMap ℚ_[3] (Bp 3) (z : ℚ_[3]) = combp 3 ![z, 0, 0, 0] := by
  ext <;> simp [combp]

/-- The integral local scalar `z` as an element of the local order. -/
noncomputable def localScalarOrder (z : ℤ_[3]) : localOrder 3 :=
  ⟨algebraMap ℚ_[3] (Bp 3) (z : ℚ_[3]), ⟨![z, 0, 0, 0], (algebraMap_eq_combp z).symm⟩⟩

theorem localReduction_localScalarOrder (z : ℤ_[3]) :
    localReduction (localScalarOrder z) = scalarRes (PadicInt.toZMod z) := by
  change red (localCoord _) = _
  rw [localCoord_eq_of _ _ (algebraMap_eq_combp z)]
  ext k
  fin_cases k <;> simp [red]

/-- Integral local scalar units, through the actual central embedding `localScalar 3`. -/
noncomputable def localIntScalar : ℤ_[3]ˣ →* localOrderUnits 3 where
  toFun c := ⟨localScalar 3 (Units.map PadicInt.Coe.ringHom.toMonoidHom c),
    (mem_localOrderUnits 3 _).2
      ⟨(localScalarOrder (c : ℤ_[3])).2, (localScalarOrder ((c⁻¹ : ℤ_[3]ˣ) : ℤ_[3])).2⟩⟩
  map_one' := Subtype.ext (by simp only [map_one]; rfl)
  map_mul' c d := Subtype.ext (by simp only [map_mul]; rfl)

theorem unitReduction_localIntScalar (c : ℤ_[3]ˣ) :
    unitReduction (localIntScalar c) = scalarUnits (Units.map PadicInt.toZMod.toMonoidHom c) := by
  apply Units.ext
  rw [coe_unitReduction, coe_scalarUnits]
  exact localReduction_localScalarOrder (c : ℤ_[3])

/-- The reductions of the integral local scalar units are exactly the residue scalar units. -/
theorem range_unitReduction_localIntScalar :
    (unitReduction.comp localIntScalar).range = scalarUnits.range := by
  ext w
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (unitReduction_localIntScalar c).symm⟩
  · rintro ⟨c, rfl⟩
    have hz : PadicInt.toZMod (((c : ZMod 3).val : ℕ) : ℤ_[3]) = (c : ZMod 3) := by
      simp
    have hu : IsUnit (((c : ZMod 3).val : ℕ) : ℤ_[3]) := by
      rw [PadicInt.isUnit_iff]
      apply norm_eq_one_of_toZMod_ne
      rw [hz]
      exact c.ne_zero
    refine ⟨hu.unit, ?_⟩
    rw [MonoidHom.comp_apply, unitReduction_localIntScalar]
    congr 1
    apply Units.ext
    exact hz

end LocalScalar

end G1.Residue
