import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# A concrete model of the coefficient ring `𝒪` (Lane RC7)

The manuscript (`diophantine_zq.tex`, tex 2747–2748, Definition `ex:arith-data`) puts
`Λ = ℤ₂[[t]]` and `𝒪 = (Λ_{(2)})^`, the `2`-adic completion of the localization of `Λ` at the
prime `(2)`; tex 3728 repeats `𝒪 = (ℤ₂[[t]]_{(2)})^`.

This file builds `𝒪` as that `2`-adic completion presented as an inverse limit,
`𝒪 = lim_n Λ_{(2)}/2ⁿ = lim_n (ℤ/2ⁿ)((t))`.
Modulo `2ⁿ`, inverting the elements of `Λ` outside `(2)` inverts exactly `t`: such an element
is `2b + tᵏu` with `u` a unit of `Λ`, and `2` is nilpotent modulo `2ⁿ`.  Hence
`Λ_{(2)}/2ⁿ = (ℤ/2ⁿ)[[t]][t⁻¹] = (ℤ/2ⁿ)((t))`, the Laurent series ring
`LaurentSeries (ZMod (2 ^ n))`.

## Main definitions and results

* `redLaurent n` : the coefficientwise reduction `(ℤ/2ⁿ⁺¹)((t)) → (ℤ/2ⁿ)((t))`;
* `OInf` : the subring of compatible sequences in `∏ₙ (ℤ/2ⁿ)((t))`, and the type `OO = ↥OInf`;
* `lamToO : Λ →+* OO`, which makes `OO` a `Λ`-algebra;
* `tInv`, `algebraMap_X_mul_tInv`, `isUnit_t` : `t` is invertible in `𝒪`;
* `isUnit_one_add_two_mul_OO` : `1 + 2y` is invertible for every `y ∈ 𝒪`;
* `proj M : OO →+* (ℤ/2^M)((t))`, the reduction modulo `2^M`, with `proj_two_pow_mul`,
  `proj_algebraMap`, `proj_tInv`;
* `lamToO_injective` : `Λ → 𝒪` is injective, so `𝒪` is nontrivial;
* `coeff_proj_eq_zero_of_mem` : the coefficient form of the pole bounds: if
  `y ≡ t^{-L} a (mod 2^M)` with `a ∈ Λ`, then the reduction of `y` modulo `2^M` has no Laurent
  term below degree `-L`.

The model has the defining properties of `(Λ_{(2)})^`:

* `isUnit_algebraMap_of_not_mem_span_two` : elements of `Λ` outside `(2)` become units;
* `proj_eq_zero_iff_mem`, `ker_proj`, `proj_surjective`, `quotTwoPowEquiv` :
  `𝒪/2^M ≅ (ℤ/2^M)((t))`;
* an `IsAdicComplete (Ideal.span {2}) OO` instance: `𝒪` is `2`-adically complete and separated;
* `exists_eq_two_pow_mul_unit` and an `IsDomain OO` instance: every nonzero element is `2^M`
  times a unit, and `𝒪` is an integral domain.

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Determinant

namespace OModel

/-- Coefficientwise application of a ring homomorphism to Laurent series. -/
noncomputable def laurentMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one (f : R →*₀ S)
  map_mul' _ _ := HahnSeries.map_mul (f : R →ₙ+* S)
  map_zero' := HahnSeries.map_zero (f : ZeroHom R S)
  map_add' _ _ := HahnSeries.map_add (f : R →+ S)

/-- **Tex 2747–2748, 3728 (PROVED).**  `laurentMap f` acts on coefficients by `f`. -/
theorem laurentMap_coeff {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : LaurentSeries R) (i : ℤ) : (laurentMap f x).coeff i = f (x.coeff i) := rfl

end OModel

open OModel

/-- The coefficientwise reduction `(ℤ/2ⁿ⁺¹)((t)) → (ℤ/2ⁿ)((t))`, the transition map of the inverse
system `n ↦ Λ_{(2)}/2ⁿ = (ℤ/2ⁿ)((t))` whose limit is `𝒪` (tex 2747–2748, 3728). -/
noncomputable def redLaurent (n : ℕ) :
    LaurentSeries (ZMod (2 ^ (n + 1))) →+* LaurentSeries (ZMod (2 ^ n)) :=
  laurentMap (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)))

/-- **Tex 2747–2748, 3728 (PROVED).**  `redLaurent n` reduces each coefficient modulo `2ⁿ`. -/
theorem redLaurent_coeff (n : ℕ) (x : LaurentSeries (ZMod (2 ^ (n + 1)))) (i : ℤ) :
    (redLaurent n x).coeff i = ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))
      (x.coeff i) := rfl

/-- **Tex 2747–2748, 3728.**  The model of `𝒪 = (ℤ₂[[t]]_{(2)})^`: the `2`-adic completion
presented as the inverse limit `lim_n (ℤ/2ⁿ)((t))`, i.e. the subring of compatible sequences
in `∏ₙ (ℤ/2ⁿ)((t))`. -/
def OInf : Subring (∀ n : ℕ, LaurentSeries (ZMod (2 ^ n))) where
  carrier := {x | ∀ n, redLaurent n (x (n + 1)) = x n}
  mul_mem' {a b} ha hb n := by
    simp only [Set.mem_ofPred_eq] at ha hb
    simp only [Pi.mul_apply, map_mul, ha n, hb n]
  one_mem' n := by simp only [Pi.one_apply, map_one]
  add_mem' {a b} ha hb n := by
    simp only [Set.mem_ofPred_eq] at ha hb
    simp only [Pi.add_apply, map_add, ha n, hb n]
  zero_mem' n := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {a} ha n := by
    simp only [Set.mem_ofPred_eq] at ha
    simp only [Pi.neg_apply, map_neg, ha n]

/-- The ring `𝒪 = (Λ_{(2)})^` of tex 2747–2748 and 3728, as the type of the inverse-limit
subring `OInf`; it is a commutative ring. -/
abbrev OO : Type := ↥OInf

/-- **Tex 2747–2748, 3728 (PROVED).**  Membership in the inverse limit is compatibility. -/
theorem mem_OInf_iff (x : ∀ n : ℕ, LaurentSeries (ZMod (2 ^ n))) :
    x ∈ OInf ↔ ∀ n, redLaurent n (x (n + 1)) = x n := Iff.rfl

namespace OModel

/-- Component `n` of `Λ → 𝒪`: reduce the coefficients modulo `2ⁿ`, then view the power series
as a Laurent series. -/
noncomputable def lamComp (n : ℕ) : PowerSeries ℤ_[2] →+* LaurentSeries (ZMod (2 ^ n)) :=
  (HahnSeries.ofPowerSeries ℤ (ZMod (2 ^ n))).comp (PowerSeries.map (PadicInt.toZModPow n))

/-- **Tex 2747–2748, 3728 (PROVED).**  The components of `Λ → 𝒪` are compatible. -/
theorem redLaurent_lamComp (n : ℕ) (a : PowerSeries ℤ_[2]) :
    redLaurent n (lamComp (n + 1) a) = lamComp n a := by
  ext i
  simp only [redLaurent, laurentMap_coeff, lamComp, RingHom.comp_apply, PowerSeries.coeff_coe]
  split_ifs with h
  · simp
  · simp [PowerSeries.coeff_map, PadicInt.cast_toZModPow _ _ (Nat.le_succ n)]

end OModel

/-- The structure map `Λ = ℤ₂[[t]] → 𝒪` (tex 2747–2748): component `n` reduces the coefficients
modulo `2ⁿ` and views the result in `(ℤ/2ⁿ)((t))`. -/
noncomputable def lamToO : PowerSeries ℤ_[2] →+* OO :=
  (RingHom.pi lamComp).codRestrict OInf (fun a n => redLaurent_lamComp n a)

/-- `𝒪` is a `Λ`-algebra via `lamToO`. -/
noncomputable instance : Algebra (PowerSeries ℤ_[2]) OO := lamToO.toAlgebra

/-- **Tex 2747–2748, 3728 (PROVED).**  The algebra map `Λ → 𝒪` is `lamToO`. -/
theorem algebraMap_eq_lamToO : algebraMap (PowerSeries ℤ_[2]) OO = lamToO := rfl

/-- The inverse of `t` in `𝒪`: componentwise `t⁻¹ = HahnSeries.single (-1) 1`. -/
noncomputable def tInv : OO := ⟨fun _ => HahnSeries.single (-1) 1, fun n => by
  ext i
  simp only [redLaurent, laurentMap_coeff, HahnSeries.coeff_single]
  split_ifs <;> simp only [map_one, map_zero]⟩

/-- **Tex 2747–2748, 3728 (PROVED).**  In `𝒪`, `t · t⁻¹ = 1`. -/
theorem algebraMap_X_mul_tInv : algebraMap (PowerSeries ℤ_[2]) OO PowerSeries.X * tInv = 1 := by
  apply Subtype.ext
  funext n
  show lamComp n PowerSeries.X * HahnSeries.single (-1) 1 = 1
  simp [lamComp, HahnSeries.ofPowerSeries_X]

/-- **Tex 2747–2748, 3728 (PROVED).**  The variable `t` of `Λ = ℤ₂[[t]]` is a unit of
`𝒪 = (Λ_{(2)})^` (it lies outside the prime `(2)`). -/
theorem isUnit_t : IsUnit (algebraMap (PowerSeries ℤ_[2]) OO PowerSeries.X) :=
  IsUnit.of_mul_eq_one _ algebraMap_X_mul_tInv

/-- **Tex 2747–2748, 3728 (PROVED).**  An element of the inverse limit `𝒪` whose components are
all units is a unit (inverses are unique, hence compatible). -/
theorem isUnit_of_forall_isUnit_component (x : OO)
    (h : ∀ n, IsUnit ((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) n)) : IsUnit x := by
  let v : ∀ n, LaurentSeries (ZMod (2 ^ n)) := fun n => ↑(h n).unit⁻¹
  have hv : v ∈ OInf := by
    intro n
    have h1 : (x : ∀ n, LaurentSeries (ZMod (2 ^ n))) (n + 1) * v (n + 1) = 1 :=
      (h (n + 1)).mul_val_inv
    have h2 : (x : ∀ n, LaurentSeries (ZMod (2 ^ n))) n * v n = 1 := (h n).mul_val_inv
    have h3 := congrArg (redLaurent n) h1
    rw [map_mul, map_one, x.2 n] at h3
    calc redLaurent n (v (n + 1)) = v n * ((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) n *
          redLaurent n (v (n + 1))) := by rw [← mul_assoc, mul_comm (v n), h2, one_mul]
      _ = v n := by rw [h3, mul_one]
  refine IsUnit.of_mul_eq_one ⟨v, hv⟩ ?_
  apply Subtype.ext
  funext n
  exact (h n).mul_val_inv

namespace OModel

/-- **Tex 2747–2748, 3728 (PROVED).**  In `(ℤ/2ⁿ)((t))` one has `2ⁿ = 0`. -/
theorem two_pow_eq_zero_laurent (n : ℕ) : (2 : LaurentSeries (ZMod (2 ^ n))) ^ n = 0 := by
  have h : ((2 ^ n : ℕ) : ZMod (2 ^ n)) = 0 := ZMod.natCast_self _
  have h2 := congrArg (HahnSeries.C : ZMod (2 ^ n) →+* LaurentSeries (ZMod (2 ^ n))) h
  rw [map_natCast, map_zero] at h2
  rw [← h2]
  push_cast
  rfl

end OModel

/-- **Tex 2747–2748, 3728 (PROVED).**  For every `y ∈ 𝒪`, `1 + 2y` is a unit of `𝒪`: in each
component `(ℤ/2ⁿ)((t))` the element `2y` is nilpotent, since `(2y)ⁿ = 2ⁿyⁿ = 0`. -/
theorem isUnit_one_add_two_mul_OO (y : OO) : IsUnit (1 + 2 * y) := by
  apply isUnit_of_forall_isUnit_component
  intro n
  show IsUnit (1 + 2 * (y : ∀ n, LaurentSeries (ZMod (2 ^ n))) n)
  apply IsNilpotent.isUnit_one_add
  exact ⟨n, by rw [mul_pow, two_pow_eq_zero_laurent, zero_mul]⟩

/-- The reduction `𝒪 → 𝒪/2^M = (ℤ/2^M)((t))`: evaluation of a compatible sequence at `M`
(tex 2747–2748, 3728). -/
noncomputable def proj (M : ℕ) : OO →+* LaurentSeries (ZMod (2 ^ M)) :=
  (Pi.evalRingHom (fun n => LaurentSeries (ZMod (2 ^ n))) M).comp OInf.subtype

/-- **Tex 2747–2748, 3728 (PROVED).**  `proj M` is evaluation at `M`. -/
theorem proj_apply (M : ℕ) (x : OO) : proj M x = (x : ∀ n, LaurentSeries (ZMod (2 ^ n))) M :=
  rfl

/-- **Tex 2747–2748, 3728 (PROVED).**  The reductions are compatible:
`redLaurent n (proj (n + 1) x) = proj n x`. -/
theorem redLaurent_proj (n : ℕ) (x : OO) : redLaurent n (proj (n + 1) x) = proj n x := x.2 n

/-- **Tex 2747–2748, 3728 (PROVED).**  Elements of the inverse limit `𝒪` are determined by
their reductions modulo all powers of `2`. -/
theorem OO_ext {x y : OO} (h : ∀ n, proj n x = proj n y) : x = y :=
  Subtype.ext (funext h)

/-- **Tex 2747–2748, 3728 (PROVED).**  An element of `𝒪` is a unit iff all its reductions
modulo `2ⁿ` are units of `(ℤ/2ⁿ)((t))`. -/
theorem isUnit_iff_forall_isUnit_proj (x : OO) : IsUnit x ↔ ∀ n, IsUnit (proj n x) :=
  ⟨fun hx n => hx.map (proj n), fun h => isUnit_of_forall_isUnit_component x h⟩

/-- **Tex 2747–2748, 3728 (PROVED).**  `2^M` vanishes modulo `2^M`: `proj M (2^M y) = 0`. -/
theorem proj_two_pow_mul (M : ℕ) (y : OO) : proj M (2 ^ M * y) = 0 := by
  rw [map_mul, map_pow, map_ofNat, two_pow_eq_zero_laurent, zero_mul]

/-- **Tex 2747–2748, 3728 (PROVED).**  The reduction modulo `2^M` of the image of `a ∈ Λ` is
the power series `a mod 2^M`, viewed in `(ℤ/2^M)((t))`. -/
theorem proj_algebraMap (M : ℕ) (a : PowerSeries ℤ_[2]) :
    proj M (algebraMap _ OO a) =
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map (PadicInt.toZModPow M) a) := rfl

/-- **Tex 2747–2748, 3728 (PROVED).**  The reduction modulo `2^M` of `t⁻¹` is the Laurent
monomial `t⁻¹ = HahnSeries.single (-1) 1`. -/
theorem proj_tInv (M : ℕ) : proj M tInv = HahnSeries.single (-1) 1 := rfl

/-- **Tex 2747–2748, 3728 (PROVED).**  Non-degeneracy: the structure map `Λ = ℤ₂[[t]] → 𝒪` is
injective (a power series over `ℤ₂` all of whose reductions modulo `2ⁿ` vanish is zero). -/
theorem lamToO_injective : Function.Injective lamToO := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine PowerSeries.ext fun k => ?_
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have h1 : lamComp n a = 0 := by
    have := congrArg (proj n) ha
    rw [map_zero] at this
    exact this
  have h2 : PowerSeries.map (PadicInt.toZModPow n) a = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by rw [map_zero]; exact h1)
  have h3 := congrArg (PowerSeries.coeff k) h2
  simpa [PowerSeries.coeff_map] using h3

/-- `𝒪` is a nontrivial ring, since `Λ` embeds into it (`lamToO_injective`). -/
instance : Nontrivial OO := lamToO_injective.nontrivial

/-- **Tex 2747–2748, 3728 (PROVED).**  Coefficient form of the pole bounds.  If
`y ≡ t^{-L} a (mod 2^M)` in `𝒪` with `a ∈ Λ`, then the reduction of `y` modulo `2^M` has no
Laurent term below degree `-L`. -/
theorem coeff_proj_eq_zero_of_mem (M L : ℕ) (y : OO) (a : PowerSeries ℤ_[2])
    (hy : y - tInv ^ L * algebraMap _ OO a ∈ Ideal.span {(2 : OO) ^ M}) (i : ℤ)
    (hi : i < -(L : ℤ)) : (proj M y).coeff i = 0 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy
  have hy' : y = tInv ^ L * algebraMap _ OO a + 2 ^ M * c := by rw [mul_comm _ c, hc]; ring
  have h : proj M y = HahnSeries.single (-(L : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map (PadicInt.toZModPow M) a) := by
    rw [hy', map_add, map_mul, map_pow, proj_tInv, proj_algebraMap, proj_two_pow_mul, add_zero,
      HahnSeries.single_pow]
    simp
  rw [h, HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  split_ifs with h'
  · rfl
  · exact absurd (by omega) h'

/-! ## The model is the `2`-adic completion of `Λ_{(2)}`

The remaining results confirm that `OO` has the defining properties of `𝒪 = (Λ_{(2)})^`
(tex 2747–2748, 3728): elements of `Λ` outside `(2)` become units, `𝒪/2^M = (ℤ/2^M)((t))`,
`𝒪` is `2`-adically complete and separated, and `𝒪` is an integral domain. -/

/-- **Tex 2747–2748, 3728 (PROVED).**  Localization property: every element of `Λ` outside the
prime `(2)` becomes a unit in `𝒪`, so `Λ → 𝒪` factors through `Λ_{(2)}`.  Such an element is
`2b + tᵏu` with `u ∈ Λˣ`, which is `tᵏu · (1 + 2 · (tᵏu)⁻¹ b)` in `𝒪`. -/
theorem isUnit_algebraMap_of_not_mem_span_two (a : PowerSeries ℤ_[2])
    (ha : a ∉ Ideal.span {(2 : PowerSeries ℤ_[2])}) :
    IsUnit (algebraMap (PowerSeries ℤ_[2]) OO a) := by
  classical
  have h2C : PowerSeries.C (2 : ℤ_[2]) = 2 := map_ofNat PowerSeries.C 2
  have hex : ∃ k, ¬ (2 : ℤ_[2]) ∣ PowerSeries.coeff k a := by
    by_contra h
    push Not at h
    apply ha
    choose c hc using h
    rw [Ideal.mem_span_singleton]
    refine ⟨PowerSeries.mk c, ?_⟩
    ext k
    rw [← h2C, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc k]
  set k := Nat.find hex with hk_def
  have hk : ¬ (2 : ℤ_[2]) ∣ PowerSeries.coeff k a := Nat.find_spec hex
  have hlt : ∀ j < k, (2 : ℤ_[2]) ∣ PowerSeries.coeff j a := fun j hj =>
    not_not.mp (Nat.find_min hex hj)
  choose! c hc using hlt
  set b : PowerSeries ℤ_[2] := PowerSeries.mk fun j => if j < k then c j else 0 with hb
  set u : PowerSeries ℤ_[2] := PowerSeries.mk fun j => PowerSeries.coeff (j + k) a with hu_def
  have hdec : a = 2 * b + PowerSeries.X ^ k * u := by
    refine PowerSeries.ext fun j => ?_
    rw [map_add, ← h2C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', hb, hu_def,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    by_cases hj : j < k
    · simp only [hj, ite_true, show ¬ k ≤ j by omega, ite_false, add_zero]
      exact hc j hj
    · simp only [hj, ite_false, show k ≤ j by omega, ite_true, mul_zero, zero_add,
        Nat.sub_add_cancel (show k ≤ j by omega)]
  have hu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : PowerSeries.constantCoeff u = PowerSeries.coeff k a := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu_def, PowerSeries.coeff_mk,
        zero_add]
    rw [this, PadicInt.isUnit_iff]
    have h1 := PadicInt.norm_le_one (PowerSeries.coeff k a)
    have h2 : ¬ ‖PowerSeries.coeff k a‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast hk
    exact le_antisymm h1 (not_lt.mp h2)
  have hw : IsUnit (algebraMap (PowerSeries ℤ_[2]) OO (PowerSeries.X ^ k * u)) := by
    rw [map_mul, map_pow]; exact (isUnit_t.pow k).mul (hu.map _)
  obtain ⟨w, hw'⟩ := hw
  have key : algebraMap (PowerSeries ℤ_[2]) OO a =
      ↑w * (1 + 2 * (↑w⁻¹ * algebraMap (PowerSeries ℤ_[2]) OO b)) := by
    rw [hdec, map_add, map_mul, ← hw', map_ofNat]
    linear_combination (-2 * algebraMap (PowerSeries ℤ_[2]) OO b) * w.mul_inv
  rw [key]
  exact w.isUnit.mul (isUnit_one_add_two_mul_OO _)

namespace OModel

/-- **Tex 2747–2748, 3728 (PROVED).**  Iterated compatibility of a sequence in the inverse limit:
for `m ≤ n`, reducing the coefficients of the `n`-th component modulo `2^m` gives the `m`-th. -/
theorem cast_coeff_of_le (x : OO) {m n : ℕ} (h : m ≤ n) (i : ℤ) :
    (ZMod.cast (((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) n).coeff i) : ZMod (2 ^ m)) =
      ((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) m).coeff i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact ZMod.cast_id _ _
  | succ k ih =>
    rw [← ih]
    have h := congrArg (fun y => HahnSeries.coeff y i) (x.2 (m + k))
    simp only [redLaurent_coeff, ZMod.castHom_apply] at h
    rw [← h]
    have := RingHom.congr_fun (ZMod.castHom_comp (pow_dvd_pow 2 (Nat.le_add_right m k))
      (pow_dvd_pow 2 (Nat.le_succ (m + k))))
      (((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) (m + k + 1)).coeff i)
    simp only [RingHom.comp_apply, ZMod.castHom_apply] at this
    exact this.symm

/-- **Tex 2747–2748, 3728 (PROVED).**  Right multiplication by `2^M` acts on the coefficients of
a Laurent series. -/
theorem coeff_mul_two_pow {R : Type*} [CommRing R] (y : LaurentSeries R) (M : ℕ) (i : ℤ) :
    (y * (2 : LaurentSeries R) ^ M).coeff i = y.coeff i * 2 ^ M := by
  have h : (2 : LaurentSeries R) ^ M = HahnSeries.single 0 ((2 : R) ^ M) := by
    rw [← HahnSeries.C_apply, map_pow, map_ofNat]
  rw [h, HahnSeries.coeff_mul_single_zero]

/-- Division by `2^M`, `ℤ/2^{M+n} → ℤ/2ⁿ`, `z ↦ ⌊z.val / 2^M⌋`, as a zero-preserving map. -/
def divTwoPow (M n : ℕ) : ZeroHom (ZMod (2 ^ (M + n))) (ZMod (2 ^ n)) where
  toFun z := ((z.val / 2 ^ M : ℕ) : ZMod (2 ^ n))
  map_zero' := by simp

/-- The sequence `n ↦ x_{M+n} / 2^M` (coefficientwise). -/
noncomputable def divSeq (x : OO) (M : ℕ) : ∀ n : ℕ, LaurentSeries (ZMod (2 ^ n)) :=
  fun n => ((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) (M + n)).map (divTwoPow M n)

/-- **Tex 2747–2748, 3728 (PROVED).**  The sequence `divSeq x M` is compatible. -/
theorem divSeq_mem (x : OO) (M : ℕ) : divSeq x M ∈ OInf := by
  intro n
  ext i
  simp only [redLaurent_coeff, divSeq, HahnSeries.map_coeff, divTwoPow, ZeroHom.coe_mk,
    map_natCast]
  have h := congrArg (fun y => HahnSeries.coeff y i) (x.2 (M + n))
  simp only [redLaurent_coeff, ZMod.castHom_apply] at h
  rw [← h, ZMod.cast_eq_val, ZMod.val_natCast, pow_add 2 M n, Nat.mod_mul_right_div_self,
    ZMod.natCast_mod]
  rfl

end OModel

/-- **Tex 2747–2748, 3728 (PROVED).**  `𝒪/2^M = (ℤ/2^M)((t))`, kernel part: an element of `𝒪`
is divisible by `2^M` iff its reduction modulo `2^M` vanishes. -/
theorem proj_eq_zero_iff_mem (M : ℕ) (x : OO) :
    proj M x = 0 ↔ x ∈ Ideal.span {(2 : OO) ^ M} := by
  constructor
  · intro hx
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨divSeq x M, divSeq_mem x M⟩, ?_⟩
    apply OO_ext
    intro n
    rw [map_mul, map_pow, map_ofNat]
    show divSeq x M n * 2 ^ M = (x : ∀ n, LaurentSeries (ZMod (2 ^ n))) n
    ext i
    rw [coeff_mul_two_pow]
    simp only [divSeq, HahnSeries.map_coeff, divTwoPow, ZeroHom.coe_mk]
    have hdvd : 2 ^ M ∣ (((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) (M + n)).coeff i).val := by
      have h1 := cast_coeff_of_le x (Nat.le_add_right M n) i
      have h0 : ((x : ∀ n, LaurentSeries (ZMod (2 ^ n))) M).coeff i = 0 := by
        rw [← proj_apply, hx]; rfl
      rw [h0, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h1
      exact h1
    rw [← cast_coeff_of_le x (Nat.le_add_left n M) i, ZMod.cast_eq_val]
    conv_rhs => rw [← Nat.div_mul_cancel hdvd]
    push_cast
    rfl
  · intro hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [mul_comm]
    exact proj_two_pow_mul M c

/-- **Tex 2747–2748, 3728 (PROVED).**  The kernel of the reduction `𝒪 → (ℤ/2^M)((t))` is
`2^M 𝒪`. -/
theorem ker_proj (M : ℕ) : RingHom.ker (proj M) = Ideal.span {(2 : OO) ^ M} :=
  Ideal.ext fun x => (RingHom.mem_ker).trans (proj_eq_zero_iff_mem M x)

namespace OModel

/-- Lift of residues `ℤ/2^M → ℤ/2ⁿ` through the representative in `[0, 2^M)`. -/
def liftVal (M n : ℕ) : ZeroHom (ZMod (2 ^ M)) (ZMod (2 ^ n)) where
  toFun z := ((z.val : ℕ) : ZMod (2 ^ n))
  map_zero' := by simp

end OModel

/-- **Tex 2747–2748, 3728 (PROVED).**  The reduction `𝒪 → (ℤ/2^M)((t))` is surjective. -/
theorem proj_surjective (M : ℕ) : Function.Surjective (proj M) := by
  intro z
  refine ⟨⟨fun n => z.map (liftVal M n), fun n => ?_⟩, ?_⟩
  · ext i
    simp only [redLaurent_coeff, HahnSeries.map_coeff, liftVal, ZeroHom.coe_mk, map_natCast]
  · ext i
    show (z.map (liftVal M M)).coeff i = z.coeff i
    simp only [HahnSeries.map_coeff, liftVal, ZeroHom.coe_mk, ZMod.natCast_zmod_val]

/-- **Tex 2747–2748, 3728 (PROVED).**  `𝒪/2^M ≅ (ℤ/2^M)((t)) = Λ_{(2)}/2^M`. -/
noncomputable def quotTwoPowEquiv (M : ℕ) :
    (OO ⧸ Ideal.span {(2 : OO) ^ M}) ≃+* LaurentSeries (ZMod (2 ^ M)) :=
  (Ideal.quotEquivOfEq (ker_proj M).symm).trans
    (RingHom.quotientKerEquivOfSurjective (proj_surjective M))

/-- **Tex 2747–2748, 3728 (PROVED).**  Membership in `(2)^M • 𝒪` is vanishing modulo `2^M`. -/
theorem mem_pow_smul_top_iff (M : ℕ) (x : OO) :
    x ∈ (Ideal.span {(2 : OO)} ^ M • ⊤ : Submodule OO OO) ↔ proj M x = 0 := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, proj_eq_zero_iff_mem]

/-- **Tex 2747–2748, 3728 (PROVED).**  `𝒪` is `2`-adically complete and separated. -/
instance : IsAdicComplete (Ideal.span {(2 : OO)}) OO where
  haus' x hx := by
    apply OO_ext
    intro n
    have := hx n
    rw [SModEq.zero, mem_pow_smul_top_iff] at this
    rw [this, map_zero]
  prec' f hf := by
    refine ⟨⟨fun n => proj n (f n), fun n => ?_⟩, fun n => ?_⟩
    · show redLaurent n (proj (n + 1) (f (n + 1))) = proj n (f n)
      rw [redLaurent_proj]
      have := hf (Nat.le_succ n)
      rw [SModEq.sub_mem, mem_pow_smul_top_iff, map_sub, sub_eq_zero] at this
      exact this.symm
    · rw [SModEq.sub_mem, mem_pow_smul_top_iff, map_sub, sub_eq_zero]
      rfl


/-- **Tex 2747–2748, 3728 (PROVED).**  `2^N ≠ 0` in `𝒪`. -/
theorem two_pow_ne_zero_OO (N : ℕ) : (2 : OO) ^ N ≠ 0 := by
  intro h
  have h1 := congrArg (fun y => (proj (N + 1) y).coeff 0) h
  simp only [map_pow, map_ofNat, map_zero, HahnSeries.coeff_zero] at h1
  have h2 : (2 : LaurentSeries (ZMod (2 ^ (N + 1)))) ^ N =
      HahnSeries.single 0 ((2 : ZMod (2 ^ (N + 1))) ^ N) := by
    rw [← HahnSeries.C_apply, map_pow, map_ofNat]
  rw [h2, HahnSeries.coeff_single_same] at h1
  have h3 : ((2 ^ N : ℕ) : ZMod (2 ^ (N + 1))) = 0 := by exact_mod_cast h1
  rw [ZMod.natCast_eq_zero_iff] at h3
  have h4 := Nat.le_of_dvd (Nat.two_pow_pos N) h3
  have h5 := Nat.two_pow_pos N
  rw [pow_succ] at h4
  omega

/-- **Tex 2747–2748, 3728 (PROVED).**  Every nonzero element of `𝒪` is `2^M` times a unit. -/
theorem exists_eq_two_pow_mul_unit (y : OO) (hy : y ≠ 0) :
    ∃ (M : ℕ) (u : OOˣ), y = 2 ^ M * u := by
  classical
  have hex : ∃ n, proj n y ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (OO_ext fun n => by rw [h n, map_zero])
  have hN : proj (Nat.find hex) y ≠ 0 := Nat.find_spec hex
  have h0 : proj 0 y = 0 := by simpa using proj_two_pow_mul 0 y
  obtain ⟨M, hM⟩ : ∃ M, Nat.find hex = M + 1 := by
    refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h => hN ?_)
    rw [h]; exact h0
  rw [hM] at hN
  have hyM : proj M y = 0 := by
    have := Nat.find_min hex (show M < Nat.find hex by omega)
    push Not at this
    exact this
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ((proj_eq_zero_iff_mem M y).mp hyM)
  have hc1 : proj 1 c ≠ 0 := by
    intro hc
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp ((proj_eq_zero_iff_mem 1 c).mp hc)
    apply hN
    rw [show d * 2 ^ 1 * 2 ^ M = 2 ^ (M + 1) * d by ring]
    exact proj_two_pow_mul (M + 1) d
  have : Fact (Nat.Prime (2 ^ 1)) := ⟨by rw [pow_one]; exact Nat.prime_two⟩
  obtain ⟨w, hw⟩ := proj_surjective 1 (proj 1 c)⁻¹
  have hcw : proj 1 (c * w - 1) = 0 := by
    rw [map_sub, map_mul, hw, map_one, mul_inv_cancel₀ hc1, sub_self]
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp ((proj_eq_zero_iff_mem 1 _).mp hcw)
  have hunit : IsUnit (c * w) := by
    have : c * w = 1 + 2 * e := by linear_combination he.symm
    rw [this]; exact isUnit_one_add_two_mul_OO e
  exact ⟨M, (isUnit_of_mul_isUnit_left hunit).unit, by rw [IsUnit.unit_spec, mul_comm]⟩

/-- **Tex 2747–2748, 3728 (PROVED).**  `𝒪` has no zero divisors. -/
instance : NoZeroDivisors OO where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    by_contra h
    push Not at h
    obtain ⟨M, u, rfl⟩ := exists_eq_two_pow_mul_unit a h.1
    obtain ⟨M', u', rfl⟩ := exists_eq_two_pow_mul_unit b h.2
    have h1 : (2 : OO) ^ (M + M') * ↑(u * u') = 0 := by
      rw [← hab, pow_add, Units.val_mul]; ring
    exact two_pow_ne_zero_OO (M + M') ((Units.mul_left_eq_zero _).mp h1)

/-- **Tex 2747–2748, 3728 (PROVED).**  `𝒪` is an integral domain. -/
instance : IsDomain OO := NoZeroDivisors.to_isDomain _

end ZInQ.Manuscript.RC.Determinant
