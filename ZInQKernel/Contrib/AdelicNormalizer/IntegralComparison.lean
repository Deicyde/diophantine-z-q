import ZInQKernel.Contrib.AdelicNormalizer.PrimeEvaluation
import ZInQKernel.Contrib.AdelicNormalizer.ScalarExtension
import ZInQKernel.Contrib.AdelicNormalizer.Residue

/-!
# Integral comparison: the completed order and the rational order modulo three

1. `completedOrder` is exactly the full `Zhat`-span of the ordered order basis
   `GlueRepo.A1.e = (1, i, (1+j)/2, (i+ij)/2)`. Here `integralComb n` is the combination with
   coefficients `n : Fin 4 → Zhat`. It is written in quaternion coordinates with the scalar
   `half = algebraMap ℚ Af (1/2)` and equals `∑ k, n k • e k`, which is also the image of
   `∑ k, n k ⊗ e k` under the scalar-extension identity. In the reverse direction, the
   coordinates `x.re - x.imJ, x.imI - x.imK, 2 x.imJ, 2 x.imK` are integral at every place,
   the place `2` included. No integrality of `1/2` is used.
2. `rationalReduction : GlueRepo.A1.O →+* Residue.Residue3` reduces the integer coordinates of
   `comb`. It is surjective and its kernel is `3 O`, so `O ⧸ ker ≃+* Residue3`, and the unit
   group of `O ⧸ ker` has `72` elements. It agrees with `Residue.localReduction` after
   `rationalToLocal 3`.

This is a contribution, not an acceptance record.
-/

open Quaternion
open IsDedekindDomain
open scoped TensorProduct

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat
  QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

namespace G1.IntegralComparison

noncomputable section

/-! ### The completed order is the `Zhat`-span of the ordered basis -/

/-- The scalar `1/2` of the finite adeles (a scalar, not an integrality assumption). -/
def half : Af := algebraMap ℚ Af (1 / 2)

theorem two_mul_half : (2 : Af) * half = 1 := by
  rw [half, ← map_ofNat (algebraMap ℚ Af) 2, ← map_mul]
  norm_num

theorem scalarEval_half (v : Place) : scalarEval v half = 2⁻¹ := by
  rw [half, scalarEval_rat]
  simp

theorem mem_Zhat_iff (a : Af) : a ∈ Zhat ↔ ∀ v, ‖scalarEval v a‖ ≤ 1 :=
  Iff.rfl

/-- The local integer `a_v` of an integral finite adele. -/
def localInt (a : Zhat) (v : Place) : Zv v :=
  ⟨scalarEval v a, (mem_Zhat_iff _).1 a.2 v⟩

@[simp] theorem coe_localInt (a : Zhat) (v : Place) :
    (localInt a v : Qv v) = scalarEval v a :=
  rfl

/-- `n 0 • e 0 + n 1 • e 1 + n 2 • e 2 + n 3 • e 3`, written in quaternion coordinates. -/
def integralComb (n : Fin 4 → Zhat) : BA :=
  ⟨n 0 + n 2 * half, n 1 + n 3 * half, n 2 * half, n 3 * half⟩

theorem quaternionEval_integralComb (n : Fin 4 → Zhat) (v : Place) :
    quaternionEval v (integralComb n) =
      GlueVigneras.combp (primeAt v).1 (fun k => localInt (n k) v) := by
  ext <;>
    simp [quaternionEval, quaternionMap, integralComb, GlueVigneras.combp, scalarEval_half] <;>
    ring

theorem integralComb_mem (n : Fin 4 → Zhat) : integralComb n ∈ completedOrder :=
  fun v => ⟨fun k => localInt (n k) v, (quaternionEval_integralComb n v).symm⟩

/-- Coordinates in the ordered order basis; `2` is a scalar, no division is used. -/
def orderCoord (x : BA) : Fin 4 → Af :=
  ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]

theorem scalarEval_orderCoord (x : BA) (v : Place) (k : Fin 4) :
    scalarEval v (orderCoord x k) = GlueVigneras.coord (primeAt v).1 (quaternionEval v x) k := by
  fin_cases k <;> simp [orderCoord, GlueVigneras.coord, quaternionEval, quaternionMap, map_ofNat]

theorem orderCoord_mem {x : BA} (hx : x ∈ completedOrder) (k : Fin 4) :
    orderCoord x k ∈ Zhat := by
  intro v
  change ‖scalarEval v (orderCoord x k)‖ ≤ 1
  rw [scalarEval_orderCoord]
  exact (GlueVigneras.mem_Op_iff_coord _ _).1 (hx v) k

theorem orderCoord_integralComb (n : Fin 4 → Zhat) (k : Fin 4) :
    orderCoord (integralComb n) k = n k := by
  have h := two_mul_half
  fin_cases k
  · simp [orderCoord, integralComb]
  · simp [orderCoord, integralComb]
  · change 2 * ((n 2 : Af) * half) = n 2
    linear_combination (n 2 : Af) * h
  · change 2 * ((n 3 : Af) * half) = n 3
    linear_combination (n 3 : Af) * h

theorem integralComb_injective : Function.Injective integralComb := by
  intro n m h
  funext k
  apply Subtype.ext
  rw [← orderCoord_integralComb n k, ← orderCoord_integralComb m k, h]

theorem integralComb_orderCoord {x : BA} (hx : x ∈ completedOrder) :
    integralComb (fun k => ⟨orderCoord x k, orderCoord_mem hx k⟩) = x := by
  have h := two_mul_half
  apply QuaternionAlgebra.ext
  · change (x.re - x.imJ) + 2 * x.imJ * half = x.re
    linear_combination x.imJ * h
  · change (x.imI - x.imK) + 2 * x.imK * half = x.imI
    linear_combination x.imK * h
  · change 2 * x.imJ * half = x.imJ
    linear_combination x.imJ * h
  · change 2 * x.imK * half = x.imK
    linear_combination x.imK * h

/-- **Integral semantic identity.** -/
theorem mem_completedOrder_iff (x : BA) :
    x ∈ completedOrder ↔ ∃ n : Fin 4 → Zhat, integralComb n = x :=
  ⟨fun hx => ⟨_, integralComb_orderCoord hx⟩, fun ⟨n, hn⟩ => hn ▸ integralComb_mem n⟩

theorem range_integralComb : Set.range integralComb = (completedOrder : Set BA) :=
  Set.ext fun x => (mem_completedOrder_iff x).symm

/-- `integralComb n = ∑ k, n k • e k`, with the embedded actual order basis. -/
theorem integralComb_eq_sum (n : Fin 4 → Zhat) :
    integralComb n = ∑ k, (n k : Af) • ScalarExtension.rationalToAdelic (GlueRepo.A1.e k) := by
  ext <;> simp [integralComb, half, Fin.sum_univ_four, GlueRepo.A1.e]

/-- The same element as the image of `∑ k, n k ⊗ e k` under the scalar-extension identity. -/
theorem integralComb_eq_scalarExtension (n : Fin 4 → Zhat) :
    integralComb n =
      ScalarExtension.scalarExtensionEquiv (∑ k, (n k : Af) ⊗ₜ[ℚ] GlueRepo.A1.e k) := by
  simp only [map_sum, ScalarExtension.scalarExtensionEquiv_apply,
    ScalarExtension.toBA_tmul_eq_smul]
  exact integralComb_eq_sum n

theorem mem_completedOrder_iff_tensor (x : BA) :
    x ∈ completedOrder ↔ ∃ n : Fin 4 → Zhat,
      ScalarExtension.scalarExtensionEquiv (∑ k, (n k : Af) ⊗ₜ[ℚ] GlueRepo.A1.e k) = x := by
  simp only [← integralComb_eq_scalarExtension]
  exact mem_completedOrder_iff x

/-! ### The rational order modulo three -/

/-- Rational coordinates in the ordered basis. -/
def ratCoordQ (x : GlueRepo.A1.B) : Fin 4 → ℚ :=
  ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]

theorem ratCoordQ_comb (n : Fin 4 → ℤ) (k : Fin 4) :
    ratCoordQ (GlueRepo.A1.comb n) k = (n k : ℚ) := by
  fin_cases k <;> simp [ratCoordQ, GlueRepo.A1.comb] <;> ring

theorem comb_injective : Function.Injective GlueRepo.A1.comb := by
  intro n m h
  funext k
  have := ratCoordQ_comb n k
  rw [h, ratCoordQ_comb] at this
  exact_mod_cast this.symm

theorem comb_add (n m : Fin 4 → ℤ) :
    GlueRepo.A1.comb (n + m) = GlueRepo.A1.comb n + GlueRepo.A1.comb m := by
  ext <;> simp [GlueRepo.A1.comb] <;> ring

theorem comb_zero : GlueRepo.A1.comb 0 = 0 := by
  ext <;> simp [GlueRepo.A1.comb]

theorem comb_one : GlueRepo.A1.comb ![1, 0, 0, 0] = 1 := by
  ext <;> simp [GlueRepo.A1.comb]

theorem comb_three_mul (m : Fin 4 → ℤ) :
    GlueRepo.A1.comb (fun k => 3 * m k) = 3 * GlueRepo.A1.comb m := by
  ext <;> simp [GlueRepo.A1.comb] <;> ring

/-- The (unique) integer coordinates of an element of `O`. -/
def ratCoord (x : GlueRepo.A1.O) : Fin 4 → ℤ :=
  Classical.choose (x.2 : (x : GlueRepo.A1.B) ∈ Set.range GlueRepo.A1.comb)

theorem comb_ratCoord (x : GlueRepo.A1.O) : GlueRepo.A1.comb (ratCoord x) = x :=
  Classical.choose_spec (x.2 : (x : GlueRepo.A1.B) ∈ Set.range GlueRepo.A1.comb)

theorem ratCoord_eq_of (x : GlueRepo.A1.O) (n : Fin 4 → ℤ)
    (h : (x : GlueRepo.A1.B) = GlueRepo.A1.comb n) : ratCoord x = n :=
  comb_injective (by rw [comb_ratCoord, h])

theorem ratCoord_mul (x y : GlueRepo.A1.O) :
    ratCoord (x * y) = GlueRepo.A1.combMul (ratCoord x) (ratCoord y) := by
  apply ratCoord_eq_of
  rw [← GlueRepo.A1.comb_mul, comb_ratCoord, comb_ratCoord]
  rfl

theorem ratCoord_add (x y : GlueRepo.A1.O) :
    ratCoord (x + y) = ratCoord x + ratCoord y := by
  apply ratCoord_eq_of
  rw [comb_add, comb_ratCoord, comb_ratCoord]
  rfl

/-- Reduction of the actual rational order modulo three. -/
def rationalReduction : GlueRepo.A1.O →+* Residue.Residue3 where
  toFun x := ⟨GlueRepo.A1.red3 (ratCoord x)⟩
  map_one' := by
    apply Residue.Residue3.ext
    rw [ratCoord_eq_of 1 ![1, 0, 0, 0] comb_one.symm]
    funext k
    fin_cases k <;> simp [GlueRepo.A1.red3, GlueRepo.A1.one3]
  map_mul' x y := by
    apply Residue.Residue3.ext
    rw [ratCoord_mul, GlueRepo.A1.red3_mul]
    rfl
  map_zero' := by
    apply Residue.Residue3.ext
    rw [ratCoord_eq_of 0 0 comb_zero.symm]
    funext k
    simp [GlueRepo.A1.red3]
  map_add' x y := by
    apply Residue.Residue3.ext
    rw [ratCoord_add]
    funext k
    simp [GlueRepo.A1.red3]

@[simp] theorem coords_rationalReduction (x : GlueRepo.A1.O) (k : Fin 4) :
    (rationalReduction x).coords k = (ratCoord x k : ZMod 3) :=
  rfl

theorem rationalReduction_surjective : Function.Surjective rationalReduction := by
  intro r
  refine ⟨⟨GlueRepo.A1.comb (fun k => ((r.coords k).val : ℤ)), ⟨_, rfl⟩⟩, ?_⟩
  apply Residue.Residue3.ext
  change GlueRepo.A1.red3 (ratCoord _) = r.coords
  rw [ratCoord_eq_of _ (fun k => ((r.coords k).val : ℤ)) rfl]
  funext k
  simp [GlueRepo.A1.red3]

/-- The kernel of the rational reduction is `3 O`. -/
theorem mem_ker_rationalReduction_iff (x : GlueRepo.A1.O) :
    x ∈ RingHom.ker rationalReduction ↔
      ∃ y ∈ GlueRepo.A1.O, (x : GlueRepo.A1.B) = 3 * y := by
  rw [RingHom.mem_ker, Residue.Residue3.ext_iff, funext_iff]
  constructor
  · intro h
    have hd : ∀ k, ∃ c : ℤ, ratCoord x k = 3 * c := fun k =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (ratCoord x k) 3).1 (h k)
    choose m hm using hd
    refine ⟨GlueRepo.A1.comb m, ⟨m, rfl⟩, ?_⟩
    rw [← comb_three_mul, ← comb_ratCoord x]
    congr 1
    funext k
    exact hm k
  · rintro ⟨y, ⟨m, rfl⟩, hx⟩
    rw [← comb_three_mul] at hx
    show ∀ k, ((ratCoord x k : ℤ) : ZMod 3) = 0
    rw [ratCoord_eq_of x _ hx]
    intro k
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (Dvd.intro (m k) (by norm_num))

/-- First isomorphism theorem: `O ⧸ 3O ≃+* Residue3`. -/
def rationalQuotientEquiv :
    GlueRepo.A1.O ⧸ RingHom.ker rationalReduction ≃+* Residue.Residue3 :=
  RingHom.quotientKerEquivOfSurjective rationalReduction_surjective

theorem card_units_rationalQuotient :
    Nat.card (GlueRepo.A1.O ⧸ RingHom.ker rationalReduction)ˣ = 72 :=
  (Nat.card_congr (Units.mapEquiv rationalQuotientEquiv.toMulEquiv).toEquiv).trans
    Residue.Residue3.card_units

theorem rationalToLocal_mem (x : GlueRepo.A1.O) : rationalToLocal 3 x ∈ localOrder 3 :=
  ⟨fun k => ((ratCoord x k : ℤ) : ℤ_[3]), by
    rw [← rationalToLocal_comb, comb_ratCoord]⟩

/-- Compatibility with the local reduction at three. -/
theorem rationalReduction_eq_localReduction (x : GlueRepo.A1.O) :
    rationalReduction x = Residue.localReduction ⟨rationalToLocal 3 x, rationalToLocal_mem x⟩ := by
  apply Residue.Residue3.ext
  funext k
  change ((ratCoord x k : ℤ) : ZMod 3) = PadicInt.toZMod (Residue.localCoord ⟨_, _⟩ k)
  rw [Residue.localCoord_eq_of _ (fun k => ((ratCoord x k : ℤ) : ℤ_[3]))
    (by change rationalToLocal 3 (x : GlueRepo.A1.B) = _
        rw [← comb_ratCoord x, rationalToLocal_comb])]
  simp

end

end G1.IntegralComparison
