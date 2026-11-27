import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.GeomFree5
import Mathlib

/-!
# `κ₅ : M₂(F₅) ≃+* O / 5 O`

Modulo `5 O`, the elements `E = e5`, `X`, `Y` of `O` and `F = 1 - E` satisfy the relations of
the matrix units `e₁₁`, `e₁₂`, `e₂₁`, `e₂₂` of `M₂(F₅)`: from `E² = E`, `E X = X`, `E Y = 0`,
`X E = 0`, `X Y = E` and `E + Y X = 1` one gets `e_{ij} e_{kl} = δ_{jk} e_{il}` for all sixteen
products. Hence `(a b; c d) ↦ a E + b X + c Y + d F` is a ring homomorphism
`M₂(F₅) → O / 5 O`. It is injective because `M₂(F₅)` is a simple ring and `O / 5 O` is
nontrivial, and both sides have `625` elements, so it is an isomorphism `κ₅`.

Since `κ₅(e₂₂) = 1 - e5`, the condition `(1 - e5) δ = 1 - e5` defining Buzzard's group `H`
reads `e₂₂ κ₅⁻¹(δ) = e₂₂`, i.e. the second row of `κ₅⁻¹(δ)` is `(0, 1)`.
-/

set_option autoImplicit false
noncomputable section

open LeafQM LeafQM.AV

namespace Y3Buzzard.XDV15

/-! ## `O / 5 O` is an `F₅`-algebra -/

theorem natCast_five_OMod5 : ((5 : ℕ) : Y3OrderMod.OMod 5) = 0 := by
  have h : (((5 : ℕ) : O) : Y3OrderMod.OMod 5) = ((0 : O) : Y3OrderMod.OMod 5) :=
    Y3OrderMod.coe_eq_coe_iff.2 ⟨1, by rw [sub_zero, mul_one]⟩
  rw [RingCon.coe_natCast, RingCon.coe_zero] at h
  exact h

theorem nontrivial_OMod5 : Nontrivial (Y3OrderMod.OMod 5) := by
  have : Finite (Y3OrderMod.OMod 5) := Y3OrderMod.finite_OMod 5 (by norm_num)
  exact Finite.one_lt_card_iff_nontrivial.1 (by rw [GF5.card_OMod5]; norm_num)

attribute [local instance] nontrivial_OMod5

theorem charP_OMod5 : CharP (Y3OrderMod.OMod 5) 5 :=
  (CharP.charP_iff_prime_eq_zero (by norm_num)).2 natCast_five_OMod5

attribute [local instance] charP_OMod5

/-- The scalars `F₅ → O / 5 O`. -/
def sc5 : ZMod 5 →+* Y3OrderMod.OMod 5 := ZMod.castHom (dvd_refl 5) _

/-- Scalars are central. -/
theorem sc5_comm (a : ZMod 5) (r : Y3OrderMod.OMod 5) : r * sc5 a = sc5 a * r := by
  rw [← ZMod.natCast_zmod_val a, map_natCast]
  exact (Nat.cast_comm _ _).symm

theorem sc5_mul_sc5 (a b : ZMod 5) (u v : Y3OrderMod.OMod 5) :
    sc5 a * u * (sc5 b * v) = sc5 (a * b) * (u * v) := by
  rw [map_mul, mul_assoc, ← mul_assoc u, sc5_comm b u]
  simp only [mul_assoc]

/-! ## Matrix units in `O / 5 O` -/

/-- The class of `E = e5`, the image of `e₁₁`. -/
def cE : Y3OrderMod.OMod 5 := ((GF5.mE : O) : Y3OrderMod.OMod 5)

/-- The class of `X`, the image of `e₁₂`. -/
def cX : Y3OrderMod.OMod 5 := ((GF5.mX : O) : Y3OrderMod.OMod 5)

/-- The class of `Y`, the image of `e₂₁`. -/
def cY : Y3OrderMod.OMod 5 := ((GF5.mY : O) : Y3OrderMod.OMod 5)

/-- `F = 1 - E`, the image of `e₂₂`. -/
def cF : Y3OrderMod.OMod 5 := 1 - cE

theorem coe_eq_of_rel {a b : O} (h : ∃ c : O, a - b = ((5 : ℕ) : O) * c) :
    ((a : O) : Y3OrderMod.OMod 5) = ((b : O) : Y3OrderMod.OMod 5) :=
  Y3OrderMod.coe_eq_coe_iff.2 h

theorem cE_mul_cE : cE * cE = cE := by
  have h := coe_eq_of_rel GF5.rel_EE
  rw [RingCon.coe_mul] at h
  exact h

theorem cE_mul_cX : cE * cX = cX := by
  have h := coe_eq_of_rel GF5.rel_EX
  rw [RingCon.coe_mul] at h
  exact h

theorem cE_mul_cY : cE * cY = 0 := by
  have h := coe_eq_of_rel GF5.rel_EY
  rw [RingCon.coe_mul, RingCon.coe_zero] at h
  exact h

theorem cX_mul_cE : cX * cE = 0 := by
  have h := coe_eq_of_rel GF5.rel_XE
  rw [RingCon.coe_mul, RingCon.coe_zero] at h
  exact h

theorem cX_mul_cY : cX * cY = cE := by
  have h := coe_eq_of_rel GF5.rel_XY
  rw [RingCon.coe_mul] at h
  exact h

theorem cE_add_cY_mul_cX : cE + cY * cX = 1 := by
  have h := coe_eq_of_rel GF5.rel_EYX
  rw [RingCon.coe_add, RingCon.coe_mul, RingCon.coe_one] at h
  exact h

theorem cY_mul_cX : cY * cX = cF := by
  rw [cF, ← cE_add_cY_mul_cX]
  abel

theorem cX_mul_cX : cX * cX = 0 := by
  calc cX * cX = cX * (cE * cX) := by rw [cE_mul_cX]
    _ = 0 := by rw [← mul_assoc, cX_mul_cE, zero_mul]

theorem cY_mul_cE : cY * cE = cY := by
  have h := congrArg (· * cY) cE_add_cY_mul_cX
  simp only [add_mul, one_mul, mul_assoc, cE_mul_cY, cX_mul_cY, zero_add] at h
  exact h

theorem cY_mul_cY : cY * cY = 0 := by
  calc cY * cY = cY * cE * cY := by rw [cY_mul_cE]
    _ = 0 := by rw [mul_assoc, cE_mul_cY, mul_zero]

theorem cE_mul_cF : cE * cF = 0 := by rw [cF, mul_sub, mul_one, cE_mul_cE, sub_self]

theorem cX_mul_cF : cX * cF = cX := by rw [cF, mul_sub, mul_one, cX_mul_cE, sub_zero]

theorem cY_mul_cF : cY * cF = 0 := by rw [cF, mul_sub, mul_one, cY_mul_cE, sub_self]

theorem cF_mul_cE : cF * cE = 0 := by rw [cF, sub_mul, one_mul, cE_mul_cE, sub_self]

theorem cF_mul_cX : cF * cX = 0 := by rw [cF, sub_mul, one_mul, cE_mul_cX, sub_self]

theorem cF_mul_cY : cF * cY = cY := by rw [cF, sub_mul, one_mul, cE_mul_cY, sub_zero]

theorem cF_mul_cF : cF * cF = cF := by
  calc cF * cF = (1 - cE) * cF := rfl
    _ = cF := by rw [sub_mul, one_mul, cE_mul_cF, sub_zero]

/-! ## The isomorphism -/

/-- `(a b; c d) ↦ a E + b X + c Y + d F`. -/
def kap5 (M : Matrix (Fin 2) (Fin 2) (ZMod 5)) : Y3OrderMod.OMod 5 :=
  sc5 (M 0 0) * cE + sc5 (M 0 1) * cX + sc5 (M 1 0) * cY + sc5 (M 1 1) * cF

theorem kap5_one : kap5 1 = 1 := by
  simp only [kap5, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), map_one, map_zero, one_mul, zero_mul,
    add_zero, cF]
  abel

theorem kap5_zero : kap5 0 = 0 := by
  simp only [kap5, Matrix.zero_apply, map_zero, zero_mul, add_zero]

theorem kap5_add (M N : Matrix (Fin 2) (Fin 2) (ZMod 5)) : kap5 (M + N) = kap5 M + kap5 N := by
  simp only [kap5, Matrix.add_apply, map_add, add_mul]
  abel

theorem kap5_mul (M N : Matrix (Fin 2) (Fin 2) (ZMod 5)) : kap5 (M * N) = kap5 M * kap5 N := by
  simp only [kap5, Matrix.mul_apply, Fin.sum_univ_two, map_add, add_mul, mul_add]
  simp only [sc5_mul_sc5]
  simp only [cE_mul_cE, cE_mul_cX, cE_mul_cY, cE_mul_cF, cX_mul_cE, cX_mul_cX, cX_mul_cY,
    cX_mul_cF, cY_mul_cE, cY_mul_cX, cY_mul_cY, cY_mul_cF, cF_mul_cE, cF_mul_cX, cF_mul_cY,
    cF_mul_cF, mul_zero, add_zero, zero_add]
  abel

/-- `κ₅` as a ring homomorphism. -/
def kap5Hom : Matrix (Fin 2) (Fin 2) (ZMod 5) →+* Y3OrderMod.OMod 5 where
  toFun := kap5
  map_one' := kap5_one
  map_mul' := kap5_mul
  map_zero' := kap5_zero
  map_add' := kap5_add

theorem card_M2F5 : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod 5)) = 625 := by
  change Nat.card (Fin 2 → Fin 2 → ZMod 5) = 625
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin]
  norm_num

/-- `κ₅` is bijective: injective as `M₂(F₅)` is simple, and both sides have `625` elements. -/
theorem kap5Hom_bijective : Function.Bijective kap5Hom := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (Y3OrderMod.OMod 5) := Y3OrderMod.finite_OMod 5 (by norm_num)
  exact (Nat.bijective_iff_injective_and_card kap5Hom).2
    ⟨RingHom.injective kap5Hom, card_M2F5.trans GF5.card_OMod5.symm⟩

/-- `κ₅ : M₂(F₅) ≃+* O / 5 O`, with `e₁₁ ↦ E`, `e₁₂ ↦ X`, `e₂₁ ↦ Y`, `e₂₂ ↦ 1 - E`. -/
def kappa5 : Matrix (Fin 2) (Fin 2) (ZMod 5) ≃+* Y3OrderMod.OMod 5 :=
  RingEquiv.ofBijective kap5Hom kap5Hom_bijective

theorem kappa5_apply (M : Matrix (Fin 2) (Fin 2) (ZMod 5)) : kappa5 M = kap5 M :=
  RingEquiv.ofBijective_apply _ _ M

theorem kappa5_e11 : kappa5 (Matrix.of ![![1, 0], ![0, 0]]) = ((e5 : O) : Y3OrderMod.OMod 5) := by
  rw [kappa5_apply]
  simp [kap5, cE, GF5.mE]

/-- `κ₅(e₂₂) = 1 - e5`. -/
theorem kappa5_e22 :
    kappa5 (Matrix.of ![![0, 0], ![0, 1]]) = ((f5 : O) : Y3OrderMod.OMod 5) := by
  rw [kappa5_apply, f5, RingCon.coe_sub, RingCon.coe_one]
  simp [kap5, cF, cE, GF5.mE]

/-- Buzzard's `H` is the group of units whose second row under `κ₅⁻¹` is `(0, 1)`. -/
theorem mem_H5_iff (δ : Y3OrderMod.G 5) :
    δ ∈ H5 ↔ (kappa5.symm (δ : Y3OrderMod.OMod 5)) 1 0 = 0 ∧
      (kappa5.symm (δ : Y3OrderMod.OMod 5)) 1 1 = 1 := by
  obtain ⟨M, hM⟩ : ∃ M, kappa5.symm (δ : Y3OrderMod.OMod 5) = M := ⟨_, rfl⟩
  have hδ : (δ : Y3OrderMod.OMod 5) = kappa5 M := by rw [← hM, RingEquiv.apply_symm_apply]
  rw [hM]
  show ((f5 : O) : Y3OrderMod.OMod 5) * (δ : Y3OrderMod.OMod 5) =
    ((f5 : O) : Y3OrderMod.OMod 5) ↔ _
  rw [hδ, ← kappa5_e22, ← map_mul, kappa5.injective.eq_iff]
  constructor
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h10 h11
    exact ⟨h10, h11⟩
  · rintro ⟨h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]

end Y3Buzzard.XDV15
