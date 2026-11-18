import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1a
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.NaturalStep

/-!
# E1a, part 4: `CorrectedIsEta` from the (4.7) data, with no new GLUE

The first input of E1a, `CorrectedIsEta` (`ũ_x = η_x u_{rel,x}` in `Frac 𝒪`), is discharged from
the support-triangle data of the common coordinate (4.7) at every address — RC0's
`CommonCoordinateTriangles` in its retained-naturality form `CommonCoordinateTrianglesN`
(`CommonCoordinate/NaturalStep.lean`), whose field `hutilde : ũ_x = χ(η) u_rel` is the definition
of the corrected coordinate (tex 4219–4222) and whose steps give (4.7)
(`commonCoordinate_h47_of_natural`, with RC15's `corrected_eq`).

The two coordinate worlds are `ℚ₂[[t]]` (the (4.7) data, through `χ`) and `Frac 𝒪` (the
clearing, through the sign evaluations `evK x`); they meet in `Λ[1/2]`, `Λ = ℤ₂[[t]]`:

* `ιQ : Λ → ℚ₂[[t]]` (coefficientwise `ℤ₂ ⊂ ℚ₂`), injective;
* `uTilde_eq_of_rep`: a representation `ũ_x = g_x / 2^{e_x}` is an identity in `ℚ₂[[t]]`;
  `uK_rep_indep`: the image `uK e g ∈ Frac 𝒪` does not depend on the representation;
* `urelK`: the relaxed coordinate in `Frac 𝒪`, `u_rel = η_x⁻¹ ũ_x` with `η_x = x(η_Λ) ∈ Λ^×`;
* **`correctedIsEta_of_triangles` (PROVED)**: for a universal correction `η_Λ ∈ Λ[G]` whose
  sign evaluations are units and agree with the (4.7) data's `χ(η)` at every address
  (`χ_x(η) = ιQ(x(η_Λ))`; for the (4.7) data over `R = Λ[G]` with `χ_x = ιQ ∘ x` this holds by
  definition), `CorrectedIsEta Dd F (φO η_Λ) urelK` holds, **and** `urelK x` is the image in
  `Frac 𝒪` of the (4.7) data's relaxed coordinate `u_rel` (`urel_eq_of_triangles`: equality of
  coefficients in `ℚ₂`). The pinned `u_rel` is thus the two-term relaxed coordinate of the (4.7)
  step models (`IsCoordOn` of `NaturalStep`), the input of `RelIsKM`.
* `isUnit_signEval_eta`: the sign evaluations of `η_Λ = ∏ (1 + v_q (1 + g_q))` are units of `Λ`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.ClearingComplex ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)

/-- `Λ = ℤ₂[[t]] → ℚ₂[[t]]`, coefficientwise. -/
abbrev ιQ : Lam →+* PowerSeries ℚ_[2] := PowerSeries.map (algebraMap ℤ_[2] ℚ_[2])

theorem coeff_ιQ (g : Lam) (j : ℕ) :
    PowerSeries.coeff j (ιQ g) = ((PowerSeries.coeff j g : ℤ_[2]) : ℚ_[2]) := by
  simp [ιQ]

theorem ιQ_injective : Function.Injective ιQ := by
  intro a b h
  ext j
  have := congrArg (PowerSeries.coeff j) h
  rw [coeff_ιQ, coeff_ιQ] at this
  exact_mod_cast this

/-- A representation `ũ_x = g_x / 2^{e_x}` as an identity of power series. -/
theorem uTilde_eq_of_rep {ℓ : ℕ} {Dd : RCData ℓ} {F : Family} {e : Addr F.b → ℕ}
    {g : Addr F.b → Lam} (hrep : UTildeRep Dd F e g) (x : Addr F.b) :
    Dd.uTilde F x = PowerSeries.C ((2 : ℚ_[2]) ^ e x)⁻¹ * ιQ (g x) := by
  ext j
  rw [PowerSeries.coeff_C_mul, coeff_ιQ, hrep x j, div_eq_inv_mul]

/-- Two representations give the same element of `Frac 𝒪`. -/
theorem uK_rep_indep {ℓ : ℕ} {Dd : RCData ℓ} {F : Family} {e e' : Addr F.b → ℕ}
    {g g' : Addr F.b → Lam} (h : UTildeRep Dd F e g) (h' : UTildeRep Dd F e' g') (x : Addr F.b) :
    uK (O := OO) (e x) (g x) = uK (e' x) (g' x) := by
  have hΛ : (2 : Lam) ^ e' x * g x = (2 : Lam) ^ e x * g' x := by
    apply ιQ_injective
    have h1 := uTilde_eq_of_rep h x
    have h2 := uTilde_eq_of_rep h' x
    rw [h1] at h2
    have hC : ∀ n : ℕ, ιQ ((2 : Lam) ^ n) = PowerSeries.C ((2 : ℚ_[2]) ^ n) := by
      intro n; simp [ιQ, map_pow, map_ofNat]
    rw [map_mul, map_mul, hC, hC]
    have hne : ∀ n : ℕ, (2 : ℚ_[2]) ^ n ≠ 0 := fun n => pow_ne_zero _ two_ne_zero
    calc PowerSeries.C ((2 : ℚ_[2]) ^ e' x) * ιQ (g x)
        = PowerSeries.C ((2 : ℚ_[2]) ^ e' x * (2 ^ e x)) *
            (PowerSeries.C ((2 : ℚ_[2]) ^ e x)⁻¹ * ιQ (g x)) := by
          rw [← mul_assoc, ← map_mul, mul_assoc, mul_inv_cancel₀ (hne _), mul_one]
      _ = PowerSeries.C ((2 : ℚ_[2]) ^ e' x * (2 ^ e x)) *
            (PowerSeries.C ((2 : ℚ_[2]) ^ e' x)⁻¹ * ιQ (g' x)) := by rw [h2]
      _ = PowerSeries.C ((2 : ℚ_[2]) ^ e x) * ιQ (g' x) := by
          rw [← mul_assoc, ← map_mul, mul_comm ((2 : ℚ_[2]) ^ e' x), mul_assoc,
            mul_inv_cancel₀ (hne _), mul_one]
  have h2O : ∀ n : ℕ, (2 : FractionRing OO) ^ n ≠ 0 := by
    intro n
    rw [show (2 : FractionRing OO) ^ n = algebraMap OO (FractionRing OO) ((2 : OO) ^ n) by
      rw [map_pow, map_ofNat]]
    exact (map_ne_zero_iff _ (IsFractionRing.injective OO (FractionRing OO))).mpr
      (Determinant.two_pow_ne_zero_OO n)
  unfold Determinant.uK
  rw [div_eq_div_iff (h2O _) (h2O _)]
  have := congrArg (fun a => algebraMap OO (FractionRing OO) (algebraMap Lam OO a)) hΛ
  simp only [map_mul, map_pow, map_ofNat] at this
  linear_combination this

/-- The relaxed coordinate in `Frac 𝒪`: `u_rel = η_x⁻¹ ũ_x`, from a representation `(e₀, g₀)` and
the units `η_x = x(η_Λ) ∈ Λ`. -/
def urelK {b : ℕ} (ηΛ : MonoidAlgebra Lam (SignGroup b))
    (hunit : ∀ x : Addr b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr b → ℕ)
    (g₀ : Addr b → Lam) (x : Addr b) : FractionRing OO :=
  uK (e₀ x) ((hunit x).unit⁻¹ * g₀ x)

/-- **`CorrectedIsEta` from the (4.7) data** (PROVED): with the universal correction `η_Λ`, any
representation `(e₀, g₀)` of `ũ`, and `urelK` the relaxed coordinate. -/
theorem correctedIsEta_of_triangles {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep Dd F e₀ g₀) :
    CorrectedIsEta Dd F (φO F.b ηΛ) (urelK ηΛ hunit e₀ g₀) := by
  intro e g hrep x
  rw [uK_rep_indep hrep h₀ x]
  have hev : evK (sgnChar x) (φO F.b ηΛ) =
      algebraMap OO (FractionRing OO) (algebraMap Lam OO ((hunit x).unit : Lam)) := by
    rw [Determinant.evK_apply, signEval_φO, IsUnit.unit_spec]
  rw [hev]
  unfold urelK Determinant.uK
  rw [mul_div_assoc', ← map_mul, ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]

/-- **The relaxed coordinate of the (4.7) data is `urelK`** (PROVED): if the (4.7) data at `x`
(`CommonCoordinateTrianglesN`, with `hutilde : ũ_x = χ(η) u_rel`) has `χ(η) = ιQ(x(η_Λ))`, then its
relaxed coordinate is `u_rel = 2^{-e₀} ιQ(η_x⁻¹ g₀)`, the element whose image in `Frac 𝒪` is
`urelK x`. -/
theorem urel_eq_of_triangles {ℓ : ℕ} {Dd : RCData ℓ} {F : Family}
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) {e₀ : Addr F.b → ℕ}
    {g₀ : Addr F.b → Lam} (h₀ : UTildeRep Dd F e₀ g₀) (x : Addr F.b)
    (T : CommonCoordinateTrianglesN Dd F x)
    (hcompat : T.chi (Central.eta T.Q T.v T.g) =
      ιQ (Determinant.signEval (sgnChar x) ηΛ)) :
    T.urel = PowerSeries.C ((2 : ℚ_[2]) ^ e₀ x)⁻¹ * ιQ ((hunit x).unit⁻¹ * g₀ x) := by
  have hut := T.hutilde
  rw [hcompat, uTilde_eq_of_rep h₀ x] at hut
  have hinv : ιQ (((hunit x).unit⁻¹ : Lamˣ) : Lam) *
      ιQ (Determinant.signEval (sgnChar x) ηΛ) = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  calc T.urel = ιQ (((hunit x).unit⁻¹ : Lamˣ) : Lam) *
        (ιQ (Determinant.signEval (sgnChar x) ηΛ) * T.urel) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [← hut, map_mul]; ring

/-- **`CorrectedIsEta` from the (4.7) data, pinned to its relaxed coordinate** (PROVED):
`CorrectedIsEta Dd F (φO η_Λ) urelK`, and at every address the (4.7) data's relaxed coordinate
`u_rel` is the element `2^{-e₀} ιQ(η_x⁻¹ g₀)` of `Λ[1/2]` whose image in `Frac 𝒪` is `urelK x`. -/
theorem correctedIsEta_of_triangles' {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (ηΛ : MonoidAlgebra Lam (SignGroup F.b))
    (hunit : ∀ x : Addr F.b, IsUnit (Determinant.signEval (sgnChar x) ηΛ)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep Dd F e₀ g₀)
    (T : ∀ x, CommonCoordinateTrianglesN Dd F x)
    (hcompat : ∀ x, (T x).chi (Central.eta (T x).Q (T x).v (T x).g) =
      ιQ (Determinant.signEval (sgnChar x) ηΛ)) :
    CorrectedIsEta Dd F (φO F.b ηΛ) (urelK ηΛ hunit e₀ g₀) ∧
      ∀ x, (T x).urel = PowerSeries.C ((2 : ℚ_[2]) ^ e₀ x)⁻¹ * ιQ ((hunit x).unit⁻¹ * g₀ x) :=
  ⟨correctedIsEta_of_triangles Dd F ηΛ hunit e₀ g₀ h₀,
    fun x => urel_eq_of_triangles ηΛ hunit h₀ x (T x) (hcompat x)⟩

/-- `1 + 2c` is a unit of `ℤ₂`. -/
theorem isUnit_one_add_two_mul_Z2 (c : ℤ_[2]) : IsUnit (1 + 2 * c) := by
  rw [PadicInt.isUnit_iff]
  have h2 : ‖(2 : ℤ_[2]) * c‖ < 1 := by
    rw [norm_mul]
    have hp : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
      have := PadicInt.norm_p (p := 2); exact_mod_cast this
    rw [hp]
    have := PadicInt.norm_le_one c
    nlinarith [norm_nonneg c]
  have h1 : ‖(1 : ℤ_[2])‖ = 1 := norm_one
  rw [PadicInt.norm_add_eq_max_of_ne (by rw [h1]; exact (ne_of_gt h2)), h1]
  exact max_eq_left h2.le

/-- **The sign evaluations of the universal correction are units of `Λ`**: for
`η_Λ = ∏_{q ∈ Q} (1 + v_q (1 + g_q))` with `x(g_q) = ±1`, `x(η_Λ) = ∏_{unused} (1 + 2 x(v_q))`. -/
theorem isUnit_signEval_eta {b : ℕ} {ι : Type} [DecidableEq ι] (Q : Finset ι)
    (v g : ι → MonoidAlgebra Lam (SignGroup b)) (x : Addr b)
    (hsign : ∀ q ∈ Q, Determinant.signEval (sgnChar x) (g q) = 1 ∨
      Determinant.signEval (sgnChar x) (g q) = -1) :
    IsUnit (Determinant.signEval (sgnChar x) (Central.eta Q v g)) := by
  classical
  have := Central.map_eta (Determinant.signEval (O := Lam) (sgnChar x)).toRingHom Q v g hsign
  change IsUnit ((Determinant.signEval (O := Lam) (sgnChar x)).toRingHom (Central.eta Q v g))
  rw [this]
  refine IsUnit.prod_iff.mpr fun q _ => ?_
  rw [PowerSeries.isUnit_iff_constantCoeff, map_add, map_mul, map_one, map_ofNat]
  exact isUnit_one_add_two_mul_Z2 _

end ZInQ.Contrib.CloudB3RC53.CoordLink
