import ZInQKernel.Contrib.OneProof.TYZProp23Printed

/-!
# tyz-genus: an explicit finite idele in the class of an ideal

For a nonzero `α ∈ K_n = ℚ(√−n)` and `m ≥ 1`, `aK n m α = E·α + (1 − E)`, with `E` the image in `𝔸ᶠ_{K_n}` of the
idempotent `eDiv m ∈ 𝔸ᶠ_ℚ` supported at the primes dividing `m`: the idele equal to `α` at the places above the
primes of `m` and to `1` elsewhere.

* `piQ_tauHat_aK`: its image `τ̂(aK)` in `B̂ = ℍ[𝔸ᶠ_ℚ]` is `τ(α)` at the places dividing `m` and `1` elsewhere;
* `toClassGroup_aKU`: if `(α) = I·M` with `M + (N I) = O`, then for `m = N I` the class of `aK` is `[I]`.
-/

set_option linter.style.longLine false
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof
open IsDedekindDomain NumberField
open scoped Quaternion TensorProduct FiniteAdeleExtension nonZeroDivisors
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The idempotent of `𝔸ᶠ_ℚ` supported at the primes dividing `m`. -/
def eDiv (m : ℕ) : AQ :=
  ⟨fun w => if (Pw w : ℕ) ∣ m then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem eDiv_apply (m : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (eDiv m) w = if (Pw w : ℕ) ∣ m then 1 else 0 := rfl

theorem ev_eDiv (m : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ev w (eDiv m) = if (Pw w : ℕ) ∣ m then 1 else 0 := by
  rw [ev_apply, eDiv_apply]; split_ifs <;> simp

theorem eDiv_mul_self (m : ℕ) : eDiv m * eDiv m = eDiv m := by
  apply RestrictedProduct.ext
  intro w
  change eDiv m w * eDiv m w = eDiv m w
  rw [eDiv_apply]
  split_ifs <;> simp

variable {n : ℕ} [NeZero n]

/-- `𝔸ᶠ_{K_n}`. -/
abbrev AK (n : ℕ) [NeZero n] : Type := FiniteAdeleRing (𝓞 (QNeg n)) (QNeg n)

/-- The image of `eDiv m` in `𝔸ᶠ_{K_n}`. -/
def EK (n : ℕ) [NeZero n] (m : ℕ) : AK n := algebraMap AQ (AK n) (eDiv m)

theorem EK_mul_self (m : ℕ) : EK n m * EK n m = EK n m := by
  rw [EK, ← map_mul, eDiv_mul_self]

/-- `aK = E·α + (1 − E)`. -/
def aK (n : ℕ) [NeZero n] (m : ℕ) (α : QNeg n) : AK n :=
  EK n m * algebraMap (QNeg n) (AK n) α + (1 - EK n m)

theorem aK_mul_aK_inv (m : ℕ) {α : QNeg n} (hα : α ≠ 0) : aK n m α * aK n m α⁻¹ = 1 := by
  have hE := EK_mul_self (n := n) m
  have hA : algebraMap (QNeg n) (AK n) α * algebraMap (QNeg n) (AK n) α⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα, map_one]
  unfold aK
  linear_combination (algebraMap (QNeg n) (AK n) α * algebraMap (QNeg n) (AK n) α⁻¹ -
    algebraMap (QNeg n) (AK n) α - algebraMap (QNeg n) (AK n) α⁻¹ + 1) * hE + EK n m * hA

/-- `aK` as a finite idele. -/
def aKU (n : ℕ) [NeZero n] (m : ℕ) (α : QNeg n) (hα : α ≠ 0) : (AK n)ˣ where
  val := aK n m α
  inv := aK n m α⁻¹
  val_inv := aK_mul_aK_inv m hα
  inv_val := by
    have := aK_mul_aK_inv (n := n) m (inv_ne_zero hα)
    rwa [inv_inv] at this

/-! ### `τ̂(aK)` -/

theorem tauHat_EK (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (m : ℕ) :
    tauHat n τ (EK n m) = algebraMap AQ ℍ[AQ] (eDiv m) := by
  change (AlgHom.liftEquiv ℚ AQ (QNeg n) ℍ[AQ] ((qι).comp τ))
      ((TauCeti.GlobalNumberFields.finiteAdeleBaseChangeAlgEquiv ℚ (QNeg n)).symm
        (algebraMap AQ (AK n) (eDiv m))) = _
  rw [AlgEquiv.commutes, AlgHom.commutes]

theorem tauHat_aK (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (m : ℕ) (α : QNeg n) :
    tauHat n τ (aK n m α) =
      algebraMap AQ ℍ[AQ] (eDiv m) * qι (τ α) + (1 - algebraMap AQ ℍ[AQ] (eDiv m)) := by
  rw [aK, map_add, map_mul, map_sub, map_one, tauHat_EK, tauHat_algebraMap]

theorem piQ_tauHat_aK (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (m : ℕ) (α : QNeg n) (w : HeightOneSpectrum (𝓞 ℚ)) :
    piQ w (tauHat n τ (aK n m α)) = if (Pw w : ℕ) ∣ m then qp (Pw w : ℕ) (τ α) else 1 := by
  rw [tauHat_aK, map_add, map_mul, map_sub, map_one, piQ_algebraMap, piQ_qι, ev_eDiv]
  split_ifs <;> simp

/-! ### The class of `aK` -/

theorem EK_apply (m : ℕ) (v : HeightOneSpectrum (𝓞 (QNeg n))) :
    (EK n m) v = if (Pw (v.under (𝓞 ℚ)) : ℕ) ∣ m then 1 else 0 := by
  rw [EK, algebraMap_finiteAdeleExtensionAlgebra, finiteAdeleExtension_apply, eDiv_apply]
  split_ifs <;> simp

theorem aK_apply (m : ℕ) (α : QNeg n) (v : HeightOneSpectrum (𝓞 (QNeg n))) :
    (aK n m α) v = if (Pw (v.under (𝓞 ℚ)) : ℕ) ∣ m then (α : v.adicCompletion (QNeg n)) else 1 := by
  change (EK n m) v * (algebraMap (QNeg n) (AK n) α) v + (1 - (EK n m) v) = _
  rw [EK_apply, FiniteAdeleRing.algebraMap_apply]
  split_ifs <;> simp

/-- `Pw(v ∩ ℚ) ∣ k ↔ k ∈ v`. -/
theorem Pw_under_dvd_iff (v : HeightOneSpectrum (𝓞 (QNeg n))) (k : ℕ) :
    (Pw (v.under (𝓞 ℚ)) : ℕ) ∣ k ↔ ((k : 𝓞 (QNeg n))) ∈ v.asIdeal := by
  rw [Pw_coe, Rat.HeightOneSpectrum.natGenerator_dvd_iff, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, hxk⟩
    have hx' : x = (k : 𝓞 ℚ) := by
      apply (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective
      rw [hxk, map_natCast]
    rw [hx', HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hx
    exact hx
  · intro hk
    refine ⟨(k : 𝓞 ℚ), ?_, map_natCast _ _⟩
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hk

theorem count_coe_eq_zero (v : HeightOneSpectrum (𝓞 (QNeg n))) {J : Ideal (𝓞 (QNeg n))} (hJ : J ≠ ⊥)
    (h : ¬ J ≤ v.asIdeal) : FractionalIdeal.count (QNeg n) v (J : FractionalIdeal (𝓞 (QNeg n))⁰ (QNeg n)) = 0 := by
  classical
  rw [FractionalIdeal.count_coe (QNeg n) v hJ]
  norm_cast
  by_contra hc
  apply h
  rw [← Ideal.dvd_iff_le]
  exact (Associates.count_ne_zero_iff_dvd hJ
    (Associates.irreducible_mk.mp v.associates_irreducible)).mp hc

/-- **The class of `aK`.** If `(α) = I M` with `M + (N I) = O`, the idele `aK (N I) α` has class `[I]`. -/
theorem toClassGroup_aKU {I : (Ideal (𝓞 (QNeg n)))⁰} {α : 𝓞 (QNeg n)} {M : Ideal (𝓞 (QNeg n))}
    (hα : ((α : QNeg n)) ≠ 0) (hspan : Ideal.span {α} = (I : Ideal (𝓞 (QNeg n))) * M)
    (hM : M ⊔ Ideal.span {((Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) : ℕ) : 𝓞 (QNeg n))} = ⊤) :
    FiniteAdeleRing.toClassGroup (𝓞 (QNeg n)) (QNeg n)
      (aKU n (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) (α : QNeg n) hα) = ClassGroup.mk0 I := by
  set m := Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) with hm
  have hI0 : (I : Ideal (𝓞 (QNeg n))) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hspan
    exact hα (by rw [hspan]; rfl)
  have hcount : ∀ v : HeightOneSpectrum (𝓞 (QNeg n)),
      FractionalIdeal.count (QNeg n) v
        ((FiniteAdeleRing.toFractionalIdeal (aKU n m (α : QNeg n) hα) :
          FractionalIdeal (𝓞 (QNeg n))⁰ (QNeg n))) =
      FractionalIdeal.count (QNeg n) v
        ((FractionalIdeal.mk0 (QNeg n) I : (FractionalIdeal (𝓞 (QNeg n))⁰ (QNeg n))ˣ) :
          FractionalIdeal (𝓞 (QNeg n))⁰ (QNeg n)) := by
    intro v
    rw [FiniteAdeleRing.count_coe_toFractionalIdeal, FiniteAdeleRing.adicOrd_def, FractionalIdeal.coe_mk0]
    change -WithZero.log (Valued.v ((aK n m (α : QNeg n)) v)) = _
    rw [aK_apply]
    split_ifs with hv
    · have hmv : ((m : 𝓞 (QNeg n))) ∈ v.asIdeal := (Pw_under_dvd_iff v m).mp hv
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← Units.val_mk0 hα,
        ← FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation, coe_toPrincipalIdeal,
        Units.val_mk0, show ((α : QNeg n)) = algebraMap (𝓞 (QNeg n)) (QNeg n) α from rfl,
        ← FractionalIdeal.coeIdeal_span_singleton, hspan, FractionalIdeal.coeIdeal_mul,
        FractionalIdeal.count_mul (QNeg n) v (by simpa using hI0) (by simpa using hM0),
        count_coe_eq_zero v hM0 (fun hle => ?_), add_zero]
      have htop : M ⊔ Ideal.span {((m : ℕ) : 𝓞 (QNeg n))} ≤ v.asIdeal :=
        sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hmv)
      rw [hM] at htop
      exact v.isPrime.ne_top (top_le_iff.mp htop)
    · rw [map_one, WithZero.log_one, neg_zero, count_coe_eq_zero v hI0 (fun hle => hv ?_)]
      exact (Pw_under_dvd_iff v m).mpr (hle (Ideal.absNorm_mem _))
  have hfi : FiniteAdeleRing.toFractionalIdeal (aKU n m (α : QNeg n) hα) = FractionalIdeal.mk0 (QNeg n) I := by
    rw [FractionalIdeal.finprod_unitOfPrime_zpow_count (FiniteAdeleRing.toFractionalIdeal _),
      FractionalIdeal.finprod_unitOfPrime_zpow_count (FractionalIdeal.mk0 (QNeg n) I)]
    simp only [hcount]
  rw [FiniteAdeleRing.toClassGroup_apply, hfi, ClassGroup.mk_mk0]

end ZInQ.Contrib.TYZGenusFold
