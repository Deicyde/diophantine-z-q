/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_theta_mul (git blob 1549f54b06a3d84f9a8d6c9d46ea24de451514ab, sha256 421386d0529e55e38659843e9627e7a600b741ad9a8a9b8820b89353f8c586b3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_PhiGen_sum_qTwist_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_theta_mul.ModularCurve
end P2MW.S_ModularCurve_theta_mul.ModularCurve
namespace ModularCurve.PhiGen
end ModularCurve.PhiGen
namespace P2MW.S_ModularCurve_theta_mul.ModularCurve.PhiGen
end P2MW.S_ModularCurve_theta_mul.ModularCurve.PhiGen

namespace P2MW.S_ModularCurve_theta_mul

open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_theta_mul.ModularCurve
open _root_.ModularCurve.PhiGen
open _root_.P2MW.S_ModularCurve_theta_mul.ModularCurve.PhiGen

namespace ModularCurve export _root_.ModularCurve (qTwist qTwist_coeff qTwist_one_apply qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply) end ModularCurve
open scoped _root_.ModularCurve in
private theorem ModularCurve.theta_coeff {R : Type*} [CommRing R] (f : LaurentSeries R) (k : ℤ) : ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f).coeff k = k • f.coeff k := by
  rw [HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp

open scoped _root_.ModularCurve in
private theorem ModularCurve.theta_mul {R : Type*} [CommRing R] (f g : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (f * g) = f * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R g) + g * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) := by
  have hθ : ∀ (h : LaurentSeries R) (m : ℤ),
      ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R h).coeff m
        = m • h.coeff m := by
    intro h m
    rw [HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
      LaurentSeries.hasseDeriv_coeff]
    simp
  have hsupp : ∀ h : LaurentSeries R,
      ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R h).support
        ⊆ h.support := by
    intro h m hm
    rw [HahnSeries.mem_support] at hm ⊢
    intro h0
    exact hm (by rw [hθ, h0, smul_zero])
  ext k
  rw [HahnSeries.coeff_add, hθ, mul_comm g, HahnSeries.coeff_mul_right' g.isPWO_support (hsupp g),
    HahnSeries.coeff_mul_left' f.isPWO_support (hsupp f), HahnSeries.coeff_mul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  obtain ⟨-, -, hk⟩ := Finset.mem_antidiagonal.mp hij
  rw [hθ, hθ, ← hk, add_smul, mul_smul_comm, smul_mul_assoc, add_comm]

open scoped _root_.ModularCurve in
private theorem ModularCurve.theta_order {K : Type*} [Field K] [Algebra ℚ K] (f : LaurentSeries K) (hf : f.order ≠ 0) : ((HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K f).order = f.order := by
  have hθ : ∀ m : ℤ,
      ((HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K f).coeff m
        = m • f.coeff m := by
    intro m
    rw [HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
      LaurentSeries.hasseDeriv_coeff]
    simp
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hf0 : f ≠ 0 := fun h => hf (by rw [h, HahnSeries.order_zero])
  have hlead : ((HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) *
      LaurentSeries.derivative K f).coeff f.order ≠ 0 := by
    rw [hθ, zsmul_eq_mul]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hf) (HahnSeries.coeff_order_eq_zero.not.mpr hf0)
  have hne : (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K f ≠ 0 :=
    HahnSeries.ne_zero_of_coeff_ne_zero hlead
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hlead) ?_
  rw [HahnSeries.le_order_iff_forall hne]
  intro j hj
  rw [hθ, HahnSeries.coeff_eq_zero_of_lt_order hj, smul_zero]

open scoped _root_.ModularCurve in
private theorem ModularCurve.theta_qExpand {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (qExpand R N f) = N • (qExpand R N ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f)) := by
  ext k
  rw [theta_coeff, HahnSeries.coeff_nsmul, Pi.smul_apply]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, theta_coeff, mul_smul, natCast_zsmul]
  · rw [qExpand_coeff_of_not_dvd N f hk, qExpand_coeff_of_not_dvd N _ hk, smul_zero, smul_zero]

open scoped _root_.ModularCurve in
private theorem ModularCurve.theta_qTwist {R : Type*} [CommRing R] (u : Rˣ) (f : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (qTwist u f) = qTwist u ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) := by
  ext k
  rw [theta_coeff, qTwist_coeff, qTwist_coeff, theta_coeff, mul_smul_comm]

namespace ModularCurve export _root_.ModularCurve (qTwist qTwist_coeff qTwist_one_apply qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply) namespace PhiGen export _root_.ModularCurve.PhiGen (sum_qTwist_coeff) end ModularCurve.PhiGen
open scoped _root_.ModularCurve _root_.ModularCurve.PhiGen in
private theorem ModularCurve.PhiGen.weightTwo_coeff_sum_slots {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [NeZero ℓ] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) (n : ℤ) : ((ℓ * ℓ) • qExpand K (ℓ * ℓ) f + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f).coeff ((ℓ : ℤ) * n) = (ℓ : K) * (f.coeff ((ℓ : ℤ) * n) + if (ℓ : ℤ) ∣ n then (ℓ : K) * f.coeff (n / ℓ) else 0) := by
  have hℓ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  rw [HahnSeries.coeff_add, HahnSeries.coeff_nsmul, Pi.smul_apply, sum_qTwist_coeff ℓ ζ hζ f,
    if_pos (dvd_mul_right _ _)]
  by_cases hn : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [if_pos (dvd_mul_right _ _),
      show (ℓ : ℤ) * ((ℓ : ℤ) * m) = ((ℓ * ℓ : ℕ) : ℤ) * m by push_cast; ring,
      qExpand_coeff_mul, Int.mul_ediv_cancel_left _ hℓ, nsmul_eq_mul]
    push_cast
    ring
  · rw [if_neg hn, qExpand_coeff_of_not_dvd (ℓ * ℓ) f, smul_zero, zero_add, add_zero]
    intro h
    apply hn
    push_cast at h
    exact (mul_dvd_mul_iff_left hℓ).mp h

open scoped _root_.ModularCurve _root_.ModularCurve.PhiGen in
private theorem ModularCurve.PhiGen.weightTwo_coeff_sum_slots_inv {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [NeZero ℓ] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) (n : ℤ) : ((ℓ : K) • qExpand K (ℓ * ℓ) f + (ℓ : K)⁻¹ • ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f).coeff ((ℓ : ℤ) * n) = f.coeff ((ℓ : ℤ) * n) + if (ℓ : ℤ) ∣ n then (ℓ : K) * f.coeff (n / ℓ) else 0 := by
  have hℓ : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hℓK : (ℓ : K) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  rw [HahnSeries.coeff_add, HahnSeries.coeff_smul, HahnSeries.coeff_smul, sum_qTwist_coeff ℓ ζ hζ f,
    if_pos (dvd_mul_right _ _), smul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hℓK]
  by_cases hn : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [if_pos (dvd_mul_right _ _),
      show (ℓ : ℤ) * ((ℓ : ℤ) * m) = ((ℓ * ℓ : ℕ) : ℤ) * m by push_cast; ring,
      qExpand_coeff_mul, Int.mul_ediv_cancel_left _ hℓ]
    ring
  · rw [if_neg hn, qExpand_coeff_of_not_dvd (ℓ * ℓ) f, mul_zero, zero_add, add_zero]
    intro h
    apply hn
    push_cast at h
    exact (mul_dvd_mul_iff_left hℓ).mp h

open scoped _root_.ModularCurve _root_.ModularCurve.PhiGen in
private theorem ModularCurve.PhiGen.weightTwo_coeff_sum_slots_not_dvd {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [NeZero ℓ] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) {k : ℤ} (hk : ¬ (ℓ : ℤ) ∣ k) : ((ℓ * ℓ) • qExpand K (ℓ * ℓ) f + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f).coeff k = 0 := by
  rw [HahnSeries.coeff_add, HahnSeries.coeff_nsmul, Pi.smul_apply, sum_qTwist_coeff ℓ ζ hζ f,
    if_neg hk, qExpand_coeff_of_not_dvd (ℓ * ℓ) f, smul_zero, add_zero]
  intro h
  apply hk
  push_cast at h
  exact dvd_trans (dvd_mul_right _ _) h

open scoped _root_.ModularCurve _root_.ModularCurve.PhiGen in
private theorem ModularCurve.PhiGen.weightTwo_theta_sum_slots {R : Type*} [CommRing R] (ℓ : ℕ) [NeZero ℓ] (ζ : Rˣ) (f : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (qExpand R (ℓ * ℓ) f + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f) = (ℓ * ℓ) • qExpand R (ℓ * ℓ) ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) + ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) := by
  rw [map_add, mul_add, theta_qExpand, map_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  exact theta_qTwist (ζ ^ b) f

open scoped _root_.ModularCurve _root_.ModularCurve.PhiGen in
private theorem ModularCurve.PhiGen.weightTwo_theta_coeff {R : Type*} [CommRing R] (ℓ : ℕ) (f : LaurentSeries R) (n : ℤ) : ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f).coeff ((ℓ : ℤ) * n) + (if (ℓ : ℤ) ∣ n then (ℓ : R) * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f).coeff (n / ℓ) else 0) = n • ((if (ℓ : ℤ) ∣ n then f.coeff (n / ℓ) else 0) + (ℓ : R) * f.coeff ((ℓ : ℤ) * n)) := by
  rw [theta_coeff]
  by_cases hn : (ℓ : ℤ) ∣ n
  · rw [if_pos hn, if_pos hn, theta_coeff]
    obtain ⟨m, rfl⟩ := hn
    rcases eq_or_ne (ℓ : ℤ) 0 with hℓ | hℓ
    · simp [hℓ]
    · rw [Int.mul_ediv_cancel_left _ hℓ]
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
      ring
  · rw [if_neg hn, if_neg hn]
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, add_zero, zero_add]
    ring

example {R : Type*} [CommRing R] (f : LaurentSeries R) :
    LaurentSeries.derivative R f = LaurentSeries.derivative ℤ f := rfl

example {K : Type*} [Field K] [Algebra ℚ K] (f : LaurentSeries K) :
    (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative K f
      = (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) * LaurentSeries.derivative ℚ f := rfl

example :
    let F : LaurentSeries ℚ := HahnSeries.single (-1 : ℤ) (1 : ℚ) + HahnSeries.single (0 : ℤ) (744 : ℚ)
      + HahnSeries.single (1 : ℤ) (196884 : ℚ) + HahnSeries.single (2 : ℤ) (21493760 : ℚ)
      + HahnSeries.single (3 : ℤ) (864299970 : ℚ) + HahnSeries.single (4 : ℤ) (20245856256 : ℚ)
    let w0 : ℤ → ℚ := fun n => (if (2 : ℤ) ∣ n then F.coeff (n / 2) else 0) + (2 : ℚ) * F.coeff (2 * n)
    w0 (-2) = 1 ∧ w0 (-1) = 0 ∧ w0 0 = 2232 ∧ w0 1 = 42987520 ∧ w0 2 = 40491909396 := by
  intro F w0
  simp only [F, w0, HahnSeries.coeff_add, HahnSeries.coeff_single]
  norm_num

example :
    let F : LaurentSeries ℚ := HahnSeries.single (-1 : ℤ) (1 : ℚ) + HahnSeries.single (0 : ℤ) (744 : ℚ)
      + HahnSeries.single (1 : ℤ) (196884 : ℚ) + HahnSeries.single (2 : ℤ) (21493760 : ℚ)
      + HahnSeries.single (3 : ℤ) (864299970 : ℚ) + HahnSeries.single (4 : ℤ) (20245856256 : ℚ)
    let θF : LaurentSeries ℚ :=
      (HahnSeries.single (1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) * LaurentSeries.derivative ℚ F
    let w0 : ℤ → ℚ := fun n => (if (2 : ℤ) ∣ n then F.coeff (n / 2) else 0) + (2 : ℚ) * F.coeff (2 * n)
    let w2 : ℤ → ℚ := fun n => θF.coeff (2 * n) + (if (2 : ℤ) ∣ n then (2 : ℚ) * θF.coeff (n / 2) else 0)
    (w2 (-2) = -2 ∧ w2 (-1) = 0 ∧ w2 0 = 0 ∧ w2 1 = 42987520 ∧ w2 2 = 80983818792) ∧
      (w2 (-2) = (-2 : ℤ) • w0 (-2) ∧ w2 (-1) = (-1 : ℤ) • w0 (-1) ∧ w2 0 = (0 : ℤ) • w0 0 ∧
        w2 1 = (1 : ℤ) • w0 1 ∧ w2 2 = (2 : ℤ) • w0 2) := by
  intro F θF w0 w2
  simp only [F, θF, w0, w2, ModularCurve.theta_coeff, HahnSeries.coeff_add, HahnSeries.coeff_single]
  norm_num

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_theta_mul.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_theta_mul.ModularCurve.PhiGen in

theorem solution {R : Type*} [CommRing R] (f g : LaurentSeries R) : (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R (f * g) = f * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R g) + g * ((HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) * LaurentSeries.derivative R f) :=
  ModularCurve.theta_mul f g

#print axioms solution
