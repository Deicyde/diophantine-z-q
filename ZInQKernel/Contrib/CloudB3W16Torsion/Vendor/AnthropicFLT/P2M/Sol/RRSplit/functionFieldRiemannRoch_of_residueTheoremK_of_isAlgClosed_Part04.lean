/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean; source lines 4222-5756.
Modification notice (CloudB3 Worker16 curve support, 2026-11-16):
Factored at balanced source section boundaries. Relocated imports with the canonical main-port reuse map; expanded P2M
namespace/open/export command helpers to ordinary Lean commands, removed metadata
reactivation commands, and resolved metadata aliases directly. Expanded local notation
literally. Promoted source-private helpers into the original P2MW module namespace
so proofs can cross factoring-file boundaries without new root-name collisions.
Kept mathematical proof bodies and all public solution signatures; no new mathematical
assumptions. Lean 4.35 compatibility edits are recorded in the accompanying manifest.
Complete original LICENSE, NOTICE, and attribution are in this vendor root; a local
copy is supplied in RRSplit for independent distribution of this support patch.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed_Part03

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

section
section

set_option maxHeartbeats 6400000

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1
open ModularCurve.KwNo6Section

namespace ModularCurve
namespace KwNo6Pin

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem aCoeff_zero (v : Place K F) (S : Lg37CompletionSection v)
    (x : lg37_completion v) :
    aCoeff v S 0 x = lg37_residueHat v x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S 1 x)
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S 1 x) with ha_def
  rw [Finset.sum_range_one, pow_zero, mul_one] at ha
  have hres : lg37_residueHat v (x - S.lift (a 0)) = lg37_residueHat v 0 :=
    mp72a102_t3_residueHat_congr_of_depth_one v (by rw [ha, _root_.map_zero])
  rw [map_sub, S.residueHat_lift, _root_.map_zero, sub_eq_zero] at hres
  simp only [aCoeff, ← ha_def]
  exact hres.symm

theorem aCoeff_add (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ)
    (x y : lg37_completion v) :
    aCoeff v S m (x + y) = aCoeff v S m x + aCoeff v S m y := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y)
  have hxy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set ay := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y) with hay_def
  set axy := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
    with haxy_def
  have hsum : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift ((fun i => ax i + ay i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e : (x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i
        = (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          + (y - ∑ i ∈ Finset.range (m + 1), S.lift (ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_add, add_mul]),
        Finset.sum_add_distrib]
      ring
    rw [e, mp72a102_t3_evalDepth_add, hx, hy, add_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1), S.lift ((fun i => (ax i + ay i) - axy i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1), S.lift ((ax i + ay i) - axy i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (axy i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hxy, hsum, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => (ax i + ay i) - axy i) key m (Nat.lt_succ_self m)
  have han : axy m = ax m + ay m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hay_def, ← haxy_def]
  exact han

theorem aCoeff_smul (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ) (c : K)
    (x : lg37_completion v) :
    aCoeff v S m (algebraMap K (lg37_completion v) c * x)
      = algebraMap K v.ResidueField c * aCoeff v S m x := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hcx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set acx := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x)) with hacx_def
  have hsmul : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((algebraMap K (lg37_completion v) c * x)
        - ∑ i ∈ Finset.range (m + 1),
            S.lift ((fun i => algebraMap K v.ResidueField c * ax i) i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have e : (algebraMap K (lg37_completion v) c * x)
          - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap K (lg37_completion v) c
          * (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hlift : S.lift (algebraMap K v.ResidueField c * ax i)
          = algebraMap K (lg37_completion v) c * S.lift (ax i) := by
        rw [← Algebra.smul_def c (ax i), map_smul, Algebra.smul_def]
      rw [hlift, mul_assoc]
    rw [e, mp72a102_t3_evalDepth_mul, hx, mul_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1),
          S.lift ((fun i => algebraMap K v.ResidueField c * ax i - acx i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1),
            S.lift (algebraMap K v.ResidueField c * ax i - acx i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (acx i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hcx, hsmul, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => algebraMap K v.ResidueField c * ax i - acx i) key m (Nat.lt_succ_self m)
  have han : acx m = algebraMap K v.ResidueField c * ax m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hacx_def]
  exact han

theorem aCoeff_shift (v : Place K F) (S : Lg37CompletionSection v) (n : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
      = aCoeff v S n x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x)
  have hpx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x) with ha_def
  set b := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
    with hb_def

  set c : ℕ → v.ResidueField :=
    fun i => Nat.rec (motive := fun _ => v.ResidueField) 0 (fun j _ => a j) i with hc_def

  have hshift : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
        - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have hmul := mp72a102_t3_evalₐ_succ_mul_eq_zero (maximalIdeal v.toValuationSubring)
      v.uniformizerSubring_mem_maximalIdeal ha
    have e : (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
          - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (x - ∑ i ∈ Finset.range (n + 1), S.lift (a i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      have hc0 : c 0 = 0 := rfl
      have hcs : ∀ i, c (i + 1) = a i := fun _ => rfl
      rw [Finset.sum_range_succ', hc0, _root_.map_zero, zero_mul, add_zero, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcs i, pow_succ]
      ring
    rw [e]
    exact hmul

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      (∑ i ∈ Finset.range (n + 2), S.lift ((fun i => c i - b i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 2), S.lift (c i - b i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (b i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hpx, hshift, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 2)
    (fun i => c i - b i) key (n + 1) (Nat.lt_succ_self (n + 1))
  have hcn : c (n + 1) = a n := rfl
  have hbn : b (n + 1) = a n := by
    have := sub_eq_zero.mp hzero
    rw [hcn] at this
    exact this.symm
  simp only [aCoeff, ← ha_def, ← hb_def]
  exact hbn

theorem aCoeff_shift_pow (v : Place K F) (S : Lg37CompletionSection v) (n k : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + k)
        ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring) ^ k
          * x)
      = aCoeff v S n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring) ^ (k + 1) * x
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * ((algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring) ^ k * x) := by
      rw [pow_succ]; ring
    rw [show n + (k + 1) = (n + k) + 1 from by omega, hstep, aCoeff_shift, ih]

theorem aCoeff_one_eq_zero (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : aCoeff v S n 1 = 0 := by
  have hc := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1)
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1) with hcc_def

  set e : ℕ → v.ResidueField := fun i => if i = 0 then 1 else 0 with he_def
  have hesum : (∑ i ∈ Finset.range (n + 1), S.lift (e i)
      * algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring ^ i) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [he_def]
    · intro i _ hi; simp [he_def, hi]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hevalid : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    rw [hesum, sub_self, _root_.map_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      (∑ i ∈ Finset.range (n + 1), S.lift ((fun i => e i - cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 1), S.lift (e i - cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hc, hevalid, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 1)
    (fun i => e i - cc i) key n (Nat.lt_succ_self n)
  have hen : e n = 0 := by simp [he_def, Nat.one_le_iff_ne_zero.mp hn]
  have : e n - cc n = 0 := hzero
  rw [hen, zero_sub, neg_eq_zero] at this
  simp only [aCoeff, ← hcc_def]
  exact this

theorem clearPow_mem (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    v.uniformizer ^ (N + 1) * f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero]; exact zero_mem _
  · refine (v.mem_iff_ord_nonneg (mul_ne_zero (v.uniformizer_pow_ne_zero _) hf0)).mpr ?_
    rw [v.ord_mul (v.uniformizer_pow_ne_zero _) hf0, v.ord_uniformizer_pow]
    have h := Int.self_le_toNat (-v.ord f)
    have hNc : ((-v.ord f).toNat : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega

noncomputable def clearedHat (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    lg37_completion v :=
  algebraMap v.toValuationSubring (lg37_completion v)
    ⟨v.uniformizer ^ (N + 1) * f, clearPow_mem v f hN⟩

noncomputable def resStar (v : Place K F) (S : Lg37CompletionSection v) (f : F) :
    v.ResidueField :=
  aCoeff v S ((-v.ord f).toNat) (clearedHat v f (le_refl _))

theorem aCoeff_clearedHat_of_le (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    aCoeff v S N (clearedHat v f hN) = resStar v S f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  unfold clearedHat resStar
  have hfac : (⟨v.uniformizer ^ (((-v.ord f).toNat + k) + 1) * f,
        clearPow_mem v f hN⟩ : v.toValuationSubring)
      = v.uniformizerSubring ^ k
        * ⟨v.uniformizer ^ ((-v.ord f).toNat + 1) * f, clearPow_mem v f (le_refl _)⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, map_pow]
  exact aCoeff_shift_pow v S ((-v.ord f).toNat) k _

theorem resStar_add (v : Place K F) (S : Lg37CompletionSection v) (f g : F) :
    resStar v S (f + g) = resStar v S f + resStar v S g := by
  set N := (-v.ord f).toNat ⊔ (-v.ord g).toNat ⊔ (-v.ord (f + g)).toNat with hN
  have hf : (-v.ord f).toNat ≤ N := le_trans le_sup_left le_sup_left
  have hg : (-v.ord g).toNat ≤ N := le_trans le_sup_right le_sup_left
  have hfg : (-v.ord (f + g)).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S f hf, ← aCoeff_clearedHat_of_le v S g hg,
    ← aCoeff_clearedHat_of_le v S (f + g) hfg, ← aCoeff_add]
  congr 1
  unfold clearedHat
  rw [← map_add]
  congr 1
  apply Subtype.ext
  push_cast
  ring

theorem resStar_smul (v : Place K F) (S : Lg37CompletionSection v) (c : K) (f : F) :
    resStar v S (c • f) = c • resStar v S f := by
  set N := (-v.ord (c • f)).toNat ⊔ (-v.ord f).toNat with hN
  have hcf : (-v.ord (c • f)).toNat ≤ N := le_sup_left
  have hf : (-v.ord f).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S (c • f) hcf, ← aCoeff_clearedHat_of_le v S f hf,
    Algebra.smul_def c (aCoeff v S N (clearedHat v f hf)), ← aCoeff_smul]
  congr 1
  unfold clearedHat
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring (lg37_completion v) c, ← map_mul]
  congr 1
  apply Subtype.ext
  push_cast [v.coe_algebraMap, Algebra.smul_def]
  ring

noncomputable def resStarₗ (v : Place K F) (S : Lg37CompletionSection v) :
    F →ₗ[K] v.ResidueField where
  toFun := resStar v S
  map_add' := resStar_add v S
  map_smul' c f := by rw [RingHom.id_apply]; exact resStar_smul v S c f

theorem resStar_simplePole (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    resStar v S f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ := by
  have hM : (-v.ord f).toNat ≤ 1 := by
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [v.ord_zero]; simp
    · have hge : (0 : ℤ) ≤ v.ord (v.uniformizer * f) :=
        (v.mem_iff_ord_nonneg (mul_ne_zero v.uniformizer_ne_zero hf0)).mp hf
      rw [v.ord_mul v.uniformizer_ne_zero hf0, v.ord_uniformizer] at hge
      have := Int.self_le_toNat (-v.ord f)
      omega
  rw [← aCoeff_clearedHat_of_le v S f hM]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ (1 + 1) * f, clearPow_mem v f hM⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨v.uniformizer * f, hf⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, aCoeff_shift, aCoeff_zero, lg37_residueHat_algebraMap]

theorem resStar_of_mem (v : Place K F) (S : Lg37CompletionSection v) {f : F}
    (hf : f ∈ v.toValuationSubring) : resStar v S f = 0 := by
  rw [resStar_simplePole v S f (mul_mem v.uniformizer_mem hf), IsLocalRing.residue_eq_zero_iff]
  have : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal

theorem resStar_higherPoleMonomial (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : resStar v S (v.uniformizer ^ (n + 1))⁻¹ = 0 := by
  have hord : v.ord (v.uniformizer ^ (n + 1))⁻¹ = -((n : ℤ) + 1) := by
    rw [v.ord_inv, v.ord_uniformizer_pow]; push_cast; ring
  have hM : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat = n + 1 := by
    rw [hord]; simp
  have hle : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat ≤ n + 1 := le_of_eq hM
  rw [← aCoeff_clearedHat_of_le v S (v.uniformizer ^ (n + 1))⁻¹ hle]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ ((n + 1) + 1) * (v.uniformizer ^ (n + 1))⁻¹,
        clearPow_mem v (v.uniformizer ^ (n + 1))⁻¹ hle⟩ : v.toValuationSubring)
      = v.uniformizerSubring := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    rw [pow_succ, mul_right_comm, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1)), one_mul]
  rw [hfac]
  have : algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
      = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * 1 := by
    rw [mul_one]
  rw [this, aCoeff_shift, aCoeff_one_eq_zero v S hn]

noncomputable def canonicalLocalResidueDataKStar (v : Place K F)
    (S : Lg37CompletionSection v) : v.CanonicalLocalResidueDataK where
  res := resStarₗ v S
  res_of_mem _f hf := resStar_of_mem v S hf
  res_simplePole f hf := resStar_simplePole v S f hf
  res_higherPoleMonomial _n hn := resStar_higherPoleMonomial v S hn

section WitnessW
variable {v : Place K F} {ℓ : v.toValuationSubring}
  (hℓ : IsLocalRing.residue v.toValuationSubring ℓ ∉ Set.range (algebraMap K v.ResidueField))
include hℓ

end WitnessW


end ModularCurve.KwNo6Pin



end


end


section
section
set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_lSpace_of_weilSmul_mem_omegaSpace [HasPrincipalDivisors K F]
    {W D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W)
    {f : F} (hfφ : weilSmul K F f φ ∈ omegaSpace D) :
    f ∈ LSpace (W - D) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact (LSpace (W - D)).zero_mem
  ·
    obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    have hPinv : ∀ v : Place K F, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord, v.ord_inv]

    have hφshift : φ ∈ omegaSpace (D - P) := by
      have hinv : weilSmul K F f⁻¹ (weilSmul K F f φ) = φ := by
        rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf, weilSmul_one,
          LinearMap.id_apply]
      have h := weilSmul_mem_omegaSpace_add (inv_ne_zero hf) hPinv hfφ
      rwa [hinv, ← sub_eq_add_neg] at h

    have hle := hWmax (D - P) hφshift
    refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
    have hlev := hle v
    rw [Finsupp.sub_apply, hPord v] at hlev
    rw [Finsupp.sub_apply]
    linarith
end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residuePairing_surjective [HasPrincipalDivisors K F]
    (hRk1 : WeilDifferentialRankOne K F) (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩

  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRk1 hφmem hφ0 hμmem

  have hfL : f ∈ LSpace (W - D) :=
    mem_lSpace_of_weilSmul_mem_omegaSpace hWmax (hf ▸ hμD)
  exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩
end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residuePairingSurjective_of_weilDifferentialRankOne [HasPrincipalDivisors K F]
    (hRk1 : WeilDifferentialRankOne K F) : ResiduePairingSurjective K F := by
  intro _ W D φ hφ hφ0 hWmax
  exact residuePairing_surjective hRk1 W D hφ hφ0 hWmax
end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residuePairingSurjective_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F) : ResiduePairingSurjective K F :=
  residuePairingSurjective_of_weilDifferentialRankOne
    (weilDifferentialRankOne_of_riemannIndexFormula hRI)
end AlgebraicCurve

end


end


end


section
section
set_option autoImplicit false
noncomputable section
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField
section CanonicalKResidueTerm
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
section SupportMachinery
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable (K F)
variable {K F}

theorem weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK [HasPrincipalDivisors K F]
    (hRT : ResidueTheoremK K F) (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehlerK Rfam hω ∈ omegaSpace (canonicalDivisorOf hω) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, weilOfKaehlerK_vanish_adeleBdd_canonical Rfam hω (Submodule.mem_comap.mp hβ)]
  obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
  have hγ' : γ = ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ := Subtype.ext hf.symm
  rw [hγ', hRT Rfam hω f, add_zero]
end SupportMachinery

end CanonicalKResidueTerm

end AlgebraicCurve

end


end


end


section
section

noncomputable section

open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.Module.IsLocalRing

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Single

end Single


section SingleEval

variable [HasCanonicalLocalResidueKStar K F]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

end SingleEval


section SimplePoleProbe

variable [HasCanonicalLocalResidueKStar K F]

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable (v : Place K F)

end Place


variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [Nontrivial Ω[F⁄K]]

def simplePoleProbe {ω : Ω[F⁄K]} (_hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) : adeleSpace K F :=
  adeleSingle v ((c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹)

open scoped _root_.Classical _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Classical in
omit [Nontrivial Ω[F⁄K]] in

theorem simplePoleProbe_mem_adeleBdd {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F)
    (c : v.toValuationSubring) {D : Divisor K F} (hDv : canonicalDivisorOf hω v < D v) :
    (simplePoleProbe hω v c : Place K F → F) ∈ adeleBdd D := by
  unfold simplePoleProbe
  rw [adeleSingle_coe]
  refine single_mem_adeleBdd v _ D ?_
  rcases eq_or_ne (c : F) 0 with hc | hc
  · rw [hc, zero_mul, zero_mul, Valuation.map_zero]; exact zero_le'
  · set g : F := (c : F) * v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹ with hg
    have hg0 : g ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω))
    rw [v.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp, neg_le]

    rw [hg, v.ord_mul (mul_ne_zero hc (inv_ne_zero v.uniformizer_ne_zero))
        (inv_ne_zero (v.differentialCoeff_ne_zero hω)),
      v.ord_mul hc (inv_ne_zero v.uniformizer_ne_zero),
      v.ord_inv, v.ord_uniformizer, v.ord_inv]
    have hcnn : 0 ≤ v.ord (c : F) := v.ord_nonneg_of_mem c.2
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hDv
    linarith

end SimplePoleProbe


namespace Place
export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)
end Place
namespace Place
open scoped AlgebraicCurve.Place in
theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.exists_trace_residue_ne_zero [HasSeparableResidue K F] (v : Place K F) :
    ∃ c : v.toValuationSubring,
      Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) ≠ 0 := by
  have htr := HasSeparableResidue.trace_ne_zero (K := K) (F := F) v
  rw [ne_eq, LinearMap.ext_iff, not_forall] at htr
  obtain ⟨x, hx⟩ := htr
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨c, by simpa using hx⟩

end Place



section Nonvanishing

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Nonvanishing


section Maximality

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Maximality


section Discharge

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Discharge


end AlgebraicCurve


section AxiomAudit

end AxiomAudit


end


end


end


section
section
set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_riemannGenusReachedAt_of_bounded
    [IsCurveOver K F] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  obtain ⟨γ, hγ⟩ := hbdd

  obtain ⟨M, ⟨D₀, hD₀⟩, hMmax⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun n => ∃ D : Divisor K F, Divisor.degree D - ell D = n)
      ⟨γ, fun n ⟨D, hD⟩ => hD ▸ hγ D⟩
      ⟨Divisor.degree (0 : Divisor K F) - ell (0 : Divisor K F), 0, rfl⟩
  refine ⟨M + 1, D₀, ?_, ?_, ?_⟩
  · exact finiteDimensional_lSpace D₀
  · rw [hD₀]; ring
  · intro D
    have := hMmax (Divisor.degree D - ell D) ⟨D, rfl⟩
    linarith
end AlgebraicCurve

end


set_option autoImplicit false
noncomputable section
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem stichtenothGenusExists_of_bounded
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    StichtenothGenusExists K F :=
  ⟨‹_›, ‹_›, exists_riemannGenusReachedAt_of_bounded hbdd⟩
end AlgebraicCurve

end


end


end


section
section
set_option autoImplicit false
set_option maxHeartbeats 6400000
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsLocalRing
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve
open ModularCurve.Lg37 ModularCurve.KwNo6Section ModularCurve.KwNo6Pin
open Mp72a102T1
namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem completionSection_nonempty_generic (v : Place K F)
    [FiniteDimensional K v.ResidueField] [Algebra.IsSeparable K v.ResidueField] :
    Nonempty (Lg37CompletionSection v) := by
  obtain ⟨ᾱ, htop⟩ := Field.exists_primitive_element K v.ResidueField
  have hint : IsIntegral K ᾱ := Algebra.IsIntegral.isIntegral ᾱ
  have hmon : (minpoly K ᾱ).Monic := minpoly.monic hint
  have hsep : (minpoly K ᾱ).Separable := Algebra.IsSeparable.isSeparable K ᾱ
  have haevalbar : (aeval ᾱ) (minpoly K ᾱ) = 0 := minpoly.aeval K ᾱ
  obtain ⟨αhat, hαroot, hαres⟩ :=
    mp72a102_t1_exists_completion_root_of_residue_root v hmon hsep haevalbar
  exact ⟨sectionOfPrimitiveRoot v hint htop αhat hαroot hαres⟩
end AlgebraicCurve


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_mem_lSpace_add {D E : Divisor K F} {f g : F}
    (hf : f ∈ LSpace D) (hg : g ∈ LSpace E) :
    f * g ∈ LSpace (D + E) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul]; exact (LSpace _).zero_mem
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun v => ?_
  rw [Finsupp.add_apply, neg_add, v.ord_mul hf0 hg0]
  exact add_le_add ((mem_lSpace_iff_ord.mp hf).resolve_left hf0 v)
    ((mem_lSpace_iff_ord.mp hg).resolve_left hg0 v)

theorem pow_mem_lSpace_nsmul {B : Divisor K F} {f : F} (hf : f ∈ LSpace B) (j : ℕ) :
    f ^ j ∈ LSpace (j • B) := by
  induction j with
  | zero => simpa using one_mem_lSpace_zero (K := K) (F := F)
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_lSpace_add ih hf

structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where

  x : F

  B : Divisor K F

  hB_eff : 0 ≤ B

  hx_mem : x ∈ LSpace B

  n : ℕ

  hn_pos : 0 < n

  degB_eq : Divisor.degree B = n

  c : ℕ

  u : Fin n → F

  hu_mem : ∀ i, u i ∈ LSpace (c • B)

  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)

variable (K F) in

def HasPoleDivisorPackage : Prop := Nonempty (PoleDivisorPackage K F)

namespace PoleDivisorPackage

variable (P : PoleDivisorPackage K F)

theorem pow_mul_u_mem_lSpace (j : ℕ) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace ((j + P.c) • P.B) := by
  rw [add_nsmul]
  exact mul_mem_lSpace_add (pow_mem_lSpace_nsmul P.hx_mem j) (P.hu_mem i)

theorem pow_mul_u_mem_lSpace_of_le {j m : ℕ} (hjm : j + P.c ≤ m) (i : Fin P.n) :
    P.x ^ j * P.u i ∈ LSpace (m • P.B) := by
  refine lSpace_mono ?_ (P.pow_mul_u_mem_lSpace j i)
  intro v
  have hBv : (0 : ℤ) ≤ P.B v := P.hB_eff v
  show ((j + P.c) • P.B) v ≤ (m • P.B) v
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjm) hBv

set_option maxHeartbeats 1600000 in

theorem ell_nsmul_poleDivisor_ge [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    (P.n : ℤ) * (m - P.c + 1) ≤ ell (m • P.B) := by
  haveI := finiteDimensional_lSpace (K := K) (m • P.B)

  set g : Fin (m - P.c + 1) × Fin P.n → LSpace (m • P.B) :=
    fun p => ⟨P.x ^ (p.1 : ℕ) * P.u p.2,
      P.pow_mul_u_mem_lSpace_of_le (by have := p.1.isLt; omega) p.2⟩
    with hgdef

  have hsub : LinearIndependent K (fun p => (g p : F)) := by
    have heq : (fun p => (g p : F))
        = (fun p : ℕ × Fin P.n => P.x ^ p.1 * P.u p.2)
            ∘ (fun p : Fin (m - P.c + 1) × Fin P.n => ((p.1 : ℕ), p.2)) := by
      funext p; rfl
    rw [heq]
    refine P.lin_indep.comp _ ?_
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (Fin.val_injective hpq.1) hpq.2

  have hg : LinearIndependent K g := hsub.of_comp (LSpace (m • P.B)).subtype

  have hcard := hg.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hZ : ((m - P.c + 1) * P.n : ℤ) ≤ (ell (m • P.B) : ℤ) := by exact_mod_cast hcard
  have heq : (((m - P.c + 1 : ℕ) : ℤ) * P.n : ℤ) = (P.n : ℤ) * ((m : ℤ) - P.c + 1) := by
    rw [Nat.cast_add, Nat.cast_sub hm, Nat.cast_one]; ring
  linarith

theorem degree_nsmul_sub_ell_le [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] {m : ℕ} (hm : P.c ≤ m) :
    Divisor.degree (m • P.B) - ell (m • P.B) ≤ (P.n : ℤ) * (P.c - 1) := by
  have hge := P.ell_nsmul_poleDivisor_ge hm
  have hdeg : Divisor.degree (m • P.B) = (m : ℤ) * P.n := by
    rw [show m • P.B = (m : ℤ) • P.B from (natCast_zsmul _ _).symm,
      Divisor.degree.map_zsmul, smul_eq_mul, P.degB_eq]
  linarith

end PoleDivisorPackage


theorem PoleDivisorPackage.ell_nsmul_sub_pos [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) {A : Divisor K F} (hA : 0 ≤ A) {m : ℕ} (hm : P.c ≤ m)
    (hbig : Divisor.degree A < (P.n : ℤ) * (m - P.c + 1)) :
    0 < ell (m • P.B - A) := by
  haveI := finiteDimensional_lSpace (K := K) (m • P.B)
  have hle : m • P.B - A ≤ m • P.B := by
    intro v
    have hAv : (0 : ℤ) ≤ A v := hA v
    rw [Finsupp.sub_apply]
    linarith

  have h48 := ell_sub_ell_le_degree_sub_degree (K := K) hle
  rw [map_sub, sub_sub_cancel] at h48

  have h412 := P.ell_nsmul_poleDivisor_ge hm

  have : (0 : ℤ) < (ell (m • P.B - A) : ℤ) := by linarith
  exact_mod_cast this

set_option maxHeartbeats 1600000 in

theorem PoleDivisorPackage.degree_sub_ell_le [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (P.n : ℤ) * (P.c - 1) := by
  classical

  set D' : Divisor K F := D ⊔ 0 with hD'def
  have hD'eff : 0 ≤ D' := le_sup_right
  have hDD' : D ≤ D' := le_sup_left
  haveI := finiteDimensional_lSpace (K := K) D'
  have hmono : Divisor.degree D - (ell D : ℤ) ≤ Divisor.degree D' - ell D' := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hDD'
    linarith

  set m : ℕ := P.c + (Divisor.degree D').toNat with hmdef
  have hcm : P.c ≤ m := Nat.le_add_right _ _
  have hdegD' : 0 ≤ Divisor.degree D' := Divisor.degree_nonneg_of_nonneg hD'eff
  have hbig : Divisor.degree D' < (P.n : ℤ) * (m - P.c + 1) := by
    have hcast : ((m : ℤ) - P.c) = Divisor.degree D' := by
      simp only [hmdef, Nat.cast_add, add_sub_cancel_left, Int.toNat_of_nonneg hdegD']
    rw [hcast]
    have hn1 : (1 : ℤ) ≤ P.n := by exact_mod_cast P.hn_pos
    nlinarith

  have hellpos := P.ell_nsmul_sub_pos hD'eff hcm hbig
  have hnebot : LSpace (m • P.B - D') ≠ ⊥ :=
    fun h => by rw [ell, h, finrank_bot] at hellpos; exact lt_irrefl 0 hellpos
  obtain ⟨z, hzL, hz0⟩ := (Submodule.ne_bot_iff _).mp hnebot

  obtain ⟨Dz, hDzord, hDzdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
  have hzmem := (mem_lSpace_iff_ord.mp hzL).resolve_left hz0
  have hD'le : D' ≤ m • P.B + Dz := by
    intro v
    have := hzmem v
    simp only [Finsupp.add_apply, Finsupp.sub_apply, neg_sub] at this ⊢
    rw [hDzord]; linarith

  have hellshift : ell (m • P.B + Dz) = ell (m • P.B) :=
    (LinearEquiv.finrank_eq (lSpaceShiftEquiv (m • P.B) hz0 hDzord)).symm
  have hdegshift : Divisor.degree (m • P.B + Dz) = Divisor.degree (m • P.B) := by
    rw [map_add, hDzdeg, add_zero]

  haveI := finiteDimensional_lSpace (K := K) (m • P.B + Dz)
  have hmono' : Divisor.degree D' - (ell D' : ℤ)
      ≤ Divisor.degree (m • P.B + Dz) - ell (m • P.B + Dz) := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) hD'le
    linarith
  rw [hellshift, hdegshift] at hmono'
  have h412 := P.degree_nsmul_sub_ell_le hcm
  linarith

theorem riemannGenusBounded_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    RiemannGenusBounded K F :=
  ⟨(P.n : ℤ) * (P.c - 1), P.degree_sub_ell_le⟩

theorem stichtenothGenusExists_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_bounded (riemannGenusBounded_of_poleDivisorPackage P)

theorem stichtenothGenusExists_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage h.some

end AlgebraicCurve


end


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.IsDedekindDomain
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.WithZero

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

structure TranscendenceTower (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] where

  x : E

  hx_indep : LinearIndependent K (fun j : ℕ => x ^ j)

  v : Place K E

  hvdeg : v.deg = 1

  hxv : v.ord x = -1

  hxreg : ∀ u : Place K E, u ≠ v → 0 ≤ u.ord x

namespace TranscendenceTower

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
variable (T : TranscendenceTower K E F)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem x_ne_zero : T.x ≠ 0 := fun h => by
  have := T.hxv; rw [h, Place.ord_zero] at this; exact absurd this (by decide)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

abbrev xF : F := algebraMap E F T.x

def poleDivisor : Divisor K F := Divisor.pullback F (Finsupp.single T.v 1)

omit [FiniteDimensional E F] in

theorem poleDivisor_apply (w : Place K F) :
    T.poleDivisor w = (w.ramificationIndex E : ℤ) * (Finsupp.single T.v 1) (w.restrict E) :=
  Divisor.pullback_apply (Finsupp.single T.v 1) w

omit [FiniteDimensional E F] in

theorem poleDivisor_nonneg : 0 ≤ T.poleDivisor := by
  classical
  intro w
  rw [Finsupp.coe_zero, Pi.zero_apply, T.poleDivisor_apply, Finsupp.single_apply]
  refine mul_nonneg (Int.natCast_nonneg _) ?_
  split_ifs <;> simp

omit [FiniteDimensional E F] in

theorem xF_mem_lSpace_poleDivisor : T.xF ∈ LSpace T.poleDivisor := by
  classical
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [T.poleDivisor_apply, Place.ord_restrict, Finsupp.single_apply]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  · simp only [hw, T.hxv, ite_true, mul_one, mul_neg_one, le_refl]
  · simp only [if_neg (Ne.symm hw), mul_zero, _root_.neg_zero]
    exact mul_nonneg (Int.natCast_nonneg _) (T.hxreg _ hw)

theorem degree_poleDivisor_eq_finrank :
    Divisor.degree T.poleDivisor = (Module.finrank E F : ℤ) := by
  rw [poleDivisor, Divisor.degree_pullback, Divisor.degree_single, T.hvdeg]
  push_cast; ring

omit [FiniteDimensional E F] in

theorem mem_lSpace_nsmul_poleDivisor_of_regular_outside {f : F}
    (hreg : ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f)
    {c : ℕ} (hc : ∀ w ∈ T.v.fiber F, -(c : ℤ) ≤ w.ord f) :
    f ∈ LSpace (c • T.poleDivisor) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [Finsupp.smul_apply, T.poleDivisor_apply, Finsupp.single_apply, nsmul_eq_mul]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  ·
    simp only [hw, ite_true, mul_one]
    have he : (1 : ℤ) ≤ w.ramificationIndex E := by
      exact_mod_cast w.ramificationIndex_pos (F := E)
    have hbdd := hc w (Place.mem_fiber.mpr hw)
    nlinarith [Int.natCast_nonneg c]
  ·
    simp only [if_neg (Ne.symm hw), mul_zero, _root_.neg_zero]
    exact hreg w hw

omit [FiniteDimensional E F] in

theorem exists_forall_mem_lSpace_nsmul_poleDivisor {n : ℕ} (u : Fin n → F)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    ∃ c : ℕ, ∀ i, u i ∈ LSpace (c • T.poleDivisor) := by
  classical

  refine ⟨(Finset.univ : Finset (Fin n)).sup fun i =>
    (T.v.fiber F).sup fun w => (-(w.ord (u i))).toNat,
    fun i => T.mem_lSpace_nsmul_poleDivisor_of_regular_outside (hreg i) ?_⟩
  intro w hw

  have h1 : (-(w.ord (u i))).toNat
      ≤ (T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat :=
    Finset.le_sup (f := fun w' => (-(w'.ord (u i))).toNat) hw
  have h2 : ((T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat)
      ≤ (Finset.univ : Finset (Fin n)).sup fun i' =>
          (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat :=
    Finset.le_sup (f := fun i' => (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat)
      (Finset.mem_univ i)
  have htnat : -(w.ord (u i)) ≤ ((-(w.ord (u i))).toNat : ℤ) := Int.self_le_toNat _
  omega

end TranscendenceTower


variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

structure IntegralBasisInLSpace (T : TranscendenceTower K E F) where

  c : ℕ

  u : Fin (Module.finrank E F) → F

  hu_indep : LinearIndependent E u

  hu_mem : ∀ i, u i ∈ LSpace (c • T.poleDivisor)

variable (K E F) in

def HasIntegralBasisInLSpace (T : TranscendenceTower K E F) : Prop :=
  Nonempty (IntegralBasisInLSpace T)

def IntegralBasisInLSpace.ofRegularOutside (T : TranscendenceTower K E F)
    (u : Fin (Module.finrank E F) → F) (hu_indep : LinearIndependent E u)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    IntegralBasisInLSpace T where
  c := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose
  u := u
  hu_indep := hu_indep
  hu_mem := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose_spec

variable (K E F) in

def HasIntegralBasisRegularOutside (T : TranscendenceTower K E F) : Prop :=
  ∃ u : Fin (Module.finrank E F) → F, LinearIndependent E u ∧
    ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)

omit [FiniteDimensional E F] in

theorem hasIntegralBasisInLSpace_of_regularOutside (T : TranscendenceTower K E F)
    (h : HasIntegralBasisRegularOutside K E F T) :
    HasIntegralBasisInLSpace K E F T := by
  obtain ⟨u, hu_indep, hreg⟩ := h
  exact ⟨IntegralBasisInLSpace.ofRegularOutside T u hu_indep hreg⟩

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem linearIndependent_pow_mul {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by
  have heq : (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2)
      = (fun p : ℕ × Fin n => (x ^ p.1) • u p.2) := by
    funext p
    rw [Algebra.smul_def, map_pow]
  rw [heq]
  exact linearIndependent_smul (R := K) (S := E) (A := F) hx hu

def PoleDivisorPackage.ofTranscendenceTower (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    PoleDivisorPackage K F where
  x := T.xF
  B := T.poleDivisor
  hB_eff := T.poleDivisor_nonneg
  hx_mem := T.xF_mem_lSpace_poleDivisor
  n := Module.finrank E F
  hn_pos := Module.finrank_pos
  degB_eq := T.degree_poleDivisor_eq_finrank
  c := IB.c
  u := IB.u
  hu_mem := IB.hu_mem
  lin_indep := linearIndependent_pow_mul T.hx_indep IB.hu_indep

theorem hasPoleDivisorPackage_of_transcendenceTower
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    HasPoleDivisorPackage K F :=
  ⟨PoleDivisorPackage.ofTranscendenceTower T IB⟩

theorem hasPoleDivisorPackage_of_hasIntegralBasisInLSpace
    (T : TranscendenceTower K E F) (h : HasIntegralBasisInLSpace K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_transcendenceTower T h.some

theorem hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside
    (T : TranscendenceTower K E F) (h : HasIntegralBasisRegularOutside K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisInLSpace T
    (hasIntegralBasisInLSpace_of_regularOutside T h)

end AlgebraicCurve


end


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

namespace Place

export _root_.AlgebraicCurve.Place (ext coe_algebraMap ResidueField deg FiniteResidue adicValuation adicValuation_coe_eq_one_iff ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum mk.injEq rec ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mk ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap restrict mem_restrict_iff ord_restrict restrictInclusion coe_restrictInclusion inertiaDeg fiber mem_fiber mem_maximalIdeal_iff_ord_pos valuationSubringAlgebra integralClosureAt algebraMap_integralClosureAt_injective maximalIdeal_ne_bot forall_mem_of_restrict_eq fiberCenter mem_fiberCenter_iff_ord_pos toValuationSubring_eq_of_restrict_eq algebraMap_integralClosureAt_ne_zero ord_algebraMap_integralClosureAt fiberCenter_liesOver placeOfPrime restrict_placeOfPrime fiberCenter_placeOfPrime eq_of_fiberCenter_eq adicValuation_valuationSubring isEquiv_adicValuation_of_valuationSubring_eq mem_maximalIdeal_iff_adicValuation_lt_one ord_eq_zero_iff_adicValuation_eq_one DCoordGenerates differentialCoeff ordDifferential uniformizer ord_uniformizer uniformizer_ne_zero adicValuation_eq_exp_neg_ord LocalResidueData CanonicalLocalResidueDataK differentialCoeff_ne_zero)

open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_isIntegral {f : F} (hf : _root_.IsIntegral w.toValuationSubring f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hf
  exact hy ▸ y.2




theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_isIntegral_of_algebraMap_mem {A : Type*} [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : _root_.IsIntegral A f) : f ∈ w.toValuationSubring := by

  letI : Algebra A w.toValuationSubring :=
    ((algebraMap A F).codRestrict w.toValuationSubring.toSubring hA).toAlgebra
  haveI : IsScalarTower A w.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  exact w.mem_of_isIntegral hf.tower_top




end Place


section Bridge

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable {A : Type*} [CommRing A] [Algebra A E] [Algebra A F] [IsScalarTower A E F]

namespace Place
open scoped AlgebraicCurve.Place in
theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.mem_of_isIntegral_of_restrict [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : _root_.IsIntegral A f) : f ∈ w.toValuationSubring := by

  refine w.mem_of_isIntegral_of_algebraMap_mem (fun a => ?_) hf
  rw [IsScalarTower.algebraMap_apply A E F, ← w.mem_restrict_iff, hw]
  exact hA a

end Place



namespace Place
open scoped AlgebraicCurve.Place in
theorem _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ord_nonneg_of_isIntegral_of_restrict [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : _root_.IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_restrict hw hA hf)

end Place



variable (A) in

def TranscendenceTower.RegularOutside (T : TranscendenceTower K E F) : Prop :=
  ∀ u : Place K E, u ≠ T.v → ∀ a : A, algebraMap A E a ∈ u.toValuationSubring

theorem TranscendenceTower.ord_nonneg_of_isIntegral_of_regularOutside
    [Algebra.IsIntegral E F] (T : TranscendenceTower K E F) (hA : T.RegularOutside A)
    {f : F} (hf : _root_.IsIntegral A f) :
    ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f := fun w hw =>
  w.ord_nonneg_of_isIntegral_of_restrict rfl (hA _ hw) hf

end Bridge


section Headline

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

variable (K E F) in

def HasRegularFractionSubring (T : TranscendenceTower K E F) : Prop :=
  ∃ (A : Subalgebra K E), IsFractionRing A E ∧
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] in

theorem linearIndependent_reindex_basis {s : Finset F} (b : Basis s E F) :
    LinearIndependent E (fun i : Fin (Module.finrank E F) =>
      b ((Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm i)) :=
  b.linearIndependent.comp _ (Equiv.injective _)

omit [HasPrincipalDivisors K F] in

theorem hasIntegralBasisRegularOutside_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasIntegralBasisRegularOutside K E F T := by

  obtain ⟨s, b, hint⟩ := FiniteDimensional.exists_is_basis_integral A E F

  set e : Fin (Module.finrank E F) ≃ s :=
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm
  refine ⟨fun i => b (e i), linearIndependent_reindex_basis b, fun i w hw => ?_⟩

  exact T.ord_nonneg_of_isIntegral_of_regularOutside hA (hint (e i)) w hw

omit [HasPrincipalDivisors K F] in

theorem hasIntegralBasisRegularOutside_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasIntegralBasisRegularOutside K E F T := by
  obtain ⟨A, hfrac, hreg⟩ := h

  haveI : IsFractionRing A E := hfrac
  exact hasIntegralBasisRegularOutside_of_isFractionRing (A := A) T
    (fun u hu a => hreg u hu (a : E) a.property)

theorem hasPoleDivisorPackage_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T h)

theorem stichtenothGenusExists_of_hasRegularFractionSubring [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_hasRegularFractionSubring T h)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem TranscendenceTower.adjoin_x_regularOutside (T : TranscendenceTower K E F) :
    ∀ u : Place K E, u ≠ T.v →
      ∀ a ∈ Algebra.adjoin K {T.x}, a ∈ u.toValuationSubring := by
  intro u hu a ha

  let S : Subalgebra K E :=
    { u.toValuationSubring.toSubsemiring with
      algebraMap_mem' := u.algebraMap_mem' }
  suffices h : a ∈ S from h
  refine Algebra.adjoin_le ?_ ha
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  show T.x ∈ u.toValuationSubring
  exact u.mem_of_ord_nonneg T.x_ne_zero (T.hxreg u hu)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasRegularFractionSubring K E F T :=
  ⟨Algebra.adjoin K {T.x}, hfrac, T.adjoin_x_regularOutside⟩

theorem stichtenothGenusExists_of_adjoin_x_isFractionRing [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

end Headline


end AlgebraicCurve


end


end


end


section
section

noncomputable section

open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Module
open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.Polynomial

namespace AlgebraicCurve

export _root_.AlgebraicCurve (Place Place.ext Place.coe_algebraMap Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors Pic0 Place.ofHeightOneSpectrum HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.degree_pullback SumRamificationInertia Place.valuationSubringAlgebra Place.integralClosureAt Place.algebraMap_integralClosureAt_injective Place.placeOfPrime Place.restrict_placeOfPrime Place.mem_maximalIdeal_iff_adicValuation_lt_one IsCurveOver IsCurveOver.finite_residueField IsCurveOver.deg_eq_one_of_isAlgClosed Place.ordDifferential LSpace ell mem_lSpace_iff_ord lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase adeleBdd mem_adeleBdd adeleBdd_mono diagonalHom diagonal_mem_adeleBdd_iff adeleSpace adeleBdd_le_adeleSpace diagonal_mem_adeleSpace globalSub diagonal_mem_globalSub map_diagonal_lSpace indexOfSpecialty adeleBddPrincipal indexOfSpecialty_eq omegaSpace omegaSpace_vanishBdd omegaSpace_antitone omegaSpaceEquivIndexDual finrank_omegaSpace_eq_indexOfSpecialty weilDifferentialModule omegaSpace_le_weilDifferentialModule mem_weilDifferentialModule_iff mulAdele_apply adeleSpaceMul adeleSpaceMul_coe weilSmul weilSmul_apply weilSmul_one weilSmul_mul weilSmul_injective weilSmul_mem_omegaSpace_add residuePairing residuePairing_apply_coe residuePairing_injective WeilDifferentialRankOne RiemannGenusReachedAt RiemannGenusReached StichtenothGenusExists RiemannGenusBounded HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus HasLocalResidue HasCanonicalLocalResidueKStar single_mem_adeleBdd adeleSingle adeleSingle_coe HasSeparableResidue kaehlerResidueTermKFam kaehlerResidueTermKFam_apply weilOfKaehlerK weilOfKaehlerK_apply weilOfKaehlerK_vanish_adeleBdd_canonical ResidueTheoremK HasSeparableResidue.trace_ne_zero RiemannIndexFormula WeilDualityAdelic WeilDuality WeilOmegaEllAgrees FunctionFieldRiemannRoch functionFieldRiemannRoch_of_riemann_and_duality weilDuality_of_riemannIndex_of_adelic)

open _root_.AlgebraicCurve

section Transcendental

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem linearIndependent_pow_of_transcendental {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by
  have hinj : Function.Injective (Polynomial.aeval x : K[X] →ₐ[K] A) :=
    transcendental_iff_injective.mp hx

  have hXj : LinearIndependent K (fun j : ℕ => (X : K[X]) ^ j) := by
    have hb := (Polynomial.basisMonomials K).linearIndependent
    simp only [Polynomial.coe_basisMonomials] at hb
    convert hb using 2 with j
    exact (Polynomial.monomial_one_right_eq_X_pow j).symm
  have heq : (fun j : ℕ => x ^ j)
      = (fun j : ℕ => (Polynomial.aeval x : K[X] →ₐ[K] A) (X ^ j)) := by
    funext j; simp
  rw [heq]
  exact hXj.map' (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)

end Transcendental


namespace RationalFunctionField

export _root_.AlgebraicCurve.RationalFunctionField (algebraMap_mem_ofHeightOneSpectrum)

open _root_.AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem algebraMap_polynomial_mem_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ u.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty u with ⟨w, hw⟩ | hw
  · subst hw; exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd hw hu

theorem ord_X_nonneg_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X]
  exact u.ord_nonneg_of_mem (algebraMap_polynomial_mem_of_ne_placeInfty K hu Polynomial.X)

variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]

def transcendenceTower : TranscendenceTower K (RatFunc K) F where
  x := RatFunc.X
  hx_indep := linearIndependent_pow_of_transcendental RatFunc.transcendental_X
  v := placeInfty K
  hvdeg := deg_placeInfty K
  hxv := ord_placeInfty_X K
  hxreg := fun _ hu => ord_X_nonneg_of_ne_placeInfty K hu

omit [DecidableEq (RatFunc K)] in

theorem aeval_X_eq_algebraMap (q : K[X]) :
    (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K)) q
      = algebraMap K[X] (RatFunc K) q := by
  have hext : (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K))
      = IsScalarTower.toAlgHom K K[X] (RatFunc K) :=
    Polynomial.algHom_ext (by simp [RatFunc.algebraMap_X])
  rw [hext]; rfl

omit [DecidableEq (RatFunc K)] in

theorem algebraMap_polynomial_mem_adjoin_X (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Algebra.adjoin K {(RatFunc.X : RatFunc K)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨q, aeval_X_eq_algebraMap K q⟩

omit [DecidableEq (RatFunc K)] in

theorem isFractionRing_adjoin_X :
    IsFractionRing (Algebra.adjoin K {(RatFunc.X : RatFunc K)}) (RatFunc K) := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  refine ⟨⟨algebraMap K[X] (RatFunc K) z.num, algebraMap_polynomial_mem_adjoin_X K z.num⟩,
    ⟨algebraMap K[X] (RatFunc K) z.denom, algebraMap_polynomial_mem_adjoin_X K z.denom⟩, ?_⟩
  show z = algebraMap K[X] (RatFunc K) z.num / algebraMap K[X] (RatFunc K) z.denom
  exact z.num_div_denom.symm

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

variable [HasPrincipalDivisors K F]

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem stichtenothGenusExists_of_ratFunc_tower :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

end RationalFunctionField


end AlgebraicCurve


end


end


end

end P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
