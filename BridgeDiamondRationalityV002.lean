import BridgeFrameConjugationV001
import DirectCoefficientSaturationV004
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.KnownFieldCoefficientCoordinates

/-!
# Actual diamond rationality by localized coefficient descent

The finite axis coordinates are produced from the proved localized
representation. Both numerator membership and coefficient conjugation are
then derived using that same coordinate vector. The actual conjugate
denominator need not equal the original denominator. Cancellation uses
its nonzero power series, never a nonzero constant coefficient.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace BridgeDiamondRationality

open ZInQ.Contrib.HeckePrimeRationality
open DirectTorsionOrbit DirectOrbitInterpolation
open BridgeDenominator BridgeLambda BridgeSeries BridgeAxisFrame BridgeFrameConjugation

/-- Every actual Gamma-one diamond preserves rational period-one coefficients at level at least three.
No arithmetic basis, numerator membership, or Galois-closure premise is supplied. -/
theorem diamond_coefficients_rational (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ)) :
    ∀ (u : (ZMod N)ˣ) (n : ℕ), ∃ q : ℚ,
      (qExpansion 1 (diamondOp k u g)).coeff n = (q : ℂ) := by
  classical
  let K : IntermediateField ℚ ℂ := Torsion.coefficientField N
  let W : ℤ := k + 2 * orbitWeight N
  have hperiod := TauCeti.one_mem_strictPeriods_Gamma1_map N
  obtain ⟨J, hJ, e, R, c, hR, hrep⟩ := exists_actual_axis_coordinates N hN k g hg
  letI := hJ
  let F : (ZMod N)ˣ → J → ModularForm ((Gamma1 N).map (mapGL ℝ)) W := fun u i =>
    axisTerm N hN W (e i : ℕ) (R i) u
  have hFK (u : (ZMod N)ˣ) : ∀ i n, (qExpansion 1 (F u i)).coeff n ∈ K :=
    fun i => axisTerm_coefficients_mem N hN W (e i : ℕ) (R i) (hR i) u
  have hFdiamond (u v : (ZMod N)ˣ) (i : J) :
      diamondOp W u (F v i) = F (u * v) i :=
    diamond_axisTerm N hN W (e i : ℕ) (R i) u v
  have hrep' : denominatorProduct N hN k g = ∑ i, (c i : ℂ) • F 1 i := hrep
  have htranslate (u : (ZMod N)ˣ) :
      denominatorProduct N hN k (diamondOp k u g) = ∑ i, (c i : ℂ) • F u i := by
    have h := congrArg (diamondOp W u) hrep'
    rw [diamond_denominatorProduct] at h
    simp only [map_sum, map_smul, hFdiamond, mul_one] at h
    exact h
  have hnumK (u : (ZMod N)ˣ) :
      ∀ n, (qExpansion 1 (denominatorProduct N hN k (diamondOp k u g))).coeff n ∈ K := by
    rw [htranslate u]
    exact KnownFieldCoefficientCoordinates.combination_coeff_mem one_pos hperiod K (F u) (hFK u) c
  intro u
  let A : PowerSeries ℂ := qExpansion 1 (DirectLocalizedTorsionGeneration.denominator N hN)
  let B : PowerSeries ℂ := qExpansion 1 (diamondOp k u g)
  have hAK : ∀ n, A.coeff n ∈ K := denominator_coefficients_mem N hN
  have hA0 : A ≠ 0 := denominator_qExpansion_ne_zero N hN
  have hABK : ∀ n, (A * B).coeff n ∈ K := by
    simpa only [denominatorProduct_qExpansion] using hnumK u
  have hBK : ∀ n, B.coeff n ∈ K :=
    DirectCoefficientSaturation.coefficients_mem_of_nonzero_mul K A B hA0 hAK hABK
  have hfixed : ∀ σ : K ≃ₐ[ℚ] K, ∀ n,
      σ (⟨B.coeff n, hBK n⟩ : K) = (⟨B.coeff n, hBK n⟩ : K) := by
    intro σ
    let s : (ZMod N)ˣ := galoisUnit N hN σ
    have hcov (v : (ZMod N)ˣ) :
        qExpansion 1 (∑ i, (σ (c i) : ℂ) • F (s * v) i :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) W) =
          conjugateSeries K σ (qExpansion 1 (denominatorProduct N hN k (diamondOp k v g))) (hnumK v) := by
      have hFcov : ∀ i n, (qExpansion 1 (F (s * v) i)).coeff n =
          (σ (⟨(qExpansion 1 (F v i)).coeff n, hFK v i n⟩ : K) : ℂ) := by
        intro i n
        have h := congrArg (fun P : PowerSeries ℂ => P.coeff n)
          (axisTerm_series_conjugate N hN W (e i : ℕ) (R i) (hR i) σ v)
        rw [conjugateSeries_coeff] at h
        exact h.symm
      ext n
      rw [conjugateSeries_coeff]
      exact KnownFieldCoefficientCoordinates.conjugate_coeff_of_known_coordinates
        one_pos hperiod K (F v) (F (s * v)) (hFK v) σ hFcov
          (denominatorProduct N hN k (diamondOp k v g)) (hnumK v) c (htranslate v) n
    have hfirst : (∑ i, (σ (c i) : ℂ) • F s i :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) W) = conjugateProduct N hN k σ g := by
      apply ModularForm.qExpansion_injective one_pos hperiod
      have h := hcov 1
      simp only [mul_one] at h
      have hOne : diamondOp k (1 : (ZMod N)ˣ) g = g := by
        rw [_root_.diamondOp_one k, LinearMap.id_apply]
      have hProdOne : denominatorProduct N hN k (diamondOp k (1 : (ZMod N)ˣ) g) =
          denominatorProduct N hN k g := congrArg (denominatorProduct N hN k) hOne
      have hconjOne := conjugateSeries_congr K σ _ _ (hnumK 1)
        (denominatorProduct_coefficients_mem N hN k g hg)
        (congrArg (fun f : ModularForm ((Gamma1 N).map (mapGL ℝ)) W => qExpansion 1 f) hProdOne)
      exact h.trans (hconjOne.trans (denominatorProduct_series_conjugate N hN k g hg σ))
    have htranslated : (∑ i, (σ (c i) : ℂ) • F (s * u) i :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) W) =
          conjugateProduct N hN k σ (diamondOp k u g) := by
      have h := congrArg (diamondOp W u) hfirst
      rw [diamond_conjugateProduct] at h
      simp only [map_sum, map_smul, hFdiamond] at h
      simpa only [mul_comm u s] using h
    have hintertwining :
        conjugateSeries K σ (qExpansion 1 (denominatorProduct N hN k (diamondOp k u g))) (hnumK u) =
          qExpansion 1 (conjugateProduct N hN k σ (diamondOp k u g)) :=
      (hcov u).symm.trans (congrArg (fun f : ModularForm ((Gamma1 N).map (mapGL ℝ)) W => qExpansion 1 f) htranslated)
    have hproduct :
        qExpansion 1 (conjugateDenominator N hN σ) * conjugateSeries K σ B hBK =
          qExpansion 1 (conjugateDenominator N hN σ) * B := by
      calc
        qExpansion 1 (conjugateDenominator N hN σ) * conjugateSeries K σ B hBK =
            conjugateSeries K σ A hAK * conjugateSeries K σ B hBK := by
          rw [denominator_series_conjugate]
        _ = conjugateSeries K σ (A * B) (coefficients_mem_mul K A B hAK hBK) :=
          (conjugateSeries_mul K σ A B hAK hBK).symm
        _ = conjugateSeries K σ
            (qExpansion 1 (denominatorProduct N hN k (diamondOp k u g))) (hnumK u) :=
          (conjugateSeries_congr K σ _ _ (hnumK u) (coefficients_mem_mul K A B hAK hBK)
            (denominatorProduct_qExpansion N hN k (diamondOp k u g))).symm
        _ = qExpansion 1 (conjugateProduct N hN k σ (diamondOp k u g)) := hintertwining
        _ = qExpansion 1 (conjugateDenominator N hN σ) * B :=
          conjugateProduct_qExpansion N hN k σ (diamondOp k u g)
    have hzero : qExpansion 1 (conjugateDenominator N hN σ) *
        (conjugateSeries K σ B hBK - B) = 0 := by
      rw [mul_sub, hproduct, sub_self]
    have hBfixed : conjugateSeries K σ B hBK = B :=
      sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (conjugateDenominator_qExpansion_ne_zero N hN σ))
    intro n
    apply Subtype.ext
    have h := congrArg (fun P : PowerSeries ℂ => P.coeff n) hBfixed
    simpa only [conjugateSeries_coeff] using h
  intro n
  exact DiamondProductFrames.rational_of_fixed N (B.coeff n) (hBK n) (fun σ => hfixed σ n)

/-- The actual cusp-form specialization uses the unchanged cusp object and actual diamond. -/
theorem cusp_diamond_coefficients_rational (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ)) :
    ∀ (u : (ZMod N)ˣ) (n : ℕ), ∃ q : ℚ,
      (qExpansion 1 (diamondOpCusp k u g)).coeff n = (q : ℂ) := by
  intro u n
  have h := diamond_coefficients_rational N hN k (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) hg u n
  rw [diamondOp_coe_cuspForm] at h
  exact h

end BridgeDiamondRationality
