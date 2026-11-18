import BridgeAxisFrameV002
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DiamondProductFrames

/-!
# Coefficient conjugation of the derived actual axis frame

One cyclotomic unit is derived for each coefficient automorphism. The
rational level-one frame factors are fixed, while the raw torsion factor
is transported by that unit. The actual conjugate denominator is kept
separate from the original denominator throughout.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace BridgeFrameConjugation

open ZInQ.Contrib.HeckePrimeRationality
open DirectTorsionOrbit DirectOrbitInterpolation
open BridgeDenominator BridgeLambda BridgeSeries BridgeAxisFrame

/-- Equality of actual series transports coefficient conjugation across membership proofs. -/
theorem conjugateSeries_congr (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (A B : PowerSeries ℂ) (hA : ∀ n, A.coeff n ∈ K) (hB : ∀ n, B.coeff n ∈ K)
    (h : A = B) : conjugateSeries K σ A hA = conjugateSeries K σ B hB := by
  subst B
  rfl

/-- The genuine unit produced by the actual torsion coefficient dictionary. -/
def galoisUnit (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) : (ZMod N)ˣ :=
  Classical.choose (BridgeLambda.exists_galois_unit N hN σ)

/-- All actual raw unit forms obey the same derived coefficient-series covariance. -/
theorem lambdaForm_series_conjugate (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) (u : (ZMod N)ˣ) :
    conjugateSeries (Torsion.coefficientField N) σ (qExpansion 1 (lambdaForm N hN u))
      (lambdaForm_coefficients_mem N hN u) =
        qExpansion 1 (lambdaForm N hN (galoisUnit N hN σ * u)) := by
  ext n
  rw [conjugateSeries_coeff]
  exact Classical.choose_spec (BridgeLambda.exists_galois_unit N hN σ) u n

/-- The actual level-one conjugate denominator realizes precisely the derived coefficient operation. -/
theorem denominator_series_conjugate (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) :
    conjugateSeries (Torsion.coefficientField N) σ
      (qExpansion 1 (DirectLocalizedTorsionGeneration.denominator N hN))
      (denominator_coefficients_mem N hN) = qExpansion 1 (conjugateDenominator N hN σ) := by
  ext n
  rw [conjugateSeries_coeff, conjugateDenominator_coeff]

/-- The coefficient conjugate of a genuine fixed-weight frame term is its actual unit transport. -/
theorem axisTerm_series_conjugate (N : ℕ) [NeZero N] (hN : 3 ≤ N) (W : ℤ) (j : ℕ)
    (R : ModularForm 𝒮ℒ (W - (j : ℤ))) (hR : DirectLevelOneArithmetic.IsRat R)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) (u : (ZMod N)ˣ) :
    conjugateSeries (Torsion.coefficientField N) σ
      (qExpansion 1 (axisTerm N hN W j R u)) (axisTerm_coefficients_mem N hN W j R hR u) =
        qExpansion 1 (axisTerm N hN W j R (galoisUnit N hN σ * u)) := by
  let K := Torsion.coefficientField N
  have hRK : ∀ n, (qExpansion 1 R).coeff n ∈ K := by
    intro n
    obtain ⟨q, hq⟩ := hR n
    rw [hq]
    exact KnownFieldCoefficientCoordinates.rational_mem K q
  have hLK := lambdaForm_coefficients_mem N hN u
  have hLP := coefficients_mem_pow K (qExpansion 1 (lambdaForm N hN u)) hLK j
  calc
    conjugateSeries K σ (qExpansion 1 (axisTerm N hN W j R u))
        (axisTerm_coefficients_mem N hN W j R hR u) =
        conjugateSeries K σ (qExpansion 1 R * qExpansion 1 (lambdaForm N hN u) ^ j)
          (coefficients_mem_mul K _ _ hRK hLP) :=
      conjugateSeries_congr K σ _ _ _ _ (axisTerm_qExpansion N hN W j R u)
    _ = conjugateSeries K σ (qExpansion 1 R) hRK *
        conjugateSeries K σ (qExpansion 1 (lambdaForm N hN u) ^ j) hLP :=
      conjugateSeries_mul K σ _ _ hRK hLP
    _ = qExpansion 1 R * conjugateSeries K σ (qExpansion 1 (lambdaForm N hN u)) hLK ^ j := by
      rw [conjugateSeries_eq_of_rational K σ _ hRK hR, conjugateSeries_pow]
    _ = qExpansion 1 R * qExpansion 1 (lambdaForm N hN (galoisUnit N hN σ * u)) ^ j := by
      rw [lambdaForm_series_conjugate]
    _ = qExpansion 1 (axisTerm N hN W j R (galoisUnit N hN σ * u)) :=
      (axisTerm_qExpansion N hN W j R _).symm

/-- The conjugate denominator times an arbitrary original form, in the same actual target space. -/
def conjugateProduct (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) (k + 2 * orbitWeight N) :=
  ModularForm.mcast (by ring) ((restrictLevelOne N _ (conjugateDenominator N hN σ)).mul g)

/-- Its exact actual width-one series product. -/
theorem conjugateProduct_qExpansion (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion 1 (conjugateProduct N hN k σ g) =
      qExpansion 1 (conjugateDenominator N hN σ) * qExpansion 1 g := by
  simp only [conjugateProduct, ModularForm.coe_mcast]
  rw [ModularForm.qExpansion_mul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
  rfl

/-- Actual level-one invariance of the denominator makes diamond transport multiplicative in the original product. -/
theorem diamond_denominatorProduct (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (u : (ZMod N)ˣ) :
    diamondOp (k + 2 * orbitWeight N) u (denominatorProduct N hN k g) =
      denominatorProduct N hN k (diamondOp k u g) := by
  rw [denominatorProduct, diamond_mcast, BridgeLambda.diamond_mul, diamond_restrictLevelOne]
  rfl

/-- The distinct actual conjugate denominator is invariant under the same diamond, without rationality. -/
theorem diamond_conjugateProduct (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (u : (ZMod N)ˣ) :
    diamondOp (k + 2 * orbitWeight N) u (conjugateProduct N hN k σ g) =
      conjugateProduct N hN k σ (diamondOp k u g) := by
  rw [conjugateProduct, diamond_mcast, BridgeLambda.diamond_mul, diamond_restrictLevelOne]
  rfl

/-- Rationality of the original input identifies the conjugated original product with D_sigma times g. -/
theorem denominatorProduct_series_conjugate (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ))
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) :
    conjugateSeries (Torsion.coefficientField N) σ (qExpansion 1 (denominatorProduct N hN k g))
      (denominatorProduct_coefficients_mem N hN k g hg) =
        qExpansion 1 (conjugateProduct N hN k σ g) := by
  let K := Torsion.coefficientField N
  have hgK : ∀ n, (qExpansion 1 g).coeff n ∈ K := by
    intro n
    obtain ⟨q, hq⟩ := hg n
    rw [hq]
    exact KnownFieldCoefficientCoordinates.rational_mem K q
  have hDK := denominator_coefficients_mem N hN
  calc
    conjugateSeries K σ (qExpansion 1 (denominatorProduct N hN k g))
        (denominatorProduct_coefficients_mem N hN k g hg) =
        conjugateSeries K σ
          (qExpansion 1 (DirectLocalizedTorsionGeneration.denominator N hN) * qExpansion 1 g)
          (coefficients_mem_mul K _ _ hDK hgK) :=
      conjugateSeries_congr K σ _ _ _ _ (denominatorProduct_qExpansion N hN k g)
    _ = conjugateSeries K σ (qExpansion 1 (DirectLocalizedTorsionGeneration.denominator N hN)) hDK *
        conjugateSeries K σ (qExpansion 1 g) hgK := conjugateSeries_mul K σ _ _ hDK hgK
    _ = qExpansion 1 (conjugateDenominator N hN σ) * qExpansion 1 g := by
      rw [denominator_series_conjugate, conjugateSeries_eq_of_rational K σ _ hgK hg]
    _ = qExpansion 1 (conjugateProduct N hN k σ g) := (conjugateProduct_qExpansion N hN k σ g).symm

/-- Flattened actual rational level-one factors and field-valued coordinates, derived from the proved frame. -/
theorem exists_actual_axis_coordinates (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ)) :
    ∃ J : Type, ∃ hJ : Fintype J,
      letI := hJ
      ∃ e : J → Fin (orbitLength N),
      ∃ R : (i : J) → ModularForm 𝒮ℒ (k + 2 * orbitWeight N - (e i : ℤ)),
      ∃ c : J → Torsion.coefficientField N,
        (∀ i, DirectLevelOneArithmetic.IsRat (R i)) ∧
          denominatorProduct N hN k g =
            ∑ i, (c i : ℂ) • axisTerm N hN (k + 2 * orbitWeight N) (e i : ℕ) (R i) 1 := by
  classical
  obtain ⟨J, hJ, F, c, hF, hrep⟩ := exists_field_frame_coordinates N hN k g hg
  letI := hJ
  change ∀ i, ∃ j : Fin (orbitLength N),
    ∃ R : ModularForm 𝒮ℒ (k + 2 * orbitWeight N - (j : ℤ)),
      DirectLevelOneArithmetic.IsRat R ∧ F i = axisTerm N hN (k + 2 * orbitWeight N) (j : ℕ) R 1 at hF
  choose e R hR he using hF
  refine ⟨J, hJ, e, R, c, hR, ?_⟩
  rw [hrep]
  exact Finset.sum_congr rfl (fun i _ => by rw [he i])

end BridgeFrameConjugation
