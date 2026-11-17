import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionProducts
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPeriodConversion
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoefficientConjugation
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.KnownFieldCoefficientCoordinates
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DiamondProductFrames
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# Diamond rationality from an explicit finite torsion-product representation

The input is a given finite complex-linear representation on the principal
congruence subgroup by actual torsion-product forms. The argument descends its
coordinates to the cyclotomic field and uses all Fourier rows, residue transport,
and the invariance of a rational-coefficient form under coefficient conjugation.
It does not provide the representation or assert an unrestricted spanning theorem.
-/

set_option autoImplicit false
noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelDiamondFromProducts

open Torsion AllLevelForms AllLevelPrincipal AllLevelProducts
open ThetaFiveTorsion (act)

set_option quotPrecheck false in
local notation "ΓP" N => (Gamma N).map (mapGL ℝ)
set_option quotPrecheck false in
local notation "Γ1R" N => (Gamma1 N).map (mapGL ℝ)

variable {N : ℕ} [NeZero N] {J : Type*} [Fintype J]

/-- Congruent admissible tuples give the same actual product form. -/
theorem productForm_eq_of_congr
    (k : ℕ) (v w : Fin k → ℤ × ℤ)
    (hv : ∀ i, Good N (v i)) (hw : ∀ i, Good N (w i))
    (hvw : ∀ i, CongrN N (v i) (w i)) :
    productForm N (NeZero.pos N) k v hv = productForm N (NeZero.pos N) k w hw := by
  apply _root_.ModularForm.ext
  intro τ
  rw [productForm_apply, productForm_apply]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (F_eq_of_congr (NeZero.pos N) (hw i) (hvw i)) τ

/-- Slashing an actual finite product-form combination transports every tuple
by the same integral special-linear matrix. -/
theorem sum_products_slash
    (k : ℕ) (v : J → Fin k → ℤ × ℤ)
    (hv : ∀ j i, Good N (v j i)) (c : J → ℂ) (γ : SL(2, ℤ)) :
    ⇑(∑ j, c j • productForm N (NeZero.pos N) k (v j) (hv j) :
      _root_.ModularForm (ΓP N) (k : ℤ)) ∣[(k : ℤ)] γ =
    ⇑(∑ j, c j • productForm N (NeZero.pos N) k
      (fun i => act (v j i) γ) (good_act_tuple (hv j) γ) :
      _root_.ModularForm (ΓP N) (k : ℤ)) := by
  classical
  rw [FunLike.coe_sum, FunLike.coe_sum, SlashAction.sum_slash]
  apply Finset.sum_congr rfl
  intro j _
  rw [FunLike.coe_smul, FunLike.coe_smul, _root_.ModularForm.SL_smul_slash,
    productForm_slash]

/-- Every diamond translate has rational width-one coefficients when the given
principal restriction has an explicit finite torsion-product representation. -/
theorem diamond_coefficients_rational_of_product_representation
    (N : ℕ) [NeZero N] (k : ℕ)
    (g : _root_.ModularForm (Γ1R N) (k : ℤ))
    (hgQ : ∀ n, ∃ q : ℚ, (qExpansion 1 g).coeff n = (q : ℂ))
    (v : J → Fin k → ℤ × ℤ) (hv : ∀ j i, Good N (v j i))
    (c : J → ℂ)
    (hRep : _root_.ModularForm.restrict
      (Subgroup.map_mono (Gamma_le_Gamma1 N)) g =
      ∑ j, c j • productForm N (NeZero.pos N) k (v j) (hv j)) :
    ∀ u : (ZMod N)ˣ, ∀ n, ∃ q : ℚ,
      (qExpansion 1 (diamondOp (k : ℤ) u g)).coeff n = (q : ℂ) := by
  classical
  let K : IntermediateField ℚ ℂ := coefficientField N
  let gP : _root_.ModularForm (ΓP N) (k : ℤ) :=
    _root_.ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N)) g
  let F : J → _root_.ModularForm (ΓP N) (k : ℤ) := fun j =>
    productForm N (NeZero.pos N) k (v j) (hv j)
  have hF : ∀ j n, (qExpansion (N : ℝ) (F j)).coeff n ∈ K := fun j n =>
    productForm_coeff_mem k (v j) (hv j) n
  have hgPQ : ∀ n, ∃ q : ℚ, (qExpansion (N : ℝ) gP).coeff n = (q : ℂ) := by
    change ∀ n, ∃ q : ℚ, (qExpansion (N : ℝ) g).coeff n = (q : ℂ)
    exact (AllLevelPeriodConversion.rational_coefficients_iff N g).mpr hgQ
  have hgPK : ∀ n, (qExpansion (N : ℝ) gP).coeff n ∈ K := by
    intro n
    obtain ⟨q, hq⟩ := hgPQ n
    rw [hq]
    exact KnownFieldCoefficientCoordinates.rational_mem K q
  obtain ⟨d, hd⟩ := ModularFormCoefficientCoordinates.exists_coordinates
    (period_pos (N := N)) (period_mem_strictPeriods (N := N)) K F hF gP hgPK c hRep
  intro u
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) u
  let D : _root_.ModularForm (ΓP N) (k : ℤ) :=
    _root_.ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N))
      (diamondOp (k : ℤ) u g)
  let H : J → _root_.ModularForm (ΓP N) (k : ℤ) := fun j =>
    productForm N (NeZero.pos N) k (fun i => act (v j i) (γ : SL(2, ℤ)))
      (good_act_tuple (hv j) (γ : SL(2, ℤ)))
  have hH : ∀ j n, (qExpansion (N : ℝ) (H j)).coeff n ∈ K := fun j n =>
    productForm_coeff_mem k _ _ n
  have hD : D = ∑ j, (d j : ℂ) • H j := by
    apply DFunLike.coe_injective
    calc
      ⇑D = ⇑(diamondOp (k : ℤ) u g) := rfl
      _ = ⇑g ∣[(k : ℤ)] mapGL ℝ (γ : SL(2, ℤ)) := coe_diamondOp (k : ℤ) u γ hγ g
      _ = ⇑gP ∣[(k : ℤ)] (γ : SL(2, ℤ)) := rfl
      _ = ⇑(∑ j, (d j : ℂ) • F j : _root_.ModularForm (ΓP N) (k : ℤ))
          ∣[(k : ℤ)] (γ : SL(2, ℤ)) := by rw [hd]
      _ = ⇑(∑ j, (d j : ℂ) • H j : _root_.ModularForm (ΓP N) (k : ℤ)) :=
        sum_products_slash k v hv (fun j => (d j : ℂ)) (γ : SL(2, ℤ))
  have hDK : ∀ n, (qExpansion (N : ℝ) D).coeff n ∈ K := by
    intro n
    rw [hD]
    exact KnownFieldCoefficientCoordinates.combination_coeff_mem
      (period_pos (N := N)) (period_mem_strictPeriods (N := N)) K H hH d n
  have hfixed : ∀ σ : K ≃ₐ[ℚ] K, ∀ n,
      σ (⟨(qExpansion (N : ℝ) D).coeff n, hDK n⟩ : K) =
        (⟨(qExpansion (N : ℝ) D).coeff n, hDK n⟩ : K) := by
    intro σ
    obtain ⟨t, _, _, ht⟩ := AllLevelTorsionCoefficients.automorphism_root_power_nat N σ
    have htZ : σ (AllLevelTorsionCoefficients.zetaInField N) =
        AllLevelTorsionCoefficients.zetaInField N ^ (t : ℤ) := by
      simpa only [zpow_natCast] using ht
    let B : J → _root_.ModularForm (ΓP N) (k : ℤ) := fun j =>
      productForm N (NeZero.pos N) k (deltaTuple (t : ℤ) (v j))
        (deltaTuple_good (t : ℤ) (hv j) σ htZ)
    have hB : ∀ j n, (qExpansion (N : ℝ) (B j)).coeff n =
        (σ (⟨(qExpansion (N : ℝ) (F j)).coeff n, hF j n⟩ : K) : ℂ) :=
      fun j n => (productForm_coeff_galois (t : ℤ) k (v j) (hv j) σ htZ n).symm
    let gs : _root_.ModularForm (ΓP N) (k : ℤ) := ∑ j, (σ (d j) : ℂ) • B j
    have hgs : ∀ n, (qExpansion (N : ℝ) gs).coeff n =
        (σ (⟨(qExpansion (N : ℝ) gP).coeff n, hgPK n⟩ : K) : ℂ) :=
      KnownFieldCoefficientCoordinates.conjugate_coeff_of_known_coordinates
        (period_pos (N := N)) (period_mem_strictPeriods (N := N)) K F B hF σ hB gP hgPK d hd
    have hgs_eq : gs = gP :=
      ModularFormCoefficientConjugation.conjugate_eq_of_rational_coefficients
        (period_pos (N := N)) (period_mem_strictPeriods (N := N)) K σ gP gs hgPK hgs hgPQ
    let C : J → _root_.ModularForm (ΓP N) (k : ℤ) := fun j =>
      productForm N (NeZero.pos N) k
        (deltaTuple (t : ℤ) (fun i => act (v j i) (γ : SL(2, ℤ))))
        (deltaTuple_good (t : ℤ) (good_act_tuple (hv j) (γ : SL(2, ℤ))) σ htZ)
    have hC : ∀ j n, (qExpansion (N : ℝ) (C j)).coeff n =
        (σ (⟨(qExpansion (N : ℝ) (H j)).coeff n, hH j n⟩ : K) : ℂ) := fun j n =>
      (productForm_coeff_galois (t : ℤ) k _ _ σ htZ n).symm
    let Cs : _root_.ModularForm (ΓP N) (k : ℤ) := ∑ j, (σ (d j) : ℂ) • C j
    have hCs : ∀ n, (qExpansion (N : ℝ) Cs).coeff n =
        (σ (⟨(qExpansion (N : ℝ) D).coeff n, hDK n⟩ : K) : ℂ) :=
      KnownFieldCoefficientCoordinates.conjugate_coeff_of_known_coordinates
        (period_pos (N := N)) (period_mem_strictPeriods (N := N)) K H C hH σ hC D hDK d hD
    let γt : SL(2, ℤ) := gammaT (t : ℤ) (γ : SL(2, ℤ))
    let W : J → _root_.ModularForm (ΓP N) (k : ℤ) := fun j =>
      productForm N (NeZero.pos N) k
        (fun i => act (deltaTuple (t : ℤ) (v j) i) γt)
        (good_act_tuple (deltaTuple_good (t : ℤ) (hv j) σ htZ) γt)
    have hCW : ∀ j, C j = W j := by
      intro j
      apply productForm_eq_of_congr k _ _ _ _
      intro i
      exact delta_act_congr (t : ℤ) γ.property (v j i)
    have hCsW : Cs = ∑ j, (σ (d j) : ℂ) • W j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hCW j]
    have hγt : ⇑g ∣[(k : ℤ)] γt = ⇑g ∣[(k : ℤ)] (γ : SL(2, ℤ)) :=
      DiamondProductFrames.gammaT_slash_eq N (k : ℤ) g (t : ℤ) γ
    have hCs_eq : Cs = D := by
      apply DFunLike.coe_injective
      rw [hCsW]
      calc
        ⇑(∑ j, (σ (d j) : ℂ) • W j : _root_.ModularForm (ΓP N) (k : ℤ)) =
            ⇑gs ∣[(k : ℤ)] γt :=
          (sum_products_slash k (fun j => deltaTuple (t : ℤ) (v j))
            (fun j => deltaTuple_good (t : ℤ) (hv j) σ htZ)
            (fun j => (σ (d j) : ℂ)) γt).symm
        _ = ⇑gP ∣[(k : ℤ)] γt := by rw [hgs_eq]
        _ = ⇑g ∣[(k : ℤ)] γt := rfl
        _ = ⇑g ∣[(k : ℤ)] (γ : SL(2, ℤ)) := hγt
        _ = ⇑(diamondOp (k : ℤ) u g) := (coe_diamondOp (k : ℤ) u γ hγ g).symm
        _ = ⇑D := rfl
    intro n
    apply Subtype.ext
    have hn := hCs n
    rw [hCs_eq] at hn
    exact hn.symm
  have hDQ : ∀ n, ∃ q : ℚ, (qExpansion (N : ℝ) (diamondOp (k : ℤ) u g)).coeff n = (q : ℂ) := by
    intro n
    change ∃ q : ℚ, (qExpansion (N : ℝ) D).coeff n = (q : ℂ)
    exact DiamondProductFrames.rational_of_fixed N _ (hDK n) (fun σ => hfixed σ n)
  exact (AllLevelPeriodConversion.rational_coefficients_iff N (diamondOp (k : ℤ) u g)).mp hDQ

end ZInQ.Contrib.HeckePrimeRationality.AllLevelDiamondFromProducts
