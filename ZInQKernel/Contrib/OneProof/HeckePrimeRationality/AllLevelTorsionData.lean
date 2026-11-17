import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionForms
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCoefficients
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# The explicit torsion family and its diamond/Galois dictionary

These theorems concern the constructed weight-one forms with row label `(0,b)`.
They connect the actual diamond operators to coefficientwise automorphisms of
an explicit cyclotomic field. They do not assert that this family spans all
modular forms, or that arbitrary integral forms have rational diamond images.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionData

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open ZInQ.Contrib.HeckePrimeRationality.Torsion

variable (N : ℕ) [NeZero N]

/-- Coefficient membership for the actual bundled modular form. -/
theorem torsionForm_coeff_mem (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) (n : ℕ) :
    (qExpansion 1 (AllLevelForms.torsionForm N (NeZero.pos N) b hb)).coeff n ∈
      coefficientField N :=
  AllLevelTorsionCoefficients.torsion_coeff_mem N b hb n

/-- The lower-right label of a Γ₀ representative preserves admissibility,
including nonprimitive torsion labels at composite levels. -/
lemma representative_admissible (γ : ↥(Gamma0 N)) (b : ℤ)
    (hb : ¬ (N : ℤ) ∣ b) : ¬ (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 1 * b := by
  intro hdb
  have hc : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (CongruenceSubgroup.Gamma0_mem.mp γ.2)
  have hd : (γ : SL(2, ℤ)) 0 0 * (γ : SL(2, ℤ)) 1 1 -
      (γ : SL(2, ℤ)) 0 1 * (γ : SL(2, ℤ)) 1 0 = 1 := by
    have hdet := (γ : SL(2, ℤ)).property
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  have hdiv : (N : ℤ) ∣ (γ : SL(2, ℤ)) 0 0 * ((γ : SL(2, ℤ)) 1 1 * b) -
      (γ : SL(2, ℤ)) 0 1 * ((γ : SL(2, ℤ)) 1 0 * b) :=
    dvd_sub (Dvd.dvd.mul_left hdb _) (Dvd.dvd.mul_left (Dvd.dvd.mul_right hc b) _)
  have heq : (γ : SL(2, ℤ)) 0 0 * ((γ : SL(2, ℤ)) 1 1 * b) -
      (γ : SL(2, ℤ)) 0 1 * ((γ : SL(2, ℤ)) 1 0 * b) = b := by
    linear_combination b * hd
  exact hb (heq ▸ hdiv)

/-- Evaluation of the actual diamond on the explicit torsion family, at an
arbitrary Γ₀ representative. -/
theorem diamond_torsionForm (d : (ZMod N)ˣ) (γ : ↥(Gamma0 N))
    (hγ : (Gamma0Map N).toHomUnits γ = d) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    diamondOp 1 d (AllLevelForms.torsionForm N (NeZero.pos N) b hb) =
      AllLevelForms.torsionForm N (NeZero.pos N) ((γ : SL(2, ℤ)) 1 1 * b)
        (representative_admissible N γ b hb) := by
  apply DFunLike.coe_injective
  rw [coe_diamondOp 1 d γ hγ]
  change AllLevelForms.F N (0, b) ∣[(1 : ℤ)] (γ : SL(2, ℤ)) =
    AllLevelForms.F N (0, (γ : SL(2, ℤ)) 1 1 * b)
  rw [AllLevelForms.F_slash (NeZero.pos N) _ (0, b) (by exact fun h => hb h.2)]
  have hc : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (CongruenceSubgroup.Gamma0_mem.mp γ.2)
  obtain ⟨m, hm⟩ := hc
  have hact : ThetaFiveTorsion.act (0, b) (γ : SL(2, ℤ)) =
      (0 + N * (b * m), (γ : SL(2, ℤ)) 1 1 * b + N * 0) := by
    refine Prod.ext ?_ ?_ <;> simp [ThetaFiveTorsion.act, hm] <;> ring
  rw [hact]
  funext τ
  exact AllLevelForms.F_shift (NeZero.pos N)
    (by exact fun h => representative_admissible N γ b hb h.2) (b * m) 0 τ

/-- Congruent labels give exactly the same constructed form. -/
lemma torsionForm_eq_of_label (b c : ℤ) (hb : ¬ (N : ℤ) ∣ b)
    (hc : ¬ (N : ℤ) ∣ c) (hbc : (b : ZMod N) = (c : ZMod N)) :
    AllLevelForms.torsionForm N (NeZero.pos N) b hb =
      AllLevelForms.torsionForm N (NeZero.pos N) c hc := by
  have hdiv : (N : ℤ) ∣ c - b := (ZMod.intCast_eq_intCast_iff_dvd_sub b c N).mp hbc
  obtain ⟨m, hm⟩ := hdiv
  apply ModularForm.ext
  intro τ
  change AllLevelForms.F N (0, b) τ = AllLevelForms.F N (0, c) τ
  have heq : c = b + N * m := by omega
  rw [heq]
  symm
  simpa using AllLevelForms.F_shift (NeZero.pos N) (a := 0) (b := b)
    (by exact fun h => hb h.2) 0 m τ

/-- Every actual cyclotomic automorphism has a diamond label realizing its
coefficient action on this explicit family. The label is derived, not a
caller-supplied arithmetic structure. No full-space spanning is asserted. -/
theorem galois_diamond_dictionary
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N) :
    ∃ d : (ZMod N)ˣ, ∀ (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) (n : ℕ),
      ((σ ⟨(qExpansion 1 (AllLevelForms.torsionForm N (NeZero.pos N) b hb)).coeff n,
          torsionForm_coeff_mem N b hb n⟩ : coefficientField N) : ℂ) =
        (qExpansion 1 (diamondOp 1 d (AllLevelForms.torsionForm N (NeZero.pos N) b hb))).coeff n := by
  obtain ⟨t, _, hcop, hroot⟩ := AllLevelTorsionCoefficients.automorphism_root_power_nat N σ
  let d : (ZMod N)ˣ := ZMod.unitOfCoprime t hcop
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  have hlabel : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (t : ZMod N) := by
    have h := congrArg Units.val hγ
    simpa [MonoidHom.coe_toHomUnits, Gamma0Map_apply, d] using h
  have hσ : σ (AllLevelTorsionCoefficients.zetaInField N) =
      AllLevelTorsionCoefficients.zetaInField N ^ (t : ℤ) := by
    simpa only [zpow_natCast] using hroot
  refine ⟨d, ?_⟩
  intro b hb n
  have htgood : ¬ (N : ℤ) ∣ (t : ℤ) * b :=
    AllLevelTorsionCoefficients.automorphism_admissible N b (t : ℤ) hb σ hσ
  have hforms := torsionForm_eq_of_label N ((γ : SL(2, ℤ)) 1 1 * b) ((t : ℤ) * b)
    (representative_admissible N γ b hb) htgood (by simpa using congrArg (fun x : ZMod N => x * b) hlabel)
  have hdform : diamondOp 1 d (AllLevelForms.torsionForm N (NeZero.pos N) b hb) =
      AllLevelForms.torsionForm N (NeZero.pos N) ((t : ℤ) * b) htgood :=
    (diamond_torsionForm N d γ hγ b hb).trans hforms
  rw [hdform]
  exact AllLevelTorsionCoefficients.torsion_coeff_galois N b (t : ℤ) hb σ hσ n

end ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionData
