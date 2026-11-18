import hecke.RationalTranslateOrbit
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.Normal
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.SturmBound
import ZInQKernel.Contrib.TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A good-Hecke joint eigencomponent inside a rational translate orbit

The actual rational translate submodule is invariant under the actual good
Hecke family. The family is commuting and semisimple for the actual Petersson
pairing, so its restriction to that finite-dimensional submodule has a nonzero
joint eigencomponent. No ambient basis vector is presumed to belong to the orbit.
-/

noncomputable section
set_option autoImplicit false

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open HeckeRing.GL2
open scoped MatrixGroups ModularForm Function

namespace ZInQ.Contrib.HeckePrimeRationality.ReverseHecke

/-- All primes away from the actual level, not a finite chosen subset. -/
abbrev GoodPrimeIndex (L : ℕ) := {p : ℕ // p.Prime ∧ p.Coprime L}

/-- The canonical actual good-prime Hecke-ring action on one character space. -/
def goodFamily (L : ℕ) [NeZero L] (k : ℤ) (χ : (ZMod L)ˣ →* ℂˣ) :
    GoodPrimeIndex L → Module.End ℂ (cuspFormCharSpace k χ) :=
  fun i ↦ heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 L i.val)

/-- The actual character orbit is invariant under every good-prime Hecke operator. -/
theorem characterOrbit_invariant (L : ℕ) [NeZero L] (k : ℤ)
    (χ : (ZMod L)ˣ →* ℂˣ) (f : ℍ → ℂ) :
    ∀ i : GoodPrimeIndex L, ∀ g ∈ characterOrbit L k χ f,
      goodFamily L k χ i g ∈ characterOrbit L k χ f := by
  intro i g hg
  change (goodFamily L k χ i g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) ∈ cuspOrbit L k f
  rw [goodFamily, coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ i.property.1]
  let : NeZero i.val := ⟨i.property.1.ne_zero⟩
  exact heckeTCuspNat_mem_cuspOrbit L k f i.val hg

/-- The actual good-prime operators commute, by the proved commutative Hecke-ring action. -/
theorem goodFamily_pairwise_commute (L : ℕ) [NeZero L] (k : ℤ)
    (χ : (ZMod L)ˣ →* ℂˣ) : Pairwise (Commute on goodFamily L k χ) := by
  intro i j _
  exact Commute.map
    (HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution L)
      (atkinLehnerAntiInvolution_onHeckeCoset_eq_self L) _ _)
    (heckeRingHomCuspCharSpace k χ)

section PeterssonSemisimple

variable (L : ℕ) [NeZero L] (k : ℤ) (χ : (ZMod L)ˣ →* ℂˣ)

noncomputable local instance actualPeterssonCore :
    InnerProductSpace.Core ℂ (CuspForm ((Gamma1 L).map (mapGL ℝ)) k) :=
  CuspForm.peterssonInnerCosetsCore

noncomputable local instance actualPeterssonNorm :
    NormedAddCommGroup (CuspForm ((Gamma1 L).map (mapGL ℝ)) k) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

noncomputable local instance actualPeterssonInner :
    InnerProductSpace ℂ (CuspForm ((Gamma1 L).map (mapGL ℝ)) k) :=
  InnerProductSpace.ofCore _

/-- The local inner product on the actual character space is the genuine coset Petersson pairing. -/
theorem character_inner_eq (g h : cuspFormCharSpace k χ) :
    inner ℂ g h = CuspForm.peterssonInnerCosets
      (g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) h := by
  rw [Submodule.coe_inner]
  exact CuspForm.peterssonInnerCosetsCore_inner _ _

/-- Every actual good Hecke operator has a nonzero scalar making it Petersson symmetric. -/
theorem exists_symmetric_smul_goodFamily (i : GoodPrimeIndex L) :
    ∃ c : ℂ, c ≠ 0 ∧ (c • goodFamily L k χ i).IsSymmetric := by
  obtain ⟨c, hc_sq⟩ := IsAlgClosed.exists_pow_nat_eq
    ((χ (ZMod.unitOfCoprime i.val i.property.2) : ℂ)⁻¹) (show 0 < 2 by omega)
  have hc_ne : c ≠ 0 := by
    intro hc
    rw [hc, zero_pow (by omega)] at hc_sq
    exact inv_ne_zero (mod_cast Units.ne_zero (χ (ZMod.unitOfCoprime i.val i.property.2))) hc_sq.symm
  have hconj_mul : starRingEnd ℂ c * c = 1 := by
    have hnorm_sq : ‖c‖ ^ 2 = 1 := by
      rw [← norm_pow, hc_sq]
      simpa only [map_inv, Units.coeHom_apply] using ((Units.coeHom ℂ).isOfFinOrder
        (MonoidHom.isOfFinOrder χ
          (isOfFinOrder_of_finite (ZMod.unitOfCoprime i.val i.property.2))).inv).norm_eq_one
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm_sq,
      Complex.ofReal_one]
  refine ⟨c, hc_ne, fun g h ↦ ?_⟩
  have hadj := isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0
    (χ := χ) k i.property.1 i.property.2 h g
  simp only [LinearMap.flip_apply,
    TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ_apply_apply, Pi.smul_apply,
    Submodule.coe_smul, CuspForm.peterssonInnerCosets_smul_left] at hadj
  rw [character_inner_eq L k χ, character_inner_eq L k χ]
  simp only [goodFamily, LinearMap.smul_apply, Submodule.coe_smul,
    CuspForm.peterssonInnerCosets_smul_left, CuspForm.peterssonInnerCosets_smul_right]
  have hcc : c * starRingEnd ℂ c ^ 2 = starRingEnd ℂ c := by
    rw [pow_two, ← mul_assoc, mul_comm c (starRingEnd ℂ c), hconj_mul, one_mul]
  rw [hadj, ← hc_sq, map_pow, ← mul_assoc, hcc]

/-- Semisimplicity is proved for the actual operator, not supplied as a family premise. -/
theorem goodFamily_isSemisimple (i : GoodPrimeIndex L) :
    (goodFamily L k χ i).IsSemisimple := by
  obtain ⟨c, hc, hs⟩ := exists_symmetric_smul_goodFamily L k χ i
  have hss : (c • goodFamily L k χ i).IsSemisimple :=
    Module.End.isFinitelySemisimple_iff_isSemisimple.mp hs.isFinitelySemisimple
  exact (Module.End.IsSemisimple_smul_iff hc).mp hss

end PeterssonSemisimple

/-- The actual invariant character orbit decomposes in the entire good-prime joint family. -/
theorem characterOrbit_joint_decomposition (L : ℕ) [NeZero L] (k : ℤ)
    (χ : (ZMod L)ˣ →* ℂˣ) (f : ℍ → ℂ) :
    (⨆ a : GoodPrimeIndex L → ℂ,
      characterOrbit L k χ f ⊓ ⨅ i, (goodFamily L k χ i).eigenspace (a i)) =
        characterOrbit L k χ f := by
  let p := characterOrbit L k χ f
  have hp := characterOrbit_invariant L k χ f
  have hcomm : Pairwise fun i j ↦ Commute
      ((goodFamily L k χ i).restrict (hp i)) ((goodFamily L k χ j).restrict (hp j)) := by
    intro i j hij
    exact LinearMap.restrict_commute (goodFamily_pairwise_commute L k χ hij) (hp i) (hp j)
  have hss : ∀ i, Module.End.IsSemisimple ((goodFamily L k χ i).restrict (hp i)) := fun i ↦
    (goodFamily_isSemisimple L k χ i).restrict (hp i)
  exact TauCeti.iSup_inf_iInf_eigenspace_of_invariant (goodFamily L k χ) p hp hcomm hss

/-- A nonzero element of the actual orbit yields a nonzero joint eigencomponent inside it. -/
theorem exists_nonzero_good_joint_component (L : ℕ) [NeZero L] (k : ℤ)
    (χ : (ZMod L)ˣ →* ℂˣ) (f : ℍ → ℂ)
    (g : cuspFormCharSpace k χ) (hg0 : g ≠ 0) (hg : g ∈ characterOrbit L k χ f) :
    ∃ a : GoodPrimeIndex L → ℂ, ∃ h : cuspFormCharSpace k χ,
      h ≠ 0 ∧ h ∈ characterOrbit L k χ f ∧
        ∀ i, goodFamily L k χ i h = a i • h := by
  classical
  have hp0 : characterOrbit L k χ f ≠ ⊥ := by
    intro hp
    rw [hp] at hg
    exact hg0 ((Submodule.mem_bot ℂ).mp hg)
  have hne : ∃ a : GoodPrimeIndex L → ℂ,
      characterOrbit L k χ f ⊓ ⨅ i, (goodFamily L k χ i).eigenspace (a i) ≠ ⊥ := by
    by_contra hnone
    push Not at hnone
    apply hp0
    rw [← characterOrbit_joint_decomposition L k χ f]
    simp only [hnone, iSup_bot]
  obtain ⟨a, ha⟩ := hne
  obtain ⟨h, hh, hh0⟩ := (Submodule.ne_bot_iff _).mp ha
  refine ⟨a, h, hh0, hh.1, fun i ↦ ?_⟩
  exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hh.2 i)

/-- From the original principal cusp form, produce an actual nonzero good-Hecke eigencomponent
in a finite positive-rational translate representation. No newness is asserted. -/
theorem principal_goodHecke_component (N : ℕ) [NeZero N] (k : ℕ) (_hk : 2 ≤ k)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) (k : ℤ)) (hf : f ≠ 0) :
    ∃ χ : (ZMod (N ^ 2))ˣ →* ℂˣ,
      ∃ F : CuspForm ((Gamma1 (N ^ 2)).map (mapGL ℝ)) (k : ℤ),
        F ≠ 0 ∧ F ∈ cuspFormCharSpace (k : ℤ) χ ∧
          (∃ a : GoodPrimeIndex (N ^ 2) → ℂ,
            ∀ (p : ℕ) (hp : p.Prime) (hpL : p.Coprime (N ^ 2)),
              heckeTCuspNat (k : ℤ) p (_hn := ⟨hp.ne_zero⟩) F = a ⟨p, hp, hpL⟩ • F) ∧
          ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ α : Fin m → GL (Fin 2) ℚ,
            (∀ i, 0 < (α i : Matrix (Fin 2) (Fin 2) ℚ).det) ∧
              ⇑F = ∑ i, c i • (⇑f ∣[(k : ℤ)] Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (α i)) := by
  obtain ⟨χ, g, hg0, hg⟩ := exists_nonzero_characterOrbit N (k : ℤ) f hf
  obtain ⟨a, h, hh0, hhorbit, heig⟩ := exists_nonzero_good_joint_component
    (N ^ 2) (k : ℤ) χ ⇑f g hg0 hg
  refine ⟨χ, h.val, fun hz ↦ hh0 (Subtype.ext hz), h.property, ⟨a, ?_⟩, ?_⟩
  · intro p hp hpL
    have hE := congrArg Subtype.val (heig ⟨p, hp, hpL⟩)
    simpa only [goodFamily, coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 (k : ℤ) χ hp,
      Submodule.coe_smul] using hE
  · exact functionOrbit_representation (k : ℤ) ⇑f hhorbit

end ZInQ.Contrib.HeckePrimeRationality.ReverseHecke
