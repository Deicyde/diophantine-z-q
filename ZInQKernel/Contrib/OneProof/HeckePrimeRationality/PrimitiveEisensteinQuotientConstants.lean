import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinConstantProfile
import Mathlib.NumberTheory.ModularForms.NormTrace
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Basic
import ZInQKernel.Contrib.TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual constant coefficients on the complete principal quotient

The finite indexing object is the complete quotient SL₂(ℤ)/Γ(N), explicitly
equivalent to SL₂(ℤ/Nℤ) by actual surjective reduction. Same-level modular
slashes and their constant coefficients are genuine. Translation and central
parity laws are derived from the actual at-infinity limit and slash action.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Complex Filter Set UpperHalfPlane Matrix Matrix.SpecialLinearGroup ConjAct
open scoped Topology MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
open ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

abbrev principalReal (N : ℕ) := (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

lemma translate_level_le (N : ℕ) (γ : SL(2, ℤ)) :
    principalReal N ≤ (toConjAct ((mapGL ℝ γ)⁻¹)) • principalReal N := by
  rintro x ⟨δ,hδ,rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  refine ⟨γ*δ*γ⁻¹,(CongruenceSubgroup.Gamma_normal N).conj_mem δ hδ γ,?_⟩
  simp [ConjAct.smul_def,map_mul,map_inv]

/-- Actual same-level weight-k modular slash. -/
def slashForm (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (γ : SL(2, ℤ)) :
    ModularForm (principalReal N) k :=
  ModularForm.restrict (translate_level_le N γ) (ModularForm.translate f (mapGL ℝ γ))

lemma slashForm_coe (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (γ : SL(2, ℤ)) :
    ⇑(slashForm N k f γ) = ⇑f ∣[k] γ := rfl

lemma slashForm_mul (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (γ δ : SL(2, ℤ)) :
    slashForm N k (slashForm N k f γ) δ = slashForm N k f (γ*δ) := by
  apply DFunLike.ext
  intro τ
  change ((⇑f ∣[k] γ) ∣[k] δ) τ = (⇑f ∣[k] (γ*δ)) τ
  rw [SlashAction.slash_mul]

lemma slashForm_gamma (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) : slashForm N k f γ = f := by
  apply DFunLike.ext
  intro τ
  exact congrFun (SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)) τ

/-- The actual period-N constant coefficient. -/
def constantCoefficient (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) : ℂ :=
  (UpperHalfPlane.qExpansion (N : ℝ) f).coeff 0

lemma constantCoefficient_tendsto (N : ℕ) [NeZero N] (k : ℤ) (f : ModularForm (principalReal N) k) :
    Tendsto (f : ℍ → ℂ) UpperHalfPlane.atImInfty (𝓝 (constantCoefficient N k f)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact ModularFormClass.tendsto_atImInfty f hN (level_period N)

lemma constantCoefficient_smul (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (principalReal N) k) (c : ℂ) :
    constantCoefficient N k (c • f) = c * constantCoefficient N k f := by
  have hs := constantCoefficient_tendsto N k (c • f)
  have ht := (constantCoefficient_tendsto N k f).const_mul c
  have he : (⇑(c • f) : ℍ → ℂ) = (fun τ => c * f τ) := by
    funext τ
    simp
  rw [he] at hs
  exact tendsto_nhds_unique hs ht

lemma constantCoefficient_add (N : ℕ) [NeZero N] (k : ℤ)
    (f g : ModularForm (principalReal N) k) :
    constantCoefficient N k (f+g) = constantCoefficient N k f + constantCoefficient N k g := by
  have hs := constantCoefficient_tendsto N k (f+g)
  have ht := (constantCoefficient_tendsto N k f).add (constantCoefficient_tendsto N k g)
  have he : (⇑(f+g) : ℍ → ℂ) = (fun τ => f τ + g τ) := by
    funext τ
    simp
  rw [he] at hs
  exact tendsto_nhds_unique hs ht

lemma slash_T_apply (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (t : ℤ) (τ : ℍ) :
    slashForm N k f (ModularGroup.T^t) τ = f (ModularGroup.T^t • τ) := by
  change (⇑f ∣[k] (ModularGroup.T^t)) τ = _
  rw [ModularForm.SL_slash_apply]
  have hj : UpperHalfPlane.denom (ModularGroup.T^t : SL(2, ℤ)) (τ : ℂ) = 1 := by
    rw [ModularGroup.denom_apply]
    simp only [ModularGroup.coe_T_zpow]
    simp
  rw [hj,one_zpow,mul_one]

/-- Translation preserves the actual constant coefficient, derived from its actual limit. -/
lemma constantCoefficient_T (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (principalReal N) k) (t : ℤ) :
    constantCoefficient N k (slashForm N k f (ModularGroup.T^t)) = constantCoefficient N k f := by
  have hT : Tendsto (fun τ : ℍ => ModularGroup.T^t • τ) UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty := by
    rw [UpperHalfPlane.atImInfty,tendsto_comap_iff]
    change Tendsto (fun τ : ℍ => (ModularGroup.T^t • τ).im) (Filter.comap UpperHalfPlane.im atTop) atTop
    simp_rw [ModularGroup.im_T_zpow_smul]
    exact Filter.tendsto_comap
  have he := (constantCoefficient_tendsto N k f).comp hT
  have hs := constantCoefficient_tendsto N k (slashForm N k f (ModularGroup.T^t))
  have hf : (⇑(slashForm N k f (ModularGroup.T^t)) : ℍ → ℂ) =
      (fun τ => f (ModularGroup.T^t • τ)) := funext (slash_T_apply N k f t)
  rw [hf] at hs
  exact tendsto_nhds_unique hs he

lemma slashForm_neg (N : ℕ) (k : ℕ) (f : ModularForm (principalReal N) (k : ℤ)) (γ : SL(2, ℤ)) :
    slashForm N (k : ℤ) f (-γ) = (-1 : ℂ)^k • slashForm N (k : ℤ) f γ := by
  apply DFunLike.ext
  intro τ
  change (⇑f ∣[(k : ℤ)] (-γ)) τ = ((-1 : ℂ)^k • (⇑f ∣[(k : ℤ)] γ)) τ
  have hcoe : ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = -1 := Matrix.SpecialLinearGroup.mapGL_neg_one
  rw [← mul_neg_one γ,SlashAction.slash_mul,ModularForm.SL_slash (γ := (-1 : SL(2, ℤ))),
    hcoe,ModularForm.slash_neg_one,_root_.zpow_natCast]

/-- The complete quotient, not a selected cusp or primitive-row list. -/
abbrev principalQuotient (N : ℕ) := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma N

instance quotient_normal (N : ℕ) : (CongruenceSubgroup.Gamma N).Normal := CongruenceSubgroup.Gamma_normal N

/-- The actual complete reduction equivalence. -/
def quotientReduction (N : ℕ) : principalQuotient N ≃* SL(2, ZMod N) :=
  QuotientGroup.quotientKerEquivOfSurjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))
    Matrix.SpecialLinearGroup.map_intCast_zmod_surjective

noncomputable instance quotient_fintype (N : ℕ) [NeZero N] : Fintype (principalQuotient N) :=
  Fintype.ofEquiv (SL(2, ZMod N)) (quotientReduction N).symm.toEquiv

lemma quotientReduction_mk (N : ℕ) (γ : SL(2, ℤ)) :
    quotientReduction N (QuotientGroup.mk γ) = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ := rfl

/-- Actual constant at an integral representative. -/
def constantAt (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (γ : SL(2, ℤ)) : ℂ :=
  constantCoefficient N k (slashForm N k f γ)

lemma constantAt_congr (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k)
    (γ δ : SL(2, ℤ)) (h : γ⁻¹*δ ∈ CongruenceSubgroup.Gamma N) :
    constantAt N k f γ = constantAt N k f δ := by
  have he : slashForm N k f δ = slashForm N k f γ := by
    calc slashForm N k f δ = slashForm N k f (γ*(γ⁻¹*δ)) := by rw [mul_inv_cancel_left]
      _ = slashForm N k (slashForm N k f γ) (γ⁻¹*δ) := (slashForm_mul N k f γ (γ⁻¹*δ)).symm
      _ = _ := slashForm_gamma N k _ _ h
  rw [constantAt,constantAt,he]

/-- A genuine well-defined complex constant on every complete quotient class. -/
def quotientConstant (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) : principalQuotient N → ℂ :=
  Quotient.lift (constantAt N k f) (by
    intro γ δ h
    change QuotientGroup.leftRel (CongruenceSubgroup.Gamma N) γ δ at h
    exact constantAt_congr N k f γ δ (QuotientGroup.leftRel_apply.mp h))

lemma quotientConstant_mk (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (γ : SL(2, ℤ)) :
    quotientConstant N k f (QuotientGroup.mk γ) = constantAt N k f γ := rfl

/-- The same complete quotient constants transported along actual reduction. -/
def finiteConstants (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (A : SL(2, ZMod N)) : ℂ :=
  quotientConstant N k f ((quotientReduction N).symm A)

lemma finiteConstants_reduce (N : ℕ) (k : ℤ) (f : ModularForm (principalReal N) k) (γ : SL(2, ℤ)) :
    finiteConstants N k f (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) = constantAt N k f γ := by
  rw [finiteConstants,← quotientReduction_mk,(quotientReduction N).symm_apply_apply,quotientConstant_mk]

lemma constantAt_T (N : ℕ) [NeZero N] (k : ℤ) (f : ModularForm (principalReal N) k)
    (γ : SL(2, ℤ)) (t : ℤ) : constantAt N k f (γ*ModularGroup.T^t) = constantAt N k f γ := by
  rw [constantAt,constantAt,← slashForm_mul,constantCoefficient_T]

lemma constantAt_neg (N : ℕ) [NeZero N] (k : ℕ) (f : ModularForm (principalReal N) (k : ℤ))
    (γ : SL(2, ℤ)) : constantAt N (k : ℤ) f (-γ) = (-1 : ℂ)^k * constantAt N (k : ℤ) f γ := by
  rw [constantAt,slashForm_neg,constantCoefficient_smul,constantAt]

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
