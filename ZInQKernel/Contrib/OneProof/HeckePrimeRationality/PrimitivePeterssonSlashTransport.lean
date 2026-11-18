import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonInfinityOrthogonality
import ZInQKernel.Contrib.TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Actual integral transport from the infinity Eisenstein series

Normality gives actual same-level cusp translates. Primitive residue rows
lift to integral special-linear matrices, and change of variables in the
actual invariant measure transports the independently proved infinity
unfolding to every coprime residue row.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set UpperHalfPlane Complex Matrix Matrix.SpecialLinearGroup ConjAct
open scoped Topology MatrixGroups ModularForm Pointwise ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

lemma principal_translate_level (N : ℕ) (γ : SL(2, ℤ)) :
    ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) ≤
      (toConjAct ((mapGL ℝ γ)⁻¹)) • ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) := by
  rintro x ⟨δ,hδ,rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hγδ : γ*δ*γ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem δ hδ γ
  refine ⟨γ*δ*γ⁻¹,hγδ,?_⟩
  simp [ConjAct.smul_def,ConjAct.toConjAct_inv,map_mul,map_inv]

/-- A genuine same-level cusp form with underlying function f|γ. -/
def principalCuspSlash (N : ℕ) (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) k :=
  CuspForm.restrict (principal_translate_level N γ) (CuspForm.translate f (mapGL ℝ γ))

lemma principalCuspSlash_coe (N : ℕ) (k : ℤ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    ⇑(principalCuspSlash N k f γ) = ⇑f ∣[k] γ := rfl

theorem infinity_primitive_zero_on_domain (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (D : Set ℍ) (hD : IsFundamentalDomain (CongruenceSubgroup.Gamma N) D volume) :
    UpperHalfPlane.peterssonInner (k : ℤ) D f
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) (infinityRow N)) = 0 := by
  have hz := periodizedSeed_integral_zero N k hk f D hD
  simp_rw [periodizedSeed_eq_actual_eisenstein] at hz
  exact hz

lemma principalDomain_translate_fundamental (N : ℕ) (hN : 3 ≤ N) (γ : SL(2, ℤ)) :
    IsFundamentalDomain (CongruenceSubgroup.Gamma N) (γ • principalDomain N) volume := by
  exact (principalDomain_fundamental N hN).smul_of_eq_conjAct_pointwise_smul
    (measurePreserving_smul γ⁻¹ volume).quasiMeasurePreserving
    (CongruenceSubgroup.Gamma_cong_eq_self N (toConjAct γ)).symm

/-- Surjective reduction supplies an actual integral primitive-row lift. -/
theorem primitive_residue_row_lift (N : ℕ) (a : Fin 2 → ZMod N)
    (ha : IsCoprime (a 0) (a 1)) :
    ∃ γ : SL(2, ℤ), infinityRow N ᵥ* γ = a := by
  obtain ⟨A,_,hA⟩ := ModularGroup.bottom_row_surj ha
  obtain ⟨γ,hγ⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := N) A
  have hrow (i : Fin 2) : (γ 1 i : ZMod N) = a i := by
    have he := congrArg (fun B : SL(2, ZMod N) => B 1 i) hγ
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,
      Matrix.map_apply,Int.coe_castRingHom,hA] using he
  refine ⟨γ,?_⟩
  have he : infinityRow N ᵥ* γ = (fun i => (γ 1 i : ZMod N)) := by
    ext i
    simp [infinityRow,Matrix.vecMul,Fin.sum_univ_two]
    rfl
  rw [he]
  ext i
  exact hrow i

/-- Change of variables for the true Petersson integrand. -/
lemma pairing_slash_change_variables (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (γ : SL(2, ℤ)) :
    UpperHalfPlane.peterssonInner (k : ℤ) (principalDomain N) f
      ((⇑(ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) (infinityRow N))) ∣[(k : ℤ)] γ) =
    UpperHalfPlane.peterssonInner (k : ℤ) (γ • principalDomain N)
      (principalCuspSlash N (k : ℤ) f γ⁻¹)
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) (infinityRow N)) := by
  let E := ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) (infinityRow N)
  have he (τ : ℍ) : UpperHalfPlane.petersson (k : ℤ) f (⇑E ∣[(k : ℤ)] γ) τ =
      UpperHalfPlane.petersson (k : ℤ) (principalCuspSlash N (k : ℤ) f γ⁻¹) E (γ • τ) := by
    have hp := UpperHalfPlane.petersson_slash_SL (k : ℤ) (⇑f ∣[(k : ℤ)] γ⁻¹) E γ τ
    rw [← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one] at hp
    exact hp
  unfold UpperHalfPlane.peterssonInner
  change (∫ τ in principalDomain N, UpperHalfPlane.petersson (k : ℤ) f (⇑E ∣[(k : ℤ)] γ) τ) =
    (∫ τ in γ • principalDomain N, UpperHalfPlane.petersson (k : ℤ) (principalCuspSlash N (k : ℤ) f γ⁻¹) E τ)
  simp_rw [he]
  rw [← Set.image_smul]
  exact ((measurePreserving_smul γ volume).setIntegral_image_emb
    (measurableEmbedding_const_smul _) _ _).symm

/-- Every coprime row is orthogonal by actual integral transport. -/
theorem coprime_primitive_eisenstein_petersson_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) (ha : IsCoprime (a 0) (a 1))
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    UpperHalfPlane.peterssonInner (k : ℤ) (principalDomain N) f
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a) = 0 := by
  obtain ⟨γ,hγ⟩ := primitive_residue_row_lift N a ha
  have he : ⇑(ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a) =
      ⇑(ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) (infinityRow N)) ∣[(k : ℤ)] γ := by
    change eisensteinSeries a (k : ℤ) = eisensteinSeries (infinityRow N) (k : ℤ) ∣[(k : ℤ)] γ
    rw [EisensteinSeries.eisensteinSeries_slash_apply,hγ]
  rw [he,pairing_slash_change_variables N hN k hk f γ]
  exact infinity_primitive_zero_on_domain N k hk _ _ (principalDomain_translate_fundamental N hN γ)

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson
