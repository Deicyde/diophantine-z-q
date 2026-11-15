import RayGlueO
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Integers

/-! # rayclass-cft, Part G2: the glue `QHatIntegral`, proved

Integral finite adeles of `k` come from `ℤ̂ ⊗ 𝒪_k` under Tau Ceti's base change
(`exists_integral_preimage`, the integral branch of Tau Ceti's private
`exists_semilocalHom_sum_tmul_eq`, re-proved from its public lemmas), so `q̂(𝒪̂_k) ⊆ 𝒪̂` when
`q(𝒪_k) ⊆ 𝒪`; a congruence idele `a` of `3·𝒪_k` is `1 + 3b` with `b` integral. -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open IsDedekindDomain NumberField
open scoped TensorProduct FiniteAdeleExtension AdicCompletionExtension
open ShimuraCFT TauCeti TauCeti.GlobalNumberFields

variable {k : Type} [Field k] [NumberField k]

/-- Integral components above `v` come from `∑ cᵢ ⊗ bᵢ` with `cᵢ ∈ 𝒪_v` (the integral branch of
Tau Ceti's private `exists_semilocalHom_sum_tmul_eq`, same proof). -/
theorem exists_integral_coeffs {K : Type} [Field K] [NumberField K] [Algebra K k]
    (v : HeightOneSpectrum (𝓞 K))
    (z : (w : {w : HeightOneSpectrum (𝓞 k) // w.asIdeal.LiesOver v.asIdeal}) →
      w.1.adicCompletion k)
    (hz : ∀ w, z w ∈ w.1.adicCompletionIntegers k) :
    ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 k) → v.adicCompletion K,
      semilocalHom k v (∑ i, c i ⊗ₜ[K] (RingOfIntegers.basis k i : k)) = z ∧
      ∀ i, c i ∈ v.adicCompletionIntegers K := by
  classical
  let b := RingOfIntegers.basis k
  obtain ⟨ζ, hζ⟩ := (integralSemilocalEquiv k v).surjective fun w ↦ ⟨z w, hz w⟩
  have hspan : Submodule.span (v.adicCompletionIntegers K)
      (Set.range fun i ↦ (1 : v.adicCompletionIntegers K) ⊗ₜ[𝓞 K] b i) = ⊤ := by
    have h := Submodule.baseChange_span (R := 𝓞 K) (v.adicCompletionIntegers K) (Set.range b)
    rw [Submodule.span_eq_top_of_span_eq_top ℤ (𝓞 K) _ b.span_eq, Submodule.baseChange_top,
      ← Set.range_comp] at h
    exact h.symm
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    (hspan ▸ Submodule.mem_top : ζ ∈ Submodule.span _ _)
  refine ⟨fun i ↦ c i, ?_, fun i ↦ (c i).2⟩
  have h := integralSemilocalEquiv_fieldCompatibility ζ
  rw [hζ, ← hc, map_sum] at h
  simp_rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    integralSemilocalToField_tmul, coe_semilocalEquiv] at h
  exact h

/-- **Integral finite adeles of `k` come from `ℤ̂ ⊗ 𝒪_k`.** -/
theorem exists_integral_preimage {K : Type} [Field K] [NumberField K] [Algebra K k]
    (y : FiniteAdeleRing (𝓞 k) k)
    (hy : ∀ w, y w ∈ w.adicCompletionIntegers k) :
    ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 k) → FiniteAdeleRing (𝓞 K) K,
      (∀ i v, a i v ∈ v.adicCompletionIntegers K) ∧
      finiteAdeleBaseChangeHom K k (∑ i, a i ⊗ₜ[K] (RingOfIntegers.basis k i : k)) = y := by
  classical
  choose c hc hci using fun v : HeightOneSpectrum (𝓞 K) ↦
    exists_integral_coeffs v (fun w ↦ y w.1) (fun w ↦ hy w.1)
  let a (i : Module.Free.ChooseBasisIndex ℤ (𝓞 k)) : FiniteAdeleRing (𝓞 K) K :=
    ⟨fun v ↦ c v i, Filter.Eventually.of_forall fun v ↦ hci v i⟩
  refine ⟨a, fun i v => hci v i, FiniteAdeleRing.ext k fun w ↦ ?_⟩
  rw [finiteAdeleBaseChangeHom_apply K k _ (w.under (𝓞 K)) ⟨w, inferInstance⟩]
  convert congrFun (hc (w.under (𝓞 K))) ⟨w, inferInstance⟩ using 2
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
    ContinuousAlgHom.coe_coe, FiniteAdeleRing.proj_apply]
  rfl

theorem algebraMap_mul_mem {a : AQ} (ha : a ∈ ZhatQ) {x : BAQ} (hx : x ∈ OhatQ) :
    algebraMap AQ BAQ a * x ∈ OhatQ := by
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨fun i => a * n i, fun i => ZhatS.mul_mem ha (hn i), ?_⟩
  ext <;> simp [ShimuraGlue.ofQ, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem OhatQ_zero : (0 : BAQ) ∈ OhatQ := ⟨0, fun i => ZhatS.zero_mem, by simp [ShimuraGlue.ofQ_zero]⟩

/-- **`q̂(𝒪̂_k) ⊆ 𝒪̂` when `q(𝒪_k) ⊆ 𝒪`.** -/
theorem qHat_mem_OhatQ (q : k →ₐ[ℚ] LeafQM.B) (hq : ∀ x : 𝓞 k, LeafQM.InO (q x))
    (y : FiniteAdeleRing (𝓞 k) k) (hy : ∀ w, y w ∈ w.adicCompletionIntegers k) :
    qHat q y ∈ OhatQ := by
  obtain ⟨a, ha, hpre⟩ := exists_integral_preimage (K := ℚ) y hy
  have hs : (finiteAdeleBaseChangeAlgEquiv ℚ k).symm y =
      ∑ i, a i ⊗ₜ[ℚ] (RingOfIntegers.basis k i : k) := by
    rw [AlgEquiv.symm_apply_eq]; exact hpre.symm
  show (qT q) ((finiteAdeleBaseChangeAlgEquiv ℚ k).symm y) ∈ OhatQ
  rw [hs, map_sum]
  refine Finset.sum_induction _ (· ∈ OhatQ) (fun _ _ => OhatQ_add) OhatQ_zero fun i _ => ?_
  simp only [qT, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.comp_apply]
  exact algebraMap_mul_mem (ha i) (bEmb_mem_of_inO (hq _))

end RayClassCFT

namespace RayClassCFT

open IsDedekindDomain NumberField
open ShimuraCFT TauCeti TauCeti.GlobalNumberFields ShimuraGlue.Ray

variable {k : Type} [Field k] [NumberField k]

theorem qHatU_coe (q : k →ₐ[ℚ] LeafQM.B) (s : IdeleGroup (𝓞 k) k) :
    ((qHatU q s : BAQˣ) : BAQ) = qHat q ((IdeleGroup.toFiniteIdele (𝓞 k) k s :
      FiniteAdeleRing (𝓞 k) k)) := rfl

/-- `v(3) = exp(−e_v)`, `e_v` the exponent of `v` in `3·𝒪_k`. -/
theorem valued_three (w : HeightOneSpectrum (𝓞 k)) :
    Valued.v ((3 : k) : w.adicCompletion k) = WithZero.exp (-((mod3 k).exponent w : ℤ)) := by
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h3 : (3 : k) = algebraMap (𝓞 k) k 3 := (map_ofNat _ 3).symm
  rw [h3, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ (by
      exact_mod_cast (show ((3 : ℕ) : 𝓞 k) ≠ 0 from Nat.cast_ne_zero.2 (by norm_num)))]
  rfl

/-- **A congruence idele of `3·𝒪_k` is `1 + 3b` with `b` integral.** -/
theorem cong_sub_one_div_three {s : IdeleGroup (𝓞 k) k}
    (hs : s ∈ ideleCongruenceSubgroup (mod3 k)) (w : HeightOneSpectrum (𝓞 k)) :
    (((IdeleGroup.toFiniteIdele (𝓞 k) k s : FiniteAdeleRing (𝓞 k) k) - 1) *
      algebraMap k (FiniteAdeleRing (𝓞 k) k) (1 / 3)) w ∈ w.adicCompletionIntegers k := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hn : w.asIdeal ^ ((mod3 k).exponent w) ∣ (mod3 k).finitePart :=
    ((mod3 k).pow_dvd_finitePart_iff_le_exponent w).2 le_rfl
  have h1 := ideleCongruenceSubgroup.valued_snd_sub_one_le_of_pow_dvd hs hn
  have e : (((IdeleGroup.toFiniteIdele (𝓞 k) k s : FiniteAdeleRing (𝓞 k) k) - 1) *
      algebraMap k (FiniteAdeleRing (𝓞 k) k) (1 / 3)) w =
      ((s : AdeleRing (𝓞 k) k).2 w - 1) * ((1 / 3 : k) : w.adicCompletion k) := rfl
  rw [e, map_mul]
  have h3 : Valued.v ((1 / 3 : k) : w.adicCompletion k) =
      (WithZero.exp (-((mod3 k).exponent w : ℤ)))⁻¹ := by
    rw [← valued_three, ← map_inv₀]
    congr 1
    have ha : ∀ x : k, (x : w.adicCompletion k) = algebraMap k (w.adicCompletion k) x := fun x => rfl
    rw [ha, ha, ← map_inv₀]
    congr 1
    norm_num
  rw [h3]
  calc Valued.v ((s : AdeleRing (𝓞 k) k).2 w - 1) * (WithZero.exp (-((mod3 k).exponent w : ℤ)))⁻¹
      ≤ WithZero.exp (-((mod3 k).exponent w : ℤ)) *
          (WithZero.exp (-((mod3 k).exponent w : ℤ)))⁻¹ := by
        gcongr
    _ = 1 := mul_inv_cancel₀ (WithZero.exp_ne_zero)

/-- **The glue `QHatIntegral`, proved** (for every number field `k`). -/
theorem qHatIntegral (k : Type) [Field k] [NumberField k] : QHatIntegral k := by
  intro q hq s hs
  set a : FiniteAdeleRing (𝓞 k) k := (IdeleGroup.toFiniteIdele (𝓞 k) k s : FiniteAdeleRing (𝓞 k) k)
  set b : FiniteAdeleRing (𝓞 k) k := (a - 1) * algebraMap k (FiniteAdeleRing (𝓞 k) k) (1 / 3)
  have hint : ∀ t ∈ ideleCongruenceSubgroup (mod3 k), ∀ w : HeightOneSpectrum (𝓞 k),
      (IdeleGroup.toFiniteIdele (𝓞 k) k t : FiniteAdeleRing (𝓞 k) k) w ∈ w.adicCompletionIntegers k :=
    fun t ht w => ideleCongruenceSubgroup.snd_mem_adicCompletionIntegers ht w
  have hab : a = 1 + 3 * b := by
    have h3 : (3 : FiniteAdeleRing (𝓞 k) k) * algebraMap k (FiniteAdeleRing (𝓞 k) k) (1 / 3) = 1 := by
      rw [show (3 : FiniteAdeleRing (𝓞 k) k) = algebraMap k (FiniteAdeleRing (𝓞 k) k) 3 from
          (map_ofNat _ 3).symm,
        ← map_mul]; norm_num
    calc a = 1 + (a - 1) * ((3 : FiniteAdeleRing (𝓞 k) k) *
          algebraMap k (FiniteAdeleRing (𝓞 k) k) (1 / 3)) := by rw [h3]; ring
      _ = 1 + 3 * b := by simp only [b]; ring
  refine ⟨?_, ?_, qHat q b, qHat_mem_OhatQ q hq b (cong_sub_one_div_three hs), ?_⟩
  · rw [qHatU_coe]; exact qHat_mem_OhatQ q hq a (hint s hs)
  · rw [← map_inv, qHatU_coe]
    exact qHat_mem_OhatQ q hq _ (hint s⁻¹ (Subgroup.inv_mem _ hs))
  · rw [qHatU_coe]
    show qHat q a = 1 + 3 * qHat q b
    rw [hab, map_add, map_one, map_mul, map_ofNat]

/-- **`RayClassCM` with the glue `RingOfIntegersGen` and `QHatIntegral` discharged.** -/
theorem rayClassCM_of3 (hL : ShimuraMainThmIDeligneY3AbU)
    (hMR : LeafQM.AV.R1UnivRigid.MumfordRigidityCore) (hCN : ClassNumberOneB)
    (hB : CMBaseChange) (hA : CMAnalytic) : RayClassCM :=
  rayClassCM_of2 hL hMR hCN (qHatIntegral K4) (qHatIntegral K3) (qHatIntegral K24) hB hA

end RayClassCFT

#print axioms RayClassCFT.qHatIntegral
#print axioms RayClassCFT.rayClassCM_of3
