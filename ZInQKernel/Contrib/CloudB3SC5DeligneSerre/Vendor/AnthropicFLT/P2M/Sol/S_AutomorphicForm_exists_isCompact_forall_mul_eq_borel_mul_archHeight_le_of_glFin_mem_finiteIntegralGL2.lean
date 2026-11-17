/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 (git blob ae4c1424f056626537ab2260452182d087a8a6e9, sha256 f3f725b26e1e055d703b9c24b176411663fa621a653a7aa3af4c8485825e5f20).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WindowedSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace B3Translate

variable (F : Type) [Field F] [NumberField F]




theorem continuous_entry (i j : Fin 2) : Continuous fun g : (AdelicGL2 (𝓞 F) F) => ((g : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j :=
  (Units.continuous_val.matrix_elem i j)

theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) := by
  have : (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) = (fun g : (AdelicGL2 (𝓞 F) F) => ((g : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) ⁻¹' {0} := by
    ext g; exact mem_borelSubgroup_iff _
  rw [this]
  exact isClosed_singleton.preimage (continuous_entry F 1 0)

noncomputable def hgt (b : ↥(adelicBorel (𝓞 F) F)) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (borelDiagFst b) / NumberField.TateGlobal.ideleNorm F (borelDiagSnd b)

theorem hgt_mul (b c : ↥(adelicBorel (𝓞 F) F)) : hgt F (b * c) = hgt F b * hgt F c := by
  simp only [hgt, map_mul, NumberField.TateGlobal.ideleNorm_mul]
  rw [mul_div_mul_comm]

theorem hgt_pos (b : ↥(adelicBorel (𝓞 F) F)) : 0 < hgt F b :=
  div_pos (NumberField.TateGlobal.ideleNorm_pos _) (NumberField.TateGlobal.ideleNorm_pos _)

theorem continuous_borelDiagFst : Continuous (borelDiagFst : ↥(adelicBorel (𝓞 F) F) → (AdeleRing (𝓞 F) F)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_entry F 0 0).comp continuous_subtype_val
  · have : (fun b : ↥(adelicBorel (𝓞 F) F) => ((borelDiagFst b)⁻¹ : (AdeleRing (𝓞 F) F)ˣ).val)
        = fun b => ((b⁻¹ : ↥(adelicBorel (𝓞 F) F)) : (AdelicGL2 (𝓞 F) F)).val 0 0 := by
      funext b; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_entry F 0 0).comp (continuous_subtype_val.comp continuous_inv)

theorem continuous_borelDiagSnd : Continuous (borelDiagSnd : ↥(adelicBorel (𝓞 F) F) → (AdeleRing (𝓞 F) F)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_entry F 1 1).comp continuous_subtype_val
  · have : (fun b : ↥(adelicBorel (𝓞 F) F) => ((borelDiagSnd b)⁻¹ : (AdeleRing (𝓞 F) F)ˣ).val)
        = fun b => ((b⁻¹ : ↥(adelicBorel (𝓞 F) F)) : (AdelicGL2 (𝓞 F) F)).val 1 1 := by
      funext b; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_entry F 1 1).comp (continuous_subtype_val.comp continuous_inv)

theorem continuous_hgt : Continuous (hgt F) :=
  ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_borelDiagFst F)).div
    ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_borelDiagSnd F))
    fun b => (NumberField.TateGlobal.ideleNorm_pos _).ne'

end B3Translate

namespace B3Translate

variable (F : Type) [Field F] [NumberField F]




theorem norm_snd_eq_one_of_integral (x : (AdeleRing (𝓞 F) F)ˣ)
    (h1 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (x : (AdeleRing (𝓞 F) F)).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2 v ∈ v.adicCompletionIntegers F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ‖(x : (AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
  have ha : ‖(x : (AdeleRing (𝓞 F) F)).2 v‖ ≤ 1 := NumberField.AdelicHeight.norm_le_one_of_mem_adicCompletionIntegers (h1 v)
  have hb : ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2 v‖ ≤ 1 := NumberField.AdelicHeight.norm_le_one_of_mem_adicCompletionIntegers (h2 v)
  have hprod : ‖(x : (AdeleRing (𝓞 F) F)).2 v‖ * ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    rw [← norm_mul]
    have := congrArg (fun y : (AdeleRing (𝓞 F) F) => y.2 v) x.mul_inv
    change ((x : (AdeleRing (𝓞 F) F)).2 * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2) v = (1 : (AdeleRing (𝓞 F) F)).2 v at this
    rw [show ((x : (AdeleRing (𝓞 F) F)).2 * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2) v = (x : (AdeleRing (𝓞 F) F)).2 v * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2 v from rfl] at this
    rw [this]
    exact norm_one
  refine le_antisymm ha ?_
  calc (1 : ℝ) = ‖(x : (AdeleRing (𝓞 F) F)).2 v‖ * ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2 v‖ := hprod.symm
    _ ≤ ‖(x : (AdeleRing (𝓞 F) F)).2 v‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_one _

theorem ideleNorm_eq_prod_of_integral (x : (AdeleRing (𝓞 F) F)ˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(x : (AdeleRing (𝓞 F) F)).2 v‖ = 1) :
    NumberField.TateGlobal.ideleNorm F x = ∏ w : InfinitePlace F, ‖(x : (AdeleRing (𝓞 F) F)).1 w‖ ^ w.mult := by
  show ((distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ≥0) : ℝ) = _
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm,
    finprod_eq_one_of_forall_eq_one h, mul_one]

theorem archComponent_glArch_apply (w : InfinitePlace F) (g : (AdelicGL2 (𝓞 F) F)) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (((g : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w := by
  rw [archComponent_apply, glArch_apply]

theorem localHeight_archComponent_borel (w : InfinitePlace F) (b : ↥(adelicBorel (𝓞 F) F)) :
    localHeight (archComponent F w (glArch (𝓞 F) F (b : (AdelicGL2 (𝓞 F) F))))
      = ‖(((b : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).1 w‖ / ‖(((b : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖ := by
  set M := ((archComponent F w (glArch (𝓞 F) F (b : (AdelicGL2 (𝓞 F) F))) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
    with hM
  have h10 : M 1 0 = 0 := by
    rw [hM, archComponent_glArch_apply, borel_entry_one_zero]; rfl
  have h00 : M 0 0 = (((b : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).1 w := by rw [hM, archComponent_glArch_apply]
  have h11 : M 1 1 = (((b : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w := by rw [hM, archComponent_glArch_apply]

  have hne : M 1 1 ≠ 0 := by
    rw [h11]
    have hu : IsUnit ((((b : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w) := by
      have := (borelDiagSnd b).isUnit
      have hmap := this.map ((Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w).comp
        (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
      exact hmap
    exact hu.ne_zero
  unfold localHeight rowNormSq
  rw [← hM, Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, norm_zero, h00, h11]
  have hpos : 0 < ‖(((b : (AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖ := norm_pos_iff.mpr (by rwa [h11] at hne)
  field_simp
  ring

theorem hgt_eq_archHeight {g b k : (AdelicGL2 (𝓞 F) F)} (hb : b ∈ adelicBorel (𝓞 F) F) (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F)
    (hkf : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hka : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) (hgeq : g = b * k) :
    hgt F ⟨b, hb⟩ = archHeight F (glArch (𝓞 F) F g) := by

  have hbf : glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F := by
    have : b = g * k⁻¹ := by rw [hgeq, mul_inv_cancel_right]
    rw [this, map_mul, map_inv]
    exact (finiteIntegralGL2 (𝓞 F) F).mul_mem hg ((finiteIntegralGL2 (𝓞 F) F).inv_mem hkf)
  obtain ⟨hint, hint'⟩ := mem_finiteIntegralGL2_iff.mp hbf
  set bb : ↥(adelicBorel (𝓞 F) F) := ⟨b, hb⟩ with hbb

  have hfst : ∀ v, ‖((borelDiagFst bb : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    refine norm_snd_eq_one_of_integral F _ (fun v => hint 0 0 v) (fun v => ?_)
    rw [← map_inv]
    have := (mem_finiteIntegralGL2_iff.mp ((finiteIntegralGL2 (𝓞 F) F).inv_mem hbf)).1 0 0 v
    rw [← map_inv] at this
    exact this
  have hsnd : ∀ v, ‖((borelDiagSnd bb : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    refine norm_snd_eq_one_of_integral F _ (fun v => hint 1 1 v) (fun v => ?_)
    rw [← map_inv]
    have := (mem_finiteIntegralGL2_iff.mp ((finiteIntegralGL2 (𝓞 F) F).inv_mem hbf)).1 1 1 v
    rw [← map_inv] at this
    exact this

  have hH : archHeight F (glArch (𝓞 F) F g) = archHeight F (glArch (𝓞 F) F b) := by
    rw [hgeq, map_mul]
    unfold archHeight
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_mul, localHeight_mul_rowIsometry _ (hka w)]
  rw [hH, hgt, ideleNorm_eq_prod_of_integral F _ hfst, ideleNorm_eq_prod_of_integral F _ hsnd, ← Finset.prod_div_distrib]
  unfold archHeight
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← div_pow]
  congr 1
  exact (localHeight_archComponent_borel F w bb).symm

end B3Translate

open B3Translate in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∀ t : AdelicGL2 (𝓞 F) F,
      ∃ (k₁ k₂ : ℝ) (Ω : Set (AdelicGL2 (𝓞 F) F)), 0 < k₁ ∧ k₁ ≤ k₂ ∧ IsCompact Ω ∧
        ∀ g : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F →
          ∃ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F), ω ∈ Ω ∧
            g * t = (b : AdelicGL2 (𝓞 F) F) * ω ∧
            k₁ * archHeight F (glArch (𝓞 F) F g) ≤ hgt b ∧
            hgt b ≤ k₂ * archHeight F (glArch (𝓞 F) F g) := by
  intro α hgt t
  have hhgt : ∀ b, hgt b = B3Translate.hgt F b := fun b => rfl
  set K : Subgroup (AdelicGL2 (𝓞 F) F) := adelicMaximalCompact F with hK
  have hKc : IsCompact (K : Set (AdelicGL2 (𝓞 F) F)) := isCompact_adelicMaximalCompact F
  have hmemK : ∀ {k : AdelicGL2 (𝓞 F) F}, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) → k ∈ K :=
    fun h1 h2 => ⟨h1, h2⟩

  set KtK : Set (AdelicGL2 (𝓞 F) F) :=
    (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * t * p.2) '' ((K : Set (AdelicGL2 (𝓞 F) F)) ×ˢ (K : Set (AdelicGL2 (𝓞 F) F)))
    with hKtK
  have hKtKc : IsCompact KtK :=
    (hKc.prod hKc).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  set S : Set ↥(adelicBorel (𝓞 F) F) := Subtype.val ⁻¹' KtK with hS
  have hSc : IsCompact S := (isClosed_adelicBorel F).isClosedEmbedding_subtypeVal.isCompact_preimage hKtKc

  obtain ⟨b₀, k₀, hb₀, hk₀f, hk₀a, ht⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F t
  have hb₀S : (⟨b₀, hb₀⟩ : ↥(adelicBorel (𝓞 F) F)) ∈ S := by
    refine ⟨(1, k₀⁻¹), ⟨K.one_mem, K.inv_mem (hmemK hk₀f hk₀a)⟩, ?_⟩
    show 1 * t * k₀⁻¹ = b₀
    rw [one_mul, ht, mul_inv_cancel_right]

  obtain ⟨bmin, hbminS, hmin⟩ := hSc.exists_isMinOn ⟨_, hb₀S⟩ (continuous_hgt F).continuousOn
  obtain ⟨bmax, hbmaxS, hmax⟩ := hSc.exists_isMaxOn ⟨_, hb₀S⟩ (continuous_hgt F).continuousOn
  refine ⟨B3Translate.hgt F bmin, B3Translate.hgt F bmax, K, hgt_pos F bmin, hmin hbmaxS, hKc, fun g hg => ?_⟩

  obtain ⟨bg, kg, hbg, hkgf, hkga, hgeq⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  obtain ⟨b', k', hb', hk'f, hk'a, heq'⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F (kg * t)
  have hb'S : (⟨b', hb'⟩ : ↥(adelicBorel (𝓞 F) F)) ∈ S := by
    refine ⟨(kg, k'⁻¹), ⟨hmemK hkgf hkga, K.inv_mem (hmemK hk'f hk'a)⟩, ?_⟩
    show kg * t * k'⁻¹ = b'
    rw [heq', mul_inv_cancel_right]
  have hH : B3Translate.hgt F ⟨bg, hbg⟩ = archHeight F (glArch (𝓞 F) F g) := hgt_eq_archHeight F hbg hg hkgf hkga hgeq
  have hHnn : 0 ≤ archHeight F (glArch (𝓞 F) F g) := by rw [← hH]; exact (hgt_pos F _).le
  refine ⟨⟨bg, hbg⟩ * ⟨b', hb'⟩, k', hmemK hk'f hk'a, ?_, ?_, ?_⟩
  · show g * t = bg * b' * k'
    rw [hgeq, mul_assoc, heq', mul_assoc]
  · rw [hhgt, hgt_mul, hH, mul_comm]
    exact mul_le_mul_of_nonneg_left (hmin hb'S) hHnn
  · rw [hhgt, hgt_mul, hH, mul_comm (B3Translate.hgt F bmax)]
    exact mul_le_mul_of_nonneg_left (hmax hb'S) hHnn
