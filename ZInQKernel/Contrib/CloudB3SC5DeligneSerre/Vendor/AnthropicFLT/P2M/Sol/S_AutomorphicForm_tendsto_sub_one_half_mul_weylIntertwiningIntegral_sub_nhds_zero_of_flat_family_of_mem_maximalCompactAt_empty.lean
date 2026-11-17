/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty (git blob 49e8af5279c9b236a28fee02c9843fd1fd88fb7a, sha256 16d35fcc25335a12a1aadc612b15e26a081f4c0e2f3b0054ab849a8924b8efe7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

namespace A6Kit

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

private theorem glInfinite_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (H : ∀ w : InfinitePlace F, archComponent F w g = archComponent F w h) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  funext w
  have := congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (H w)
  simpa [archComponent_apply] using this

private theorem adelicGL2_ext {g h : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = finComponent (𝓞 F) F v (glFin (𝓞 F) F h)) :
    g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simpa [glArch_apply] using this
  · apply Subtype.ext
    funext v
    have := congrArg (fun m : GL (Fin 2) (v.adicCompletion F) =>
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) (h₂ v)
    simp [finComponent_apply, glFin_apply] at this
    exact this

private theorem eq_one_of_forall_archComponent_eq_one {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ maximalCompactAt F ∅)
    (h : ∀ w : InfinitePlace F, archComponent F w (glArch (𝓞 F) F k) = 1) : k = 1 := by
  rw [mem_maximalCompactAt_iff] at hk
  refine adelicGL2_ext ?_ (fun v => ?_)
  · rw [map_one]
    exact glInfinite_ext fun w => by rw [h w, map_one]
  · rw [map_one, map_one]
    exact hk.2 v (Finset.notMem_empty v)

end A6Kit

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (kinf : AdelicGL2 (𝓞 F) F) (_hkinf : kinf ∈ maximalCompactAt F ∅),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) kinf
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat kinf hkinf
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  classical

  let supp : AdelicGL2 (𝓞 F) F → Finset (InfinitePlace F) :=
    fun k => Finset.univ.filter (fun w => archComponent F w (glArch (𝓞 F) F k) ≠ 1)

  suffices hmain : ∀ (N : ℕ) (k : AdelicGL2 (𝓞 F) F), k ∈ maximalCompactAt F ∅ → (supp k).card ≤ N →
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) from
    hmain _ kinf hkinf le_rfl
  intro N
  induction N with
  | zero =>
    intro k hk hcard
    have hsupp : supp k = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    have hall : ∀ w : InfinitePlace F, archComponent F w (glArch (𝓞 F) F k) = 1 := by
      intro w
      by_contra hw
      have : w ∈ supp k := Finset.mem_filter.2 ⟨Finset.mem_univ w, hw⟩
      rw [hsupp] at this
      exact Finset.notMem_empty w this
    have hk1 : k = 1 := A6Kit.eq_one_of_forall_archComponent_eq_one hk hall
    subst hk1
    refine (tendsto_const_nhds (x := (0 : ℂ))).congr' (Eventually.of_forall fun s => ?_)
    simp only [sub_self, mul_zero]
  | succ N ih =>
    intro k hk hcard

    by_cases hsmall : (supp k).card ≤ N
    · exact ih k hk hsmall
    have hne : (supp k).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.card_empty] at hsmall
      exact hsmall (Nat.zero_le N)
    obtain ⟨w, hw⟩ := hne
    obtain ⟨k₁, k₂, hk12, -, hk1f, hk1a, -, hk1iso, hk2, hk2w⟩ :=
      AutomorphicForm.exists_eq_mul_archSupportedAt_of_mem_maximalCompactAt_empty F k hk w

    have hsupp2 : supp k₂ ⊆ (supp k).erase w := by
      intro w' hw'
      have hw'2 : archComponent F w' (glArch (𝓞 F) F k₂) ≠ 1 := (Finset.mem_filter.1 hw').2
      have hne' : w' ≠ w := fun h => hw'2 (h ▸ hk2w)
      refine Finset.mem_erase.2 ⟨hne', Finset.mem_filter.2 ⟨Finset.mem_univ w', ?_⟩⟩
      rw [hk12, map_mul, map_mul, hk1a w' hne', one_mul]
      exact hw'2
    have hcard2 : (supp k₂).card ≤ N := by
      have h1 := Finset.card_le_card hsupp2
      rw [Finset.card_erase_of_mem hw] at h1
      omega
    have ih2 := ih k₂ hk2 hcard2

    have hk2K : k₂ ∈ adelicMaximalCompact F := maximalCompactAt_le F ∅ hk2
    obtain ⟨hψ, hψK, hψf, hψjc, hψhol, hψflat⟩ :=
      AutomorphicForm.flat_family_comp_mul_of_mem_adelicMaximalCompact F hα φ hφ hφK hφf hφjc hφhol hφflat k₂ hk2K

    have hA5 := AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
      F hα (fun s h => φ s (h * k₂)) hψ hψK hψf hψjc hψhol hψflat w k₁ hk1f hk1a (hk1iso w)

    have hMk : ∀ s, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (fun h => φ s (h * k₂)) k₁
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k := by
      intro s
      simp only [weylIntertwiningIntegral, hk12, mul_assoc]
    have hM1 : ∀ s, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (fun h => φ s (h * k₂)) 1
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k₂ := by
      intro s
      simp only [weylIntertwiningIntegral, mul_one]
    have hsum := hA5.add ih2
    rw [add_zero] at hsum
    refine hsum.congr fun s => ?_
    rw [hMk, hM1]
    ring
