/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat (git blob 95b3e483a7051793efaec71aba9ebcd88b6a9f48, sha256 b2872ea768ffb1acfe68b54bb79e26a60b30423dce84fbbef10071fb8f951cb0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat

set_option autoImplicit false

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat.NumberField
open _root_.IsDedekindDomain
open _root_.MeasureTheory
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat.NumberField.AdelicFourier
open _root_.NumberField.InfiniteAdeleRing
open _root_.Filter
open TopologicalSpace
open scoped SchwartzMap

noncomputable section

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing InfinitePlace.not_isReal_iff_isComplex mixedEmbedding mixedEmbedding.mixedSpace mixedEmbedding.latticeBasis InfinitePlace AdeleRing AdelicBox.continuous_ringEquiv_mixedSpace AdelicBox.properSpace_completion AdelicBox.norm_apply_le_of_isReal AdelicBox.norm_apply_le_of_isComplex)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (schwartzBruhat schwartzBruhat_induction)
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]





open scoped Classical in

private theorem exists_one_add_norm_pow_mul_norm_le (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ℕ) :
    ∃ C : ℝ, ∀ y : mixedEmbedding.mixedSpace F, (1 + ‖y‖) ^ k * ‖g y‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl g y
  rwa [norm_iteratedFDeriv_zero] at h

section Cells

open scoped Classical

def mixedCell : Set (mixedEmbedding.mixedSpace F) := closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))

theorem isCompact_mixedCell : IsCompact (mixedCell F) :=
  (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).isCompact_closure

theorem isClosed_mixedCell : IsClosed (mixedCell F) := isClosed_closure

theorem exists_norm_le_of_mem_mixedCell : ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ mixedCell F, ‖q‖ ≤ R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (isCompact_mixedCell F).isBounded
  exact ⟨max R 0, le_max_right _ _, fun q hq => (hR q hq).trans (le_max_left _ _)⟩

def archCell : Set (InfiniteAdeleRing F) := ringEquiv_mixedSpace F ⁻¹' mixedCell F

theorem isCompact_archCell : IsCompact (archCell F) := by
  obtain ⟨R, -, hR⟩ := exists_norm_le_of_mem_mixedCell F
  haveI : ∀ v : InfinitePlace F, ProperSpace v.Completion := fun v => AdelicBox.properSpace_completion F v
  have hbig : IsCompact {x : InfiniteAdeleRing F | ∀ v, ‖x v‖ ≤ R} := by
    have : {x : InfiniteAdeleRing F | ∀ v, ‖x v‖ ≤ R} =
        Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) R := by
      ext x
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_closedBall _ _
  refine hbig.of_isClosed_subset ((isClosed_mixedCell F).preimage (AdelicBox.continuous_ringEquiv_mixedSpace F)) ?_
  intro x hx v
  have hx' : ‖ringEquiv_mixedSpace F x‖ ≤ R := hR _ hx
  by_cases hv : v.IsReal
  · exact (AdelicBox.norm_apply_le_of_isReal F x hv).trans hx'
  · exact (AdelicBox.norm_apply_le_of_isComplex F x (InfinitePlace.not_isReal_iff_isComplex.mp hv)).trans hx'

variable {F}

def cell0 (K : Set (FiniteAdeleRing (𝓞 F) F)) : Set (AdeleRing (𝓞 F) F) := {x | x.1 ∈ archCell F ∧ x.2 ∈ K}

theorem isCompact_cell0 {K : Set (FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K) : IsCompact (cell0 K) := by
  have : IsCompact (archCell F ×ˢ K) := (isCompact_archCell F).prod hK
  exact this

def cellShift (l : (mixedEmbedding.mixedSpace F)) : (AdeleRing (𝓞 F) F) := ((ringEquiv_mixedSpace F).symm l, (0 : FiniteAdeleRing (𝓞 F) F))

def cell (K : Set (FiniteAdeleRing (𝓞 F) F)) (l : (mixedEmbedding.mixedSpace F)) : Set (AdeleRing (𝓞 F) F) := (fun z : (AdeleRing (𝓞 F) F) => -cellShift l + z) ⁻¹' cell0 K

theorem isCompact_cell {K : Set (FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K) (l : (mixedEmbedding.mixedSpace F)) : IsCompact (cell K l) :=
  (Homeomorph.addLeft (-cellShift l)).isCompact_preimage.mpr (isCompact_cell0 hK)

theorem mem_cell_iff {K : Set (FiniteAdeleRing (𝓞 F) F)} {l : (mixedEmbedding.mixedSpace F)} {x : (AdeleRing (𝓞 F) F)} :
    x ∈ cell K l ↔ ringEquiv_mixedSpace F x.1 - l ∈ mixedCell F ∧ x.2 ∈ K := by
  show (-cellShift l + x).1 ∈ archCell F ∧ (-cellShift l + x).2 ∈ K ↔ _
  have h1 : (-cellShift l + x).1 = -(ringEquiv_mixedSpace F).symm l + x.1 := rfl
  have h2 : (-cellShift l + x).2 = -0 + x.2 := rfl
  rw [h2, neg_zero, zero_add, h1]
  simp only [archCell, Set.mem_preimage, map_add, map_neg, RingEquiv.apply_symm_apply]
  rw [neg_add_eq_sub]

theorem mem_cell_floor {K : Set (FiniteAdeleRing (𝓞 F) F)} {x : (AdeleRing (𝓞 F) F)} (hx : x.2 ∈ K) :
    x ∈ cell K (ZSpan.floor (mixedEmbedding.latticeBasis F) (ringEquiv_mixedSpace F x.1) : (mixedEmbedding.mixedSpace F)) := by
  rw [mem_cell_iff]
  refine ⟨subset_closure ?_, hx⟩
  rw [← ZSpan.fract_apply]
  exact ZSpan.fract_mem_fundamentalDomain _ _

theorem measure_cell [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (K : Set (FiniteAdeleRing (𝓞 F) F)) (l : (mixedEmbedding.mixedSpace F)) : μ (cell K l) = μ (cell0 K) :=
  measure_preimage_add μ _ _

end Cells

section PureTensor

variable {F}

open scoped Classical in

theorem integrable_pureTensor [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (g : 𝓢((mixedEmbedding.mixedSpace F), ℂ)) (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    Integrable (fun x : (AdeleRing (𝓞 F) F) => g (ringEquiv_mixedSpace F x.1) * h x.2) μ := by

  set e := ringEquiv_mixedSpace F with he
  have hcont : Continuous fun x : (AdeleRing (𝓞 F) F) => g (e x.1) * h x.2 :=
    (g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace F).comp continuous_fst)).mul
      (hlc.continuous.comp continuous_snd)
  set f : C((AdeleRing (𝓞 F) F), ℂ) := ⟨fun x : (AdeleRing (𝓞 F) F) => g (e x.1) * h x.2, hcont⟩ with hf
  set K := tsupport h with hKdef
  have hK : IsCompact K := hcs

  set b := mixedEmbedding.latticeBasis F with hb
  let L : Submodule ℤ (mixedEmbedding.mixedSpace F) := Submodule.span ℤ (Set.range b)
  let s : L → Compacts (AdeleRing (𝓞 F) F) := fun l => ⟨cell K (l : (mixedEmbedding.mixedSpace F)), isCompact_cell hK _⟩

  obtain ⟨R, hR0, hR⟩ := exists_norm_le_of_mem_mixedCell F
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hlc.continuous
  set k : ℕ := Module.finrank ℤ L + 1 with hk
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_le F g k
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hB0 : 0 ≤ max B 0 := le_max_right _ _

  have hsup : ∀ l : L, ‖f.restrict (s l)‖ ≤ max B 0 * (C * (1 + R) ^ k) / (1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k := by
    intro l
    have hden : 0 < (1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k := by positivity
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ cell K (l : (mixedEmbedding.mixedSpace F)) := hx
    rw [mem_cell_iff] at hx'
    obtain ⟨hq, -⟩ := hx'
    have hqR : ‖e x.1 - (l : (mixedEmbedding.mixedSpace F))‖ ≤ R := hR _ hq

    have hcmp : 1 + ‖(l : (mixedEmbedding.mixedSpace F))‖ ≤ (1 + R) * (1 + ‖e x.1‖) := by
      have : ‖(l : (mixedEmbedding.mixedSpace F))‖ ≤ ‖e x.1‖ + R := by
        calc ‖(l : (mixedEmbedding.mixedSpace F))‖ = ‖e x.1 - (e x.1 - (l : (mixedEmbedding.mixedSpace F)))‖ := by rw [sub_sub_cancel]
          _ ≤ ‖e x.1‖ + ‖e x.1 - (l : (mixedEmbedding.mixedSpace F))‖ := norm_sub_le _ _
          _ ≤ ‖e x.1‖ + R := by gcongr
      nlinarith [norm_nonneg (e x.1), norm_nonneg (l : (mixedEmbedding.mixedSpace F))]
    have hpow : (1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k ≤ (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcmp k

    have hg : ‖g (e x.1)‖ ≤ C / (1 + ‖e x.1‖) ^ k := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact hC _
    have hgx : ‖g (e x.1)‖ ≤ C * (1 + R) ^ k / (1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k := by
      refine hg.trans ?_
      rw [div_le_div_iff₀ (by positivity) hden]
      calc C * (1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k ≤ C * ((1 + R) ^ k * (1 + ‖e x.1‖) ^ k) :=
            mul_le_mul_of_nonneg_left hpow hC0
        _ = C * (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by ring
    show ‖g (e x.1) * h x.2‖ ≤ _
    rw [norm_mul]
    calc ‖g (e x.1)‖ * ‖h x.2‖ ≤ (C * (1 + R) ^ k / (1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k) * max B 0 :=
          mul_le_mul hgx ((hB _).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ = max B 0 * (C * (1 + R) ^ k) / (1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k := by ring

  have hμ : ∀ l : L, μ.real (s l) = μ.real (cell0 K) := fun l => by
    show μ.real (cell K (l : (mixedEmbedding.mixedSpace F))) = μ.real (cell0 K)
    rw [measureReal_def, measureReal_def, measure_cell]
  have hsum : Summable fun l : L => ‖f.restrict (s l)‖ * μ.real (s l) := by
    simp_rw [hμ]
    refine Summable.mul_right _ ?_
    have hcomp : Summable fun l : L =>
        max B 0 * (C * (1 + R) ^ k) * ‖(l : (mixedEmbedding.mixedSpace F)) - 0‖⁻¹ ^ k :=
      (ZLattice.summable_norm_sub_inv_pow L k (Nat.lt_succ_self _) 0).mul_left _
    refine Summable.of_norm_bounded_eventually hcomp ?_
    have hfin : {l : L | (l : (mixedEmbedding.mixedSpace F)) = 0}.Finite :=
      Set.Subsingleton.finite fun a ha c hc => Subtype.val_injective (ha.trans hc.symm)
    filter_upwards [hfin.compl_mem_cofinite] with l hl
    have hl0 : (l : (mixedEmbedding.mixedSpace F)) ≠ 0 := hl
    have hpos : 0 < ‖(l : (mixedEmbedding.mixedSpace F))‖ := norm_pos_iff.mpr hl0
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (hsup l).trans ?_
    rw [sub_zero]
    have hkey : ((1 + ‖(l : (mixedEmbedding.mixedSpace F))‖) ^ k)⁻¹ ≤ ‖(l : (mixedEmbedding.mixedSpace F))‖⁻¹ ^ k := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hpos (le_add_of_nonneg_left zero_le_one)) k
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hB0 (by positivity))

  have hU : IntegrableOn f (⋃ l : L, (s l : Set (AdeleRing (𝓞 F) F))) μ := integrableOn_iUnion_of_summable_norm_restrict hsum
  have hsupp : Function.support (fun x : (AdeleRing (𝓞 F) F) => g (e x.1) * h x.2) ⊆ ⋃ l : L, (s l : Set (AdeleRing (𝓞 F) F)) := by
    intro x hx
    have hx2 : x.2 ∈ K := by
      refine subset_tsupport _ ?_
      intro h0
      exact hx (by simp only [h0, mul_zero])
    exact Set.mem_iUnion.mpr ⟨ZSpan.floor b (e x.1), mem_cell_floor hx2⟩
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hU

end PureTensor

theorem integrable_of_mem_schwartzBruhat_impl [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {f : (AdeleRing (𝓞 F) F) → ℂ} (hf : f ∈ schwartzBruhat F) :
    Integrable f μ := by
  refine schwartzBruhat_induction (p := fun f _ => Integrable f μ) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨g, h, hlc, hcs, rfl⟩
    exact integrable_pureTensor μ g h hlc hcs
  · exact integrable_zero _ _ _
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro c f _ hf
    exact hf.smul c

#print axioms integrable_of_mem_schwartzBruhat_impl

example : ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {f : (AdeleRing (𝓞 F) F) → ℂ}
    (_ : f ∈ schwartzBruhat F), Integrable f μ :=
  fun μ _ _ hf => integrable_of_mem_schwartzBruhat_impl F μ hf

end NumberField.AdelicFourier

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat.NumberField.AdelicFourier

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    MeasureTheory.Integrable f μ := by
  exact NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat_impl F μ hf
