/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice (git blob ac305b2bac94d94ca23b385c4016c4acad52fa1c, sha256 cb06efdd43d5eade37a603aa03f08c643178bfe336b7cb593ff1ab446701163c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice.AlgebraicCurve
end P2MW.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice.AlgebraicCurve
namespace Filter
end Filter
namespace Topology
end Topology
namespace Set
end Set

namespace P2MW.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice

set_option autoImplicit false

noncomputable section

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_exists_finset_card_le_span_eq_pathPeriodLattice.AlgebraicCurve
open _root_.Filter
open _root_.Topology
open _root_.Set
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor Divisor.degree Divisor.degree_single IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed HasCanonicalDivisor Place.evalAt regularDifferentials abelJacobiDiv pathPeriodLattice exists_isUnit_det_evalAt_differentialCoeff exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice)
namespace PeriodLatticeGeneratorsProof
open _root_.AlgebraicCurve

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_finset_card_le_span_eq_of_discrete (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ s : Finset E, s.card ≤ Module.finrank ℝ E ∧ Submodule.span ℤ (s : Set E) = L := by
  classical

  set W : Submodule ℝ E := Submodule.span ℝ (L : Set E) with hW
  set L' : Submodule ℤ W := L.comap (W.subtype.restrictScalars ℤ) with hL'
  have hmemL' : ∀ x : W, x ∈ L' ↔ (x : E) ∈ L := fun x => Iff.rfl

  haveI : DiscreteTopology L' := by
    have h0 : IsOpen ({0} : Set L) := isOpen_discrete _
    obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.1 h0
    refine discreteTopology_of_isOpen_singleton_zero ?_
    refine isOpen_induced_iff.2 ⟨((↑) : W → E) ⁻¹' t, ht.preimage continuous_subtype_val, ?_⟩
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    have hx : ((x : W) : E) ∈ L := (hmemL' x).1 x.2
    have key : (⟨((x : W) : E), hx⟩ : L) ∈ ((↑) : L → E) ⁻¹' t ↔ (⟨((x : W) : E), hx⟩ : L) = 0 := by
      rw [hpre]; exact Iff.rfl
    simp only [mem_preimage] at key
    rw [key]
    constructor
    · intro h
      have h' : ((x : W) : E) = 0 := by simpa using congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (by simpa using h'))
    · intro h
      subst h
      exact Subtype.ext rfl

  haveI : IsZLattice ℝ L' := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (f := W.subtype) W.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    apply le_antisymm
    · exact Submodule.span_le.2 (by
        rintro _ ⟨x, hx, rfl⟩
        exact Submodule.subset_span ((hmemL' x).1 hx))
    · refine Submodule.span_le.2 fun y hy => Submodule.subset_span ?_
      exact ⟨⟨y, Submodule.subset_span hy⟩, (hmemL' _).2 hy, rfl⟩
  haveI : Module.Free ℤ L' := ZLattice.module_free ℝ L'
  haveI : Module.Finite ℤ L' := ZLattice.module_finite ℝ L'
  have hrank : Module.finrank ℤ L' = Module.finrank ℝ W := ZLattice.rank ℝ L'

  set B := Module.finBasis ℤ L' with hB
  set ψ : L' →ₗ[ℤ] E := (W.subtype.restrictScalars ℤ).comp L'.subtype with hψ
  have hψ_apply : ∀ x : L', ψ x = ((x : W) : E) := fun x => rfl
  refine ⟨Finset.univ.image fun k => ψ (B k), ?_, ?_⟩
  · calc (Finset.univ.image fun k => ψ (B k)).card ≤ Finset.univ.card := Finset.card_image_le
      _ = Module.finrank ℤ L' := by simp
      _ = Module.finrank ℝ W := hrank
      _ ≤ Module.finrank ℝ E := Submodule.finrank_le W
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      rw [hψ_apply]
      exact (hmemL' _).1 (B k).2
    · intro y hy
      have hy' : (⟨⟨y, Submodule.subset_span hy⟩, (hmemL' _).2 hy⟩ : L') ∈
          Submodule.span ℤ (Set.range B) := by
        rw [B.span_eq]; exact Submodule.mem_top
      have himg := Submodule.mem_map_of_mem (f := ψ) hy'
      rw [Submodule.map_span] at himg
      have hyψ : ψ ⟨⟨y, Submodule.subset_span hy⟩, (hmemL' _).2 hy⟩ = y := rfl
      rw [hyψ] at himg
      refine Submodule.span_mono ?_ himg
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)

end Lattice

section Discrete

variable {E : Type*} [NormedAddCommGroup E]

theorem discreteTopology_of_nhds_inter (L : Submodule ℤ E) {V : Set E} (hV : V ∈ 𝓝 (0 : E))
    (h : ∀ x ∈ L, x ∈ V → x = 0) : DiscreteTopology L := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_induced_iff.2 ⟨interior V, isOpen_interior, ?_⟩
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hx
    exact Subtype.ext (h x x.2 (interior_subset hx))
  · rintro rfl
    exact mem_interior_iff_mem_nhds.2 hV

end Discrete

section Divisors

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem sum_single_apply_nonneg {n : ℕ} (P : Fin n → Place K F) (w : Place K F) :
    0 ≤ (∑ k, Finsupp.single (P k) (1 : ℤ) : Divisor K F) w := by
  classical
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun k _ => by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num

theorem ord_algebraMap (w : Place K F) (c : K) : w.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hu : IsUnit (⟨algebraMap K F c, w.algebraMap_mem' c⟩ : w.toValuationSubring) := by
    refine ⟨⟨⟨algebraMap K F c, w.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, w.algebraMap_mem' c⁻¹⟩,
      ?_, ?_⟩, rfl⟩
    · ext; simp [hc]
    · ext; simp [hc]
  exact w.ord_coe_unit hu.unit

end Divisors

section Separation

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem exists_nhds_eq_of_sum_single_eq {n : ℕ} {v : Fin n → X} (hv : Function.Injective v) :
    ∃ W : Fin n → Set X, (∀ j, W j ∈ 𝓝 (v j)) ∧
      ∀ P : Fin n → X, (∀ j, P j ∈ W j) →
        (∑ k, Finsupp.single (P k) (1 : ℤ) : X →₀ ℤ) = ∑ k, Finsupp.single (v k) (1 : ℤ) →
          P = v := by
  classical
  obtain ⟨U, hU, hdisj⟩ := (Set.finite_range v).t2_separation
  refine ⟨fun j => U (v j), fun j => (hU (v j)).2.mem_nhds (hU (v j)).1, ?_⟩
  intro P hP hsum
  funext j
  have hj := congrArg (fun D : X →₀ ℤ => D (v j)) hsum
  simp only [Finsupp.finsetSum_apply] at hj

  have hR : (∑ k, (Finsupp.single (v k) (1 : ℤ)) (v j)) = 1 := by
    rw [Finset.sum_eq_single j (fun k _ hkj => by
        rw [Finsupp.single_apply, if_neg (fun h => hkj (hv h))])
      (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same]

  have hL : (∑ k, (Finsupp.single (P k) (1 : ℤ)) (v j)) = (Finsupp.single (P j) (1 : ℤ)) (v j) := by
    refine Finset.sum_eq_single j ?_ (fun h => absurd (Finset.mem_univ j) h)
    intro k _ hkj
    rw [Finsupp.single_apply, if_neg]
    intro hk
    have hne : v k ≠ v j := fun h => hkj (hv h)
    have hd : Disjoint (U (v k)) (U (v j)) :=
      hdisj (Set.mem_range_self k) (Set.mem_range_self j) hne
    exact Set.disjoint_left.1 hd (hP k) (hk ▸ (hU (v j)).1)
  rw [hR, hL] at hj
  by_contra hne
  rw [Finsupp.single_apply, if_neg hne] at hj
  exact zero_ne_one hj

end Separation

end AlgebraicCurve.PeriodLatticeGeneratorsProof

open AlgebraicCurve.PeriodLatticeGeneratorsProof in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) :
    ∃ s : Finset (Fin n → ℂ), s.card ≤ 2 * n ∧
      Submodule.span ℤ (s : Set (Fin n → ℂ)) = pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) := by
  classical
  set bΩ : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hbΩ
  set Λ : Submodule ℤ (Fin n → ℂ) := pathPeriodLattice bΩ with hΛ

  haveI : DiscreteTopology Λ := by

    obtain ⟨v, hvinj, hdet, hnonspecial⟩ :=
      AlgebraicCurve.exists_isUnit_det_evalAt_differentialCoeff (K := ℂ) (F := F) hfg b

    haveI : Nonempty (Place ℂ F) := ConnectedSpace.toNonempty
    obtain ⟨P₀⟩ : Nonempty (Place ℂ F) := inferInstance

    obtain ⟨Φ, hΦv, hopen, hcong⟩ :=
      AlgebraicCurve.exists_abelJacobiDiv_sub_mem_pathPeriodLattice_and_image_mem_nhds F hfg hF
        bΩ (fun i => (b i).2) v hdet P₀

    obtain ⟨W, hW, hWeq⟩ := exists_nhds_eq_of_sum_single_eq (X := Place ℂ F) hvinj

    set U : Set (Fin n → Place ℂ F) := Set.pi Set.univ W ∩
      {P | abelJacobiDiv bΩ P₀ ((∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1) - Φ P
        ∈ pathPeriodLattice bΩ} with hU
    have hUmem : U ∈ 𝓝 v :=
      Filter.inter_mem (set_pi_mem_nhds Set.finite_univ fun j _ => hW j) hcong
    refine discreteTopology_of_nhds_inter Λ (hopen U hUmem) ?_
    rintro x hx ⟨P, ⟨hPW, hPcong⟩, rfl⟩

    set D : Divisor ℂ F := (∑ j, Finsupp.single (P j) 1) - ∑ j, Finsupp.single (v j) 1 with hD
    have hAJ : abelJacobiDiv bΩ P₀ D ∈ pathPeriodLattice bΩ := by
      have := (pathPeriodLattice bΩ).add_mem hPcong hx
      rwa [sub_add_cancel] at this

    have hdeg : Divisor.degree D = 0 := by
      simp only [hD, map_sub, map_sum, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one, sub_self]

    obtain ⟨f, hf0, hf⟩ :=
      AlgebraicCurve.Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice F hfg hF b P₀ D
        hdeg hAJ

    have hfL : ∀ w : Place ℂ F,
        -((∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor ℂ F) w) ≤ w.ord f := by
      intro w
      rw [← hf w, hD, Finsupp.sub_apply]
      linarith [sum_single_apply_nonneg P w]
    obtain ⟨c, rfl⟩ := hnonspecial f hfL

    have hDzero : (∑ j, Finsupp.single (P j) (1 : ℤ) : Divisor ℂ F) =
        ∑ j, Finsupp.single (v j) (1 : ℤ) := by
      rw [← sub_eq_zero]
      ext w
      have := hf w
      rw [ord_algebraMap] at this
      simpa [hD] using this
    have hPv : P = v := hWeq P (fun j => hPW j (Set.mem_univ j)) hDzero
    rw [hPv, hΦv]

  obtain ⟨s, hs, hspan⟩ := exists_finset_card_le_span_eq_of_discrete (E := Fin n → ℂ) Λ
  refine ⟨s, ?_, hspan⟩
  have hfin : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [finrank_real_of_complex, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

end
