/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed (git blob 977aabb8cf5a6f30b6ec94317b6dfd16fbf663f0, sha256 d3f686dc4dc89d3848f6e31165fa7283464f89cf01b83dc40481acbca56ba502).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

namespace W7XEllMapDomain

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
  [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']

theorem algebraMap_mem_of_new
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {v' : Place K' F'}
    (hv' : ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (f : F) : algebraMap F F' f ∈ v'.toValuationSubring := by
  by_contra hmem
  obtain ⟨x, hxt, hxfin⟩ := hfg
  obtain ⟨t, _ht_trans, ht_fin, ht_sep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hxt hxfin
  haveI := ht_fin; haveI := ht_sep
  obtain ⟨P, hP⟩ :=
    AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
      (K := K) t (algebraMap F F') v'.toValuationSubring
      (fun c => by
        rw [← IsScalarTower.algebraMap_apply K F F', IsScalarTower.algebraMap_apply K K' F']
        exact v'.algebraMap_mem' _)
      ⟨f, hmem⟩
  exact hv' P hP.symm

theorem algebraMap_mem_lSpace
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {lift : Place K F → Place K' F'}
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) :
    algebraMap F F' f ∈ LSpace (K := K') (Finsupp.mapDomain lift D) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  refine mem_lSpace_iff_ord.mpr (Or.inr fun v' => ?_)
  by_cases hold : ∃ v, lift v = v'
  · obtain ⟨v, rfl⟩ := hold
    rw [Finsupp.mapDomain_apply_of_injective hlift_inj, hlift_ord]
    exact (mem_lSpace_iff_ord.mp hf).resolve_left hf0 v
  · push_neg at hold
    rw [show (Finsupp.mapDomain lift D) v' = 0 from
      Finsupp.mapDomain_notin_range D v' (by simpa [Set.range] using hold), neg_zero]
    have hmem := algebraMap_mem_of_new (K' := K') (F' := F') hfg (hlift_new v' hold) f
    rcases (v'.adicValuation_le_one_iff).mp (v'.adicValuation_le_one_of_mem hmem) with h0 | h
    · exact absurd ((algebraMap F F').injective (h0.trans (map_zero _).symm)) hf0
    · exact h

end W7XEllMapDomain

open W7XEllMapDomain

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (D : Divisor K F) [FiniteDimensional K ↥(riemannRochSpace D)] :
    ell (K := K') (D.mapDomain lift) = ell (K := K) D := by
  classical
  set b := Module.finBasis K ↥(riemannRochSpace D) with hb
  set n := ell (K := K) D with hn
  set e : Fin n → ↥(LSpace (K := K') (Finsupp.mapDomain lift D)) :=
    fun i => ⟨algebraMap F F' (b i).1,
      algebraMap_mem_lSpace hfg hlift_ord hlift_inj hlift_new (b i).2⟩ with he

  have hLI : LinearIndependent K' e := by
    have hLI0 : LinearIndependent K' (fun i => algebraMap F F' (b i : F)) :=
      linearIndependent_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen
        (b.linearIndependent.map' (riemannRochSpace D).subtype
          (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
    exact hLI0.of_comp (LSpace (K := K') (Finsupp.mapDomain lift D)).subtype

  have hSpan : Submodule.span K' (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨f', hf'⟩ -

    have hmem_img : f' ∈ Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) :=
      AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
        K F K' F' hfg hfg' hgen lift hlift_ord hlift_inj hlift_new D hf'

    have heq : Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) =
        Submodule.span K' (Set.range fun i => algebraMap F F' (b i : F)) := by
      refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨g, hg, rfl⟩

        have : algebraMap F F' g = ∑ i, (algebraMap K K' (b.repr ⟨g, hg⟩ i)) •
            algebraMap F F' (b i : F) := by
          conv_lhs => rw [show g = ((⟨g, hg⟩ : riemannRochSpace D) : F) from rfl,
            ← b.sum_repr ⟨g, hg⟩]
          simp only [Submodule.coe_sum, SetLike.val_smul, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K F F',
            Algebra.smul_def, IsScalarTower.algebraMap_apply K K' F']
        rw [this]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rintro _ ⟨i, rfl⟩; exact ⟨_, (b i).2, rfl⟩
    rw [heq] at hmem_img

    have hmap : Submodule.span K' (Set.range fun i => algebraMap F F' (b i : F)) =
        (Submodule.span K' (Set.range e)).map
          (LSpace (K := K') (Finsupp.mapDomain lift D)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hmem_img
    obtain ⟨y, hy, hyf⟩ := hmem_img
    rwa [show y = ⟨f', hf'⟩ from Subtype.ext hyf] at hy

  have hBasis : Module.Basis (Fin n) K' ↥(LSpace (K := K') (Finsupp.mapDomain lift D)) :=
    .mk hLI (le_of_eq hSpan.symm)
  calc ell (K := K') (D.mapDomain lift)
      = Fintype.card (Fin n) := Module.finrank_eq_card_basis hBasis
    _ = n := Fintype.card_fin n
    _ = ell (K := K) D := hn
