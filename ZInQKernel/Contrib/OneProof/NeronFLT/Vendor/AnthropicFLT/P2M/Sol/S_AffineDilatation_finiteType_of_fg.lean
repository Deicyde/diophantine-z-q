/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AffineDilatation_finiteType_of_fg
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AffineDilatation_finiteType_of_fg

set_option autoImplicit false

universe u v

namespace AffineDilatation
p2m_export "AffineDilatation" "subalgebra Ring gen_subset"
namespace FiniteTypeProof
p2m_open "AffineDilatation"

variable {A : Type v} [CommRing A]

theorem fg_of_fg (I : Ideal A) (a : A) (hI : I.FG) : (subalgebra I a).FG := by
  classical
  obtain ⟨T, hT⟩ := hI
  let aa : Submonoid.powers a := ⟨a, Submonoid.mem_powers a⟩
  let f : A → Localization.Away a := fun g => IsLocalization.mk' (Localization.Away a) g aa
  refine ⟨T.image f, le_antisymm ?_ ?_⟩
  · apply Algebra.adjoin_le
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact gen_subset I a ⟨g, hT ▸ Ideal.subset_span hg, rfl⟩
  · apply Algebra.adjoin_le
    rintro x ⟨g, hg, rfl⟩
    have hg' : g ∈ Ideal.span (T : Set A) := hT ▸ hg
    clear hg
    change f g ∈ Algebra.adjoin A (↑(T.image f) : Set (Localization.Away a))
    have hu : ∀ g : A, f g = algebraMap A (Localization.Away a) g * f 1 := fun g =>
      IsLocalization.mk'_eq_mul_mk'_one g aa
    rw [hu]
    induction hg' using Submodule.span_induction with
    | mem t ht =>
        rw [← hu]
        exact Algebra.subset_adjoin (by rw [Finset.coe_image]; exact ⟨t, ht, rfl⟩)
    | zero => rw [map_zero, zero_mul]; exact Subalgebra.zero_mem _
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact Subalgebra.add_mem _ hx hy
    | smul c x _ hx =>
        rw [smul_eq_mul, map_mul, mul_assoc]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) hx

theorem finiteType (I : Ideal A) (a : A) (hI : I.FG) : Algebra.FiniteType A (Ring I a) :=
  (Subalgebra.fg_iff_finiteType _).mp (fg_of_fg I a hI)

end AffineDilatation.FiniteTypeProof

theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (I : Ideal A) (a : A) (hI : I.FG) :
    Algebra.FiniteType R (AffineDilatation.Ring I a) :=
  Algebra.FiniteType.trans (S := A) inferInstance
    (AffineDilatation.FiniteTypeProof.finiteType I a hI)
