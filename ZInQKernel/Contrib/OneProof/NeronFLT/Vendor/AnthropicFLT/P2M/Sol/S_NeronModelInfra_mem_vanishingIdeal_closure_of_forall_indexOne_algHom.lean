/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (S : Set X)
    (hS : ∀ s ∈ S, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    let J : Ideal Γ(X, U) :=
      PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ closure S})
    ∀ g : Γ(X, U),
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : Γ(X, U) →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J := by
  letI : Algebra R Γ(X, U) :=
    ((X.presheaf.map (homOfLE le_top).op).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  intro J g hg
  rw [PrimeSpectrum.mem_vanishingIdeal]
  rintro 𝔭 ⟨y, hy, rfl⟩

  let Z : Set U := {z : U | g ∈ (hU.primeIdealOf z).asIdeal}
  have hZ : IsClosed Z := by
    have : Z = hU.isoSpec.hom.base ⁻¹' PrimeSpectrum.zeroLocus {g} := by
      ext z
      change g ∈ (hU.isoSpec.hom.base z).asIdeal ↔ ({g} : Set Γ(X, U)) ⊆ ((hU.isoSpec.hom.base z).asIdeal : Set Γ(X, U))
      rw [Set.singleton_subset_iff]
      rfl
    rw [this]
    exact (PrimeSpectrum.isClosed_zeroLocus _).preimage hU.isoSpec.hom.base.hom.continuous

  let A : Set U := {s : U | (s : X) ∈ S}
  have hAZ : A ⊆ Z := by
    intro s hs
    obtain ⟨R', _, _, _, _, _, hR', x, hx⟩ := hS s.1 hs
    have hxU : x.1 (IsLocalRing.closedPoint R') ∈ U := by rw [hx]; exact s.2
    obtain ⟨c, hc⟩ :=
      NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem f R' x U hU hxU
    have hs' : (⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩ : U) = s := Subtype.ext hx
    have hJc : J ≤ (IsLocalRing.maximalIdeal R').comap c := by
      rw [hc]
      intro j hj
      rw [PrimeSpectrum.mem_vanishingIdeal] at hj
      exact hj _ ⟨_, by rw [hs']; exact subset_closure hs, rfl⟩
    have := hg R' hR' c hJc
    rw [hc, hs'] at this
    exact this

  have hyA : y ∈ closure A := by
    have hind : Topology.IsInducing ((↑) : U → X) := Topology.IsInducing.subtypeVal
    have key : y ∈ ((↑) : U → X) ⁻¹' closure (((↑) : U → X) '' A) := by
      rw [Set.mem_preimage]
      refine closure_mono ?_ (show (y : X) ∈ closure ((U : Set X) ∩ S) from U.2.inter_closure ⟨y.2, hy⟩)
      rintro _ ⟨hzU, hzS⟩
      exact ⟨⟨_, hzU⟩, hzS, rfl⟩
    exact (hind.closure_eq_preimage_closure_image A).symm ▸ key
  exact hZ.closure_subset_iff.mpr hAZ hyA
