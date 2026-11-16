/-
Vendored from the Fermat's Last Theorem Lean development (Anthropic).

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective.lean (2662 bytes, sha256 ee7bdab172bc67057a66620d1d21930020ea5536b7a0bf8cfb693807d01bd785)
  Copyright      : 2026 Anthropic, PBC
  Licence        : Apache License, Version 2.0 (see LICENSE, NOTICE and NOTICE.md in
                   ZInQKernel/Contrib/CloudB3W12FiniteQuotient/)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-16, cloud batch 3 worker 12: this file has
been changed from the original, mechanically, to build on Lean v4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (the source builds on Lean v4.33.1 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d). No hypothesis or conclusion was weakened,
strengthened or omitted. Changes:
  * `import P2M.Util` removed (the file uses no port-utility command)
  * file-level `set_option`s reproducing the source lakefile `leanOptions` (autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000, backward.isDefEq.respectTransparency.types false), plus `backward.isDefEq.respectTransparency.instanceSearchTypes false` (a Lean 4.35 option absent from Lean 4.33.1; `false` restores the 4.33.1 behaviour); the source file's own `set_option`s are kept and take precedence where they repeat one
  * an explicit `end P2MW.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective` added before the final `end` (the source leaves that namespace
    open at the end of the file, which Lean closes implicitly; needed so the port namespace can be closed)
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`, so every declaration of the source is isolated under that prefix (the convention of the existing port ZInQKernel/Contrib/CloudW03NeronSurj)
-/

import Mathlib

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u
open CategoryTheory.Limits

theorem solution
    {B : Type u} [CommRing B] {M X : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of B))
    (πX : X ⟶ Spec (CommRingCat.of B)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (hsep : IsSeparated πM) (hqc : QuasiCompact πM) :
    IsSeparated πX ∧ QuasiCompact πX := by
  haveI := hint
  haveI hπsurj : Surjective π := ⟨hsurj⟩
  haveI := hsep
  haveI := hqc
  constructor
  ·
    let ππ : pullback πM πM ⟶ pullback πX πX :=
      pullback.map πM πM πX πX π π (𝟙 _) ((Category.comp_id _).trans hπX.symm) ((Category.comp_id _).trans hπX.symm)
    have hUC : UniversallyClosed ππ :=
      MorphismProperty.pullbackMap (P := @UniversallyClosed) (inferInstance : UniversallyClosed π)
        (inferInstance : UniversallyClosed π) hπX.symm hπX.symm
    have hS : Surjective ππ :=
      MorphismProperty.pullbackMap (P := @Surjective) hπsurj hπsurj hπX.symm hπX.symm
    have hsq : pullback.diagonal πM ≫ ππ = π ≫ pullback.diagonal πX := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.diagonal_fst,
          Category.id_comp, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.diagonal_snd,
          Category.id_comp, pullback.diagonal_snd, Category.comp_id]
    have hrange : Set.range (pullback.diagonal πX) = ππ '' Set.range (pullback.diagonal πM) := by
      rw [← Set.range_comp]
      change Set.range (pullback.diagonal πX).base = Set.range ((pullback.diagonal πM ≫ ππ).base)
      rw [hsq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj,
        Set.image_univ]
    have hclosed : IsClosed (Set.range (pullback.diagonal πX)) := by
      rw [hrange]
      exact ππ.isClosedMap _ (pullback.diagonal πM).isClosedEmbedding.isClosed_range
    exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩
  ·
    constructor
    intro U hU hUc
    have : πX ⁻¹' U = π '' (πM ⁻¹' U) := by
      rw [← hπX]
      change πX.base ⁻¹' U = π.base '' ((π ≫ πX).base ⁻¹' U)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ hsurj]
    rw [this]
    exact (QuasiCompact.isCompact_preimage U hU hUc).image π.continuous

end P2MW.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective

end ZInQ.Contrib.CloudW03NeronSurj.FLT
