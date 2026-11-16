/-
Vendored from the Fermat's Last Theorem Lean development (Anthropic).

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset.lean (2562 bytes, sha256 b345502c796091b0afd41d94e05df4db4f3a1d7090e524cb411a6450c803803b)
  Copyright      : 2026 Anthropic, PBC
  Licence        : Apache License, Version 2.0 (see LICENSE, NOTICE and NOTICE.md in
                   ZInQKernel/Contrib/CloudB3W12FiniteQuotient/)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-16, cloud batch 3 worker 12: this file has
been changed from the original, mechanically, to build on Lean v4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (the source builds on Lean v4.33.1 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d). No hypothesis or conclusion was weakened,
strengthened or omitted. Changes:
  * `import P2M.Util` removed (the file uses no port-utility command)
  * 18 occurrences of `(ρ g).hom` (for `ρ g : Aut X`) written `(ρ g).asIso.hom`, and `Aut.Aut_mul_def` written `Aut.mul_asIso` (2 uses): in Mathlib 56a `CategoryTheory.Aut X` is a structure with field `asIso`; same morphisms
  * file-level `set_option`s reproducing the source lakefile `leanOptions` (autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000, backward.isDefEq.respectTransparency.types false), plus `backward.isDefEq.respectTransparency.instanceSearchTypes false` (a Lean 4.35 option absent from Lean 4.33.1; `false` restores the 4.33.1 behaviour); the source file's own `set_option`s are kept and take precedence where they repeat one
  * an explicit `end P2MW.S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset` added before the final `end` (the source leaves that namespace
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

namespace P2MW.S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u v

namespace HADM10

open TopologicalSpace

theorem mem_iInf_iff {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens) (x : X) :
    x ∈ (⨅ i, U i) ↔ ∀ i, x ∈ U i := by
  constructor
  · intro h i; exact (iInf_le U i) h
  · intro h
    haveI := Fintype.ofFinite ι
    rw [← Finset.inf_univ_eq_iInf]
    simp only [← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simpa using h

end HADM10

theorem solution
    {B : Type u} [CommRing B] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πX)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X) :
    ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U := by
  classical
  intro x
  haveI : Fintype G := Fintype.ofFinite G

  haveI : X.IsSeparated := by
    have : IsSeparated (πX ≫ Limits.terminal.from _) := inferInstance
    rw [Limits.terminal.comp_from] at this
    exact ⟨this⟩

  obtain ⟨U₀, hU₀, hmem⟩ := hAF (Finset.univ.image fun g : G => (ρ g).asIso.hom.base x)
  refine ⟨⨅ g : G, (ρ g).asIso.hom ⁻¹ᵁ U₀, ?_, ?_, ?_⟩
  · exact IsAffineOpen.iInf (fun g => hU₀.preimage_of_isIso (ρ g).asIso.hom)
  · rw [HADM10.mem_iInf_iff]
    intro g
    exact hmem _ (Finset.mem_image.2 ⟨g, Finset.mem_univ _, rfl⟩)
  · intro h
    ext y
    constructor
    · intro hy
      change (ρ h).asIso.hom.base y ∈ (⨅ g : G, (ρ g).asIso.hom ⁻¹ᵁ U₀) at hy
      rw [HADM10.mem_iInf_iff] at hy
      rw [SetLike.mem_coe, HADM10.mem_iInf_iff]
      intro g

      have := hy (g * h⁻¹)
      change (ρ (g * h⁻¹)).asIso.hom.base ((ρ h).asIso.hom.base y) ∈ U₀ at this
      rw [← Scheme.Hom.comp_apply, show (ρ h).asIso.hom ≫ (ρ (g * h⁻¹)).asIso.hom = (ρ g).asIso.hom by
        rw [← Iso.trans_hom, ← Aut.mul_asIso, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]] at this
      exact this
    · intro hy
      rw [SetLike.mem_coe, HADM10.mem_iInf_iff] at hy
      change (ρ h).asIso.hom.base y ∈ (⨅ g : G, (ρ g).asIso.hom ⁻¹ᵁ U₀)
      rw [HADM10.mem_iInf_iff]
      intro g
      change ((ρ h).asIso.hom ≫ (ρ g).asIso.hom).base y ∈ U₀
      rw [show (ρ h).asIso.hom ≫ (ρ g).asIso.hom = (ρ (g * h)).asIso.hom by rw [← Iso.trans_hom, ← Aut.mul_asIso, ← map_mul]]
      exact hy (g * h)

end P2MW.S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset

end ZInQ.Contrib.CloudW03NeronSurj.FLT
