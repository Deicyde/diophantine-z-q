/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean
  Retrieved      : 2026-11-16 (immutable raw blob at the revision above; bytes and sha256 in
                   `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/PORT_MANIFEST.md`)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(Cloud Batch 3 Worker 13 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
2026-11-16). The changes are mechanical; no statement, hypothesis, definition or proof term was
weakened or omitted unless listed under "manual repairs":
  * the whole file is wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end`, so the
    source's root declarations become `ZInQ.Contrib.CloudW03NeronSurj.FLT.<name>`;
  * the source's `import P2M.Util` is dropped: this port contains no port commands, no local
    notation, no macro and no elaborator. The source's
    `p2m_open "KaehlerDifferential Algebra TensorProduct Algebra.TensorProduct"` is written as the
    ordinary `open` command it abbreviated;
  * file-level `set_option`s reproduce the source build environment (source lakefile.lean
    leanOptions: autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000,
    backward.isDefEq.respectTransparency.types false) together with
    backward.isDefEq.respectTransparency.instanceSearchTypes false, a Lean 4.35 option absent from
    the source's Lean 4.33.1 whose `false` value restores the 4.33.1 behaviour;
  * scopes the source leaves open at end of file are closed explicitly (no-op).
  * every `open` of a Mathlib namespace is written `_root_.<Namespace>`: inside the port
    namespace a bare `open N` resolves to `ZInQ.Contrib.CloudW03NeronSurj.FLT.N` whenever that
    namespace exists in the environment and then shadows Mathlib's root `N`, which is what the
    source's `r2nos_open_dual` shim worked around. Naming the root explicitly is the ordinary-Lean
    equivalent and is stable however the import graph grows.
Manual repairs: none.
-/

import Mathlib

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension

open _root_.KaehlerDifferential _root_.Algebra _root_.TensorProduct _root_.Algebra.TensorProduct

universe u

namespace R1NeronObjE2

section algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem subsingleton_kaehler_of_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton Ω[T⁄S] := by
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hsurj := KaehlerDifferential.map_surjective R S T
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have ha : KaehlerDifferential.map R S T T a' = 0 := by
    obtain ⟨x, rfl⟩ := h a'
    exact hex.apply_apply_eq_zero x
  have hb : KaehlerDifferential.map R S T T b' = 0 := by
    obtain ⟨x, rfl⟩ := h b'
    exact hex.apply_apply_eq_zero x
  rw [ha, hb]

theorem formallyEtale_of_formallySmooth_of_bijective [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  haveI hΩ : Subsingleton Ω[T⁄S] := subsingleton_kaehler_of_surjective h.2
  haveI : Algebra.FormallyUnramified S T := ⟨hΩ⟩

  have hδ : ∀ x, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R S T
    have hmem : Algebra.H1Cotangent.δ R S T x ∈
        LinearMap.ker (KaehlerDifferential.mapBaseChange R S T) := by
      rw [LinearMap.mem_ker]
      exact hex.apply_apply_eq_zero x
    rwa [LinearMap.ker_eq_bot.mpr h.1, Submodule.mem_bot] at hmem

  haveI hH1 : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun a b => ?_⟩
    have hex := Algebra.H1Cotangent.exact_map_δ R S T
    have ha : a ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex a).mp (hδ a)
    have hb : b ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex b).mp (hδ b)
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [Subsingleton.elim a' b']
  haveI : Module.Projective T Ω[T⁄S] := Module.Projective.of_free
  haveI : Algebra.FormallySmooth S T := ⟨inferInstance, hH1⟩
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

theorem mapBaseChange_surjective_of_formallyUnramified [Algebra.FormallyUnramified S T] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R S T) := by
  intro y
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hy : KaehlerDifferential.map R S T T y = 0 := Subsingleton.elim _ _
  exact (hex y).mp hy

theorem bijective_of_surjective_of_finrank_eq {A : Type*} [CommRing A] [Nontrivial A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hrank : Module.finrank A M = Module.finrank A N) : Function.Bijective f := by
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap f e.injective hf

theorem formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.FormallyEtale S T := by
  haveI : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine formallyEtale_of_formallySmooth_of_bijective (R := R) ?_
  have hsurj := mapBaseChange_surjective_of_formallyUnramified (R := R) (S := S) (T := T)
  cases subsingleton_or_nontrivial T with
  | inl hT =>
      exact ⟨fun a b _ => Subsingleton.elim _ _, hsurj⟩
  | inr hT =>
      haveI : Nontrivial S := (algebraMap S T).domain_nontrivial
      have hS : Module.rank S Ω[S⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hTr : Module.rank T Ω[T⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hSf : Module.finrank S Ω[S⁄R] = n := Module.finrank_eq_of_rank_eq hS
      have hTf : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq hTr
      exact bijective_of_surjective_of_finrank_eq _ hsurj
        (by rw [Module.finrank_baseChange, hSf, hTf])

theorem etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T := by
  haveI := formallyEtale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
    (R := R) (S := S) (T := T) n
  haveI : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

end algebra

end R1NeronObjE2

theorem solution
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension n R T]
    [Algebra.FormallyUnramified S T] :
    Algebra.Etale S T :=
  R1NeronObjE2.etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (R := R) n

end P2MW.S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension

end ZInQ.Contrib.CloudW03NeronSurj.FLT
