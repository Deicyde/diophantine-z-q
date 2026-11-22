/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicCurve_infinite_setOf_isClosed_singleton.lean
  Source sha256  : ba448a8710fa565fe28d6201de76ffbe9c9108dd7c82cafe771e2d8f28e13a38
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_infinite_setOf_isClosed_singleton
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing
r2nos_open_dual "CategoryTheory AlgebraicGeometry IsLocalRing"

universe u

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "isClosed_singleton_of_ne_genericPoint"
namespace LInf
r2nos_namespace_dual
w03_open "AlgebraicCurve"

theorem isField_of_isMaximal_bot (A : Type*) [CommRing A] [Nontrivial A]
    (h : (⊥ : Ideal A).IsMaximal) : IsField A := by
  exact Ring.isField_iff_maximal_bot.mpr h

theorem isField_of_finite_maximalSpectrum (A : Type*) [CommRing A] [IsDomain A] [IsJacobsonRing A]
    [Finite (MaximalSpectrum A)] : IsField A := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out ‹_› Ideal.isRadical_bot
  have hprod : (Finset.univ : Finset (MaximalSpectrum A)).prod (fun m => m.asIdeal) ≤ ⊥ := by
    rw [← hjac]
    refine le_trans Ideal.prod_le_inf ?_
    refine le_sInf fun J hJ => ?_
    exact Finset.inf_le (Finset.mem_univ (⟨J, hJ.2⟩ : MaximalSpectrum A))
  obtain ⟨m, -, hm⟩ := (Ideal.IsPrime.prod_le (Ideal.isPrime_bot (α := A))).mp hprod
  have hm0 : m.asIdeal = ⊥ := le_bot_iff.mp hm
  exact isField_of_isMaximal_bot A (hm0 ▸ m.isMaximal)

end AlgebraicCurve.LInf

open AlgebraicCurve.LInf in
r2nos_open_dual "AlgebraicCurve.LInf" in
theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] :
    {x : C | IsClosed ({x} : Set C)}.Infinite := by
  classical

  obtain ⟨U, hU, V, hV, hηV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c)
      (genericPoint C)
  have hfU : c.base (genericPoint C) ∈ U := hle hηV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (c.base (genericPoint C))]; exact hfU
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(C, V) := (c.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  letI : Algebra k Γ(C, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(C, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩

  haveI : Algebra.FiniteType k Γ(C, V) := by
    obtain ⟨g, hg⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k Γ(C, V)
    letI : Algebra (MvPolynomial (Fin 1) k) Γ(C, V) := g.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin 1) k) Γ(C, V) := hg
    haveI : IsScalarTower k (MvPolynomial (Fin 1) k) Γ(C, V) :=
      IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
    exact (inferInstance : Algebra.FiniteType k (MvPolynomial (Fin 1) k)).trans
      (inferInstance : Algebra.FiniteType (MvPolynomial (Fin 1) k) Γ(C, V))
  haveI : IsJacobsonRing Γ(C, V) := isJacobsonRing_of_finiteType (A := k)

  have hnf : ¬ IsField Γ(C, V) := by
    intro hF
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(C, V)
    haveI := hm
    obtain ⟨_, hdvr⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
        (k := k) m
    have h0 : (0 : Γ(C, V)) ∉ m.primeCompl := fun h => h m.zero_mem
    have hbij := hF.localization_map_bijective (Rₘ := Localization.AtPrime m) h0
    exact IsDiscreteValuationRing.not_isField (Localization.AtPrime m)
      ((RingEquiv.ofBijective _ hbij).symm.toMulEquiv.isField hF)

  by_contra hinf
  have hfin : {x : C | IsClosed ({x} : Set C)}.Finite := Set.not_infinite.mp hinf
  let g : MaximalSpectrum Γ(C, V) → C := fun m => hV.fromSpec ⟨m.asIdeal, m.isMaximal.isPrime⟩
  have hg_closed : ∀ m, IsClosed ({g m} : Set C) := by
    intro m
    apply AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c
    intro hη
    apply hnf
    have hbot : (⟨m.asIdeal, m.isMaximal.isPrime⟩ : PrimeSpectrum Γ(C, V)) = ⊥ := by
      apply hV.fromSpec.isOpenEmbedding.injective
      change g m = _
      rw [hη, ← genericPoint_eq_bot_of_affine, genericPoint_eq_of_isOpenImmersion hV.fromSpec]
    have hm0 : m.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal hbot
    exact isField_of_isMaximal_bot _ (hm0 ▸ m.isMaximal)
  have hg_inj : Function.Injective g := by
    intro m m' h
    have h' := hV.fromSpec.isOpenEmbedding.injective h
    exact MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal h')
  haveI : Finite (MaximalSpectrum Γ(C, V)) := by
    haveI := hfin.to_subtype
    refine Finite.of_injective
      (fun m => (⟨g m, hg_closed m⟩ : {x : C | IsClosed ({x} : Set C)})) ?_
    intro m m' h
    apply hg_inj
    simp only [Subtype.mk.injEq] at h
    exact h
  exact hnf (isField_of_finite_maximalSpectrum Γ(C, V))
end S_AlgebraicCurve_infinite_setOf_isClosed_singleton
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
