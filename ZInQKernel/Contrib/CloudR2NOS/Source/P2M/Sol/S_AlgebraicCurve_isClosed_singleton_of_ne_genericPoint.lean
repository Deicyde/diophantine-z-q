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
  Source file    : P2M/Sol/S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint.lean
  Source sha256  : 422c0a3c21c588e2586a902f262b81d9646dd55f6658fc5cc83cb6177ea06e1c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
r2nos_namespace_dual

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing Topology
r2nos_open_dual "CategoryTheory AlgebraicGeometry IsLocalRing Topology"

namespace Algebra
r2nos_namespace_dual
w03_export "Algebra" "algebraMap IsStandardSmoothOfRelativeDimension mem_bot IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime"
namespace IsStandardSmoothOfRelativeDimension
r2nos_namespace_dual
w03_export "Algebra.IsStandardSmoothOfRelativeDimension" "isDiscreteValuationRing_localization_atPrime"
end Algebra.IsStandardSmoothOfRelativeDimension
r2nos_open_scoped "Algebra Algebra.IsStandardSmoothOfRelativeDimension" in

theorem Algebra.IsStandardSmoothOfRelativeDimension.isMaximal_of_isPrime_of_ne_bot
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (q : Ideal A) [hq : q.IsPrime] (hq0 : q ≠ ⊥) : q.IsMaximal := by
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q hq.ne_top
  obtain ⟨_, hdvr⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := k) m

  have hdisj : Disjoint (m.primeCompl : Set A) q := by
    rw [Set.disjoint_left]; intro a ha haq; exact ha (hqm haq)
  haveI hq' : (q.map (algebraMap A (Localization.AtPrime m))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ q hq hdisj
  have hinj := IsLocalization.injective (Localization.AtPrime m) m.primeCompl_le_nonZeroDivisors
  have hq'0 : q.map (algebraMap A (Localization.AtPrime m)) ≠ ⊥ := by
    intro h
    apply hq0
    refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
    have hmem : algebraMap A (Localization.AtPrime m) a ∈ q.map (algebraMap A _) :=
      Ideal.mem_map_of_mem _ ha
    rw [h, Ideal.mem_bot] at hmem
    exact (injective_iff_map_eq_zero _).mp hinj a hmem
  have hmax' : (q.map (algebraMap A (Localization.AtPrime m))).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hq'0 hq'
  have heq : q.map (algebraMap A (Localization.AtPrime m)) = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal hmax'

  have : q = m := by
    refine le_antisymm hqm fun a ha => ?_
    have h1 := IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m)
      hq hdisj
    have hmem : a ∈ Ideal.comap (algebraMap A (Localization.AtPrime m))
        (q.map (algebraMap A (Localization.AtPrime m))) := by
      rw [Ideal.mem_comap, heq]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m a).mpr ha
    exact h1.le hmem
  exact this ▸ hm

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : x ≠ genericPoint C) : IsClosed ({x} : Set C) := by
  classical
  rw [← closure_subset_iff_isClosed]
  intro y hy

  obtain ⟨U, hU, V, hV, hyV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) y
  have hxV : x ∈ V := by
    obtain ⟨w, hwV, hwx⟩ := mem_closure_iff.mp hy V V.isOpen hyV
    rw [Set.mem_singleton_iff] at hwx
    exact hwx ▸ hwV

  have hcyU : c.base y ∈ U := hle hyV
  obtain rfl : U = ⊤ := top_le_iff.mp fun w _ => by
    rw [Subsingleton.elim w (c.base y)]; exact hcyU
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(C, V) := (c.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  letI : Algebra K Γ(C, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(C, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩

  set qx := hV.primeIdealOf ⟨x, hxV⟩ with hqx
  set qy := hV.primeIdealOf ⟨y, hyV⟩ with hqy

  have hspec : (⟨x, hxV⟩ : V) ⤳ ⟨y, hyV⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp (specializes_iff_mem_closure.mpr hy)
  have hle' : qx.asIdeal ≤ qy.asIdeal :=
    (PrimeSpectrum.le_iff_specializes qx qy).mpr (hspec.map hV.isoSpec.hom.base.hom.continuous)

  have hinj : Function.Injective (hV.isoSpec.hom.base) := (Scheme.homeoOfIso hV.isoSpec).injective
  have hqx0 : qx.asIdeal ≠ ⊥ := by
    intro h0
    apply hx
    have h1 : qx = genericPoint (Spec Γ(C, V)) := by
      rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext h0
    rw [← hV.primeIdealOf_genericPoint] at h1
    exact congrArg Subtype.val (hinj h1)

  have hqxmax : qx.asIdeal.IsMaximal :=
    Algebra.IsStandardSmoothOfRelativeDimension.isMaximal_of_isPrime_of_ne_bot (k := K) _ hqx0
  have hqq : qx = qy := PrimeSpectrum.ext (hqxmax.eq_of_le qy.isPrime.ne_top hle')
  have hxy : (⟨x, hxV⟩ : V) = ⟨y, hyV⟩ := hinj hqq
  rw [Set.mem_singleton_iff]
  exact (congrArg Subtype.val hxy).symm
end S_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
