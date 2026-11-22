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
  Source file    : P2M/Sol/S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential.lean
  Source sha256  : fc31c0eaa8ee703d5bfae71890fb7453097c4c3e7c15cea7fb234229098d5275
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 4 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential
r2nos_namespace_dual

set_option autoImplicit false

universe u

open KaehlerDifferential
r2nos_open_dual "KaehlerDifferential"

namespace EtaleCoordGC7
r2nos_namespace_dual

open TensorProduct
r2nos_open_dual "TensorProduct"

theorem formallyEtale_of_bijective_mapBaseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra.FormallySmooth R T]
    (h : Function.Bijective (mapBaseChange R S T)) : Algebra.FormallyEtale S T := by

  have hδ : ∀ x : Algebra.H1Cotangent S T, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    apply h.1
    rw [map_zero]
    exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
  haveI : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp (hδ x)
    obtain ⟨y', rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T y).mp (hδ y)
    rw [Subsingleton.elim x' y']

  haveI : Subsingleton (Ω[T⁄S]) := by
    have hz : ∀ z : Ω[T⁄S], z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := KaehlerDifferential.map_surjective R S T z
      exact (KaehlerDifferential.exact_mapBaseChange_map R S T w).mpr (h.2 w)
    exact ⟨fun x y => by rw [hz x, hz y]⟩
  exact ⟨inferInstance, inferInstance⟩

end EtaleCoordGC7

open scoped TensorProduct in
r2nos_open_scoped_dual "TensorProduct" in
open EtaleCoordGC7 in
r2nos_open_dual "EtaleCoordGC7" in
theorem solution
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    {ι : Type u} [Finite ι] (a : ι → A)
    (b : Module.Basis ι A (Ω[A⁄R])) (hb : ∀ i, b i = KaehlerDifferential.D R A (a i)) :
    (MvPolynomial.aeval a : MvPolynomial ι R →ₐ[R] A).toRingHom.Etale := by
  classical
  letI algPA : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval a).toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => ((MvPolynomial.aeval a).commutes r).symm
  have halg : ∀ p : MvPolynomial ι R, algebraMap (MvPolynomial ι R) A p = MvPolynomial.aeval a p :=
    fun _ => rfl

  let b' : Module.Basis ι A (A ⊗[MvPolynomial ι R] Ω[(MvPolynomial ι R)⁄R]) :=
    Algebra.TensorProduct.basis A (KaehlerDifferential.mvPolynomialBasis R ι)
  have hX : ∀ i, KaehlerDifferential.mvPolynomialBasis R ι i =
      D R (MvPolynomial ι R) (MvPolynomial.X i) :=
    fun i => Module.Basis.apply_eq_iff.mpr (KaehlerDifferential.mvPolynomialBasis_repr_D_X R ι i)
  have hb' : ∀ i, mapBaseChange R (MvPolynomial ι R) A (b' i) = b i := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, mapBaseChange_tmul, one_smul, hX, map_D, halg,
      MvPolynomial.aeval_X, hb]
  have heq : mapBaseChange R (MvPolynomial ι R) A = (b'.equiv b (Equiv.refl ι)).toLinearMap :=
    b'.ext fun i => by rw [hb', LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hbij : Function.Bijective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [heq]; exact (b'.equiv b (Equiv.refl ι)).bijective
  haveI : Algebra.FormallyEtale (MvPolynomial ι R) A := formallyEtale_of_bijective_mapBaseChange hbij
  haveI : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  haveI : Algebra.Etale (MvPolynomial ι R) A := ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this
end S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
