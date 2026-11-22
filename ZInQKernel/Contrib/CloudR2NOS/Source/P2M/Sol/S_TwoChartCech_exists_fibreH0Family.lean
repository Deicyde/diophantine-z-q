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
  Source file    : P2M/Sol/S_TwoChartCech_exists_fibreH0Family.lean
  Source sha256  : dc3957d4545d2f86df4ea6d3b841c88368557836ab1116ffbade68e0e5753fdc
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_TwoChartCech_nonempty_kerBaseChangeTowerEquiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_TwoChartCech_exists_fibreH0Family
r2nos_namespace_dual

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
r2nos_open_dual "CategoryTheory AlgebraicGeometry Opposite TensorProduct"

namespace TwoChartCech
r2nos_namespace_dual
w03_export "TwoChartCech" "exists_twoTermComplex_kerMapBaseChange_bijective finrank_ker_baseChange_eq_of_field_extension nonempty_kerBaseChangeTowerEquiv"
w03_open "TwoChartCech"
namespace Family
r2nos_namespace_dual

def baseChangeTTC {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
    (S : Type u) [CommRing S] [Algebra R S] : CoherentBaseChange.TwoTermComplex.{u, u} S :=
  haveI : Module.Finite S (S ⊗[R] G.C0) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R G.C0))
  haveI : Module.Finite S (S ⊗[R] G.C1) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R G.C1))
  { C0 := S ⊗[R] G.C0, C1 := S ⊗[R] G.C1, d := G.d.baseChange S }

@[reducible] def algebraOfHom' {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U : T.Opens) :
    Algebra R Γ(T, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

theorem specMap_algebraMap_eq {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U : T.Opens)
    (hU : IsAffineOpen U) :
    letI := algebraOfHom' f U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, U))) = hU.fromSpec ≫ f := by
  letI := algebraOfHom' f U
  have halg : (algebraMap R Γ(T, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ f ⁻¹ᵁ ⊤)]

theorem base_eq_comap {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U : T.Opens)
    (hU : IsAffineOpen U) (x : U) :
    letI := algebraOfHom' f U
    f.base x.1 = PrimeSpectrum.comap (algebraMap R Γ(T, U)) (hU.primeIdealOf x) := by
  letI := algebraOfHom' f U
  have h1 : f.base x.1 = (hU.fromSpec ≫ f).base (hU.primeIdealOf x) := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, hU.fromSpec_primeIdealOf x]
  rw [h1, ← specMap_algebraMap_eq f U hU]
  rfl

end Family

open Family
r2nos_open_dual "Family"

theorem exists_fibreH0Family'
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, F.h0 x = Module.finrank (f.base x).asIdeal.ResidueField
        (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField)) := by
  obtain ⟨G, ι0, ι1, comm, hG⟩ := exists_twoTermComplex_kerMapBaseChange_bijective d
  refine ⟨{ G := fun U hU => letI := algebraOfHom' f U; baseChangeTTC G Γ(T, U)
            h0 := fun x => Module.finrank (f.base x).asIdeal.ResidueField
              (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))
            hglue := ?_ }, fun x => rfl⟩
  intro U hU x
  letI := algebraOfHom' f U

  let 𝔮 : PrimeSpectrum Γ(T, U) := hU.primeIdealOf x
  let 𝔭 : PrimeSpectrum R := f.base x.1
  have hpq : 𝔭.asIdeal = Ideal.comap (algebraMap R Γ(T, U)) 𝔮.asIdeal := by
    show (f.base x.1).asIdeal = _
    rw [base_eq_comap f U hU x]; rfl

  let φ : 𝔭.asIdeal.ResidueField →ₐ[R] 𝔮.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ 𝔭.asIdeal 𝔮.asIdeal (Algebra.ofId R Γ(T, U)) hpq
  letI : Algebra 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm

  rw [finrank_ker_baseChange_eq_of_field_extension d 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField]

  rw [← (LinearEquiv.ofBijective _ (hG 𝔮.asIdeal.ResidueField)).finrank_eq]

  obtain ⟨e, -⟩ := nonempty_kerBaseChangeTowerEquiv G.d Γ(T, U) 𝔮.asIdeal.ResidueField
  rw [← e.finrank_eq]
  rfl

end TwoChartCech

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, F.h0 x = Module.finrank (f.base x).asIdeal.ResidueField
        (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField)) :=
  TwoChartCech.exists_fibreH0Family' d f

end
end S_TwoChartCech_exists_fibreH0Family
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
