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
  Source file    : P2M/Sol/S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact.lean
  Source sha256  : 05e3be335d7017fe85a7169caed517d4e7f4d3f0fe9ea1577c33b7cafc7d84dc
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
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

namespace P2MW.S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

namespace NoethDesc
r2nos_namespace_dual

theorem isNoetherianRing_of_faithfullyFlat (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [IsNoetherianRing B] : IsNoetherianRing A := by
  have hmono : StrictMono (Ideal.map (algebraMap A B)) :=
    Monotone.strictMono_of_injective (fun I J h => Ideal.map_mono h) Ideal.map_injective_of_faithfullyFlat
  haveI : WellFoundedGT (Ideal B) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)
  haveI : WellFoundedGT (Ideal A) := hmono.wellFoundedGT
  exact isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr inferInstance)

theorem flat_pi {R : Type*} [CommRing R] {ι : Type*} [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Flat R (S i)] : Module.Flat R (Π i, S i) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Module.Flat R (DirectSum ι S) := Module.Flat.directSum_iff.mpr inferInstance
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι S).symm

end NoethDesc

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] [IsLocallyNoetherian X] :
    IsLocallyNoetherian Y := by
  classical
  refine ⟨fun V => ?_⟩

  have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
  obtain ⟨s, hs, hsU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hc
  haveI : Finite s := hs.to_subtype
  have hle : ∀ i : s, ((i : X.affineOpens) : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    intro i
    rw [hsU]
    exact le_iSup₂ (f := fun (j : X.affineOpens) (_ : j ∈ s) => (j : X.Opens)) i.1 i.2

  let R := Γ(Y, (V : Y.Opens))
  let S : s → Type _ := fun i => Γ(X, ((i : X.affineOpens) : X.Opens))
  let φ : ∀ i : s, R →+* S i := fun i => (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle i)).hom
  letI : ∀ i : s, Algebra R (S i) := fun i => (φ i).toAlgebra

  haveI : ∀ i : s, Module.Flat R (S i) := fun i => by
    have hflat : (φ i).Flat :=
      HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) f (inferInstance : AlgebraicGeometry.Flat f) V i.1 (hle i)
    exact hflat
  haveI : ∀ i : s, IsNoetherianRing (S i) := fun i => IsLocallyNoetherian.component_noetherian (i : X.affineOpens)

  haveI : Module.Flat R (Π i : s, S i) := NoethDesc.flat_pi S
  haveI : IsNoetherianRing (Π i : s, S i) := inferInstance

  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R (Π i : s, S i))) := by
    intro 𝔭

    let y : Y := V.2.fromSpec.base 𝔭
    obtain ⟨x, hx⟩ := (‹Surjective f›).surj y
    have hxV : x ∈ (f ⁻¹ᵁ (V : Y.Opens) : X.Opens) := by
      show f.base x ∈ (V : Y.Opens)
      rw [hx]
      have hy : y ∈ Set.range V.2.fromSpec.base := ⟨𝔭, rfl⟩
      rw [V.2.range_fromSpec] at hy
      exact hy
    rw [hsU] at hxV
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ s, x ∈ ((i : X.affineOpens) : X.Opens) := by
      simpa only [TopologicalSpace.Opens.mem_iSup, exists_prop] using hxV
    obtain ⟨𝔮, h𝔮⟩ : ∃ 𝔮, (i : X.affineOpens).2.fromSpec.base 𝔮 = x := by
      have : x ∈ Set.range (i : X.affineOpens).2.fromSpec.base := by rw [(i : X.affineOpens).2.range_fromSpec]; exact hxi
      exact this

    have hcomap : PrimeSpectrum.comap (φ ⟨i, hi⟩) 𝔮 = 𝔭 := by
      have hnat := IsAffineOpen.SpecMap_appLE_fromSpec f V.2 (i : X.affineOpens).2 (hle ⟨i, hi⟩)
      have h1 : V.2.fromSpec.base ((Spec.map (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle ⟨i, hi⟩))).base 𝔮) =
          V.2.fromSpec.base 𝔭 := by
        have h2 : (Spec.map (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle ⟨i, hi⟩)) ≫ V.2.fromSpec) 𝔮 =
            ((i : X.affineOpens).2.fromSpec ≫ f) 𝔮 := by rw [hnat]
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
        show V.2.fromSpec ((Spec.map (f.appLE (V : Y.Opens) ((i : X.affineOpens) : X.Opens) (hle ⟨i, hi⟩))) 𝔮) = V.2.fromSpec 𝔭
        rw [h2]
        show f.base ((i : X.affineOpens).2.fromSpec.base 𝔮) = V.2.fromSpec.base 𝔭
        rw [h𝔮, hx]
      exact V.2.fromSpec.isOpenEmbedding.injective h1
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun i : s => S i) ⟨i, hi⟩) 𝔮, ?_⟩
    rw [← hcomap, ← PrimeSpectrum.comap_comp_apply]
    rfl
  haveI : Module.FaithfullyFlat R (Π i : s, S i) := Module.FaithfullyFlat.of_comap_surjective hsurj
  exact NoethDesc.isNoetherianRing_of_faithfullyFlat R (Π i : s, S i)
end S_AlgebraicGeometry_isLocallyNoetherian_of_flat_of_surjective_of_quasiCompact
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
