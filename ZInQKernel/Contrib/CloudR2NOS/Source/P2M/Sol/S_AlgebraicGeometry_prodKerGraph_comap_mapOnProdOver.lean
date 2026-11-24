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
  Source file    : P2M/Sol/S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver.lean
  Source sha256  : 2b33266348fdc03e64b5e83d4145a55a6a3f1e6bb79104ef4921adbd7bb78add
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme IsSeparated Scheme.IdealSheafData prodKerGraph prodKerGraph_eq_prod graphOver RelEffCartierDiv mapOnProdOver RelEffCartierDiv.I RelEffCartierDiv.pullbackAlong_ofPoint Scheme.IdealSheafData.comap_mul"
namespace ProdKerGraphNaturality
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
  {g' : T' ⟶ S}

theorem ker_graphOver_comap (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) =
      (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).ker :=
  congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint f a ha φ hφ)

omit [IsSeparated f] in

theorem comap_finsetProd {ι : Type*} (s : Finset ι)
    (I : ι → (pullback f g').IdealSheafData) (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (∏ i ∈ s, I i).comap (mapOnProdOver f φ hφ) = ∏ i ∈ s, (I i).comap (mapOnProdOver f φ hφ) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

theorem prodKerGraph_comap {r : ℕ} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g')
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) := by
  simp only [prodKerGraph_eq_prod, comap_finsetProd, ker_graphOver_comap]

end AlgebraicGeometry.ProdKerGraphNaturality

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g') (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) :=
  AlgebraicGeometry.ProdKerGraphNaturality.prodKerGraph_comap a ha φ hφ
end S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
