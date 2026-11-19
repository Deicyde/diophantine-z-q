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
  Source file    : Theorems/Thm_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective.lean
  Source sha256  : 14166a1e9c3512d67dcf6c305e99c7629040d815003260435a454278529a3ffe
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Nilpotent.Defs
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

theorem TwoChartCech.projective_ker_of_isReduced_of_kerMapBaseChange_bijective
    {R : Type u} [CommRing R] [IsReduced R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0]
    [AddCommGroup C1] [Module R C1] {d : C0 →ₗ[R] C1}
    (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d)
    (hG : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A))
    {n : ℕ} (hH0 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Projective R (LinearMap.ker d) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], Function.Bijective (TwoChartCech.kerBaseChangeHom d A)) ∧
      ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
          (𝔭.asIdeal.ResidueField ⊗[R] LinearMap.ker d) = n := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
