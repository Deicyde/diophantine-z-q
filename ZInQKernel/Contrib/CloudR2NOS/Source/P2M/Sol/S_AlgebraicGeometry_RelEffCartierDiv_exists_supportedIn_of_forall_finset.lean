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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset.lean
  Source sha256  : f84cc097e951b0176360c1a373796b311789134ed8597fbb247cbc629bab6b1e
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Opens.range_ι Scheme.Hom Scheme IsAffineOpen Scheme.Opens Scheme.Hom.comp_apply RelEffCartierDiv"
namespace RelEffCartierDiv
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelEffCartierDiv" "SupportedIn supportedInLocus mem_supportedInLocus_iff supportedIn_pullbackAlong_iff pullbackAlong I isFinite"
w03_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

set_option backward.isDefEq.respectTransparency false in
theorem exists_supportedIn_of_forall_finset_aux
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (V : S.affineOpens) (U : 𝒞.affineOpens)
      (_ : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
      (D.pullbackAlong W.ι rfl).SupportedIn U := by
  have := D.isFinite

  let q : D.I.subscheme ⟶ T := D.I.subschemeι ≫ pullback.snd f g
  have hfib : (q ⁻¹' {t}).Finite := q.finite_preimage_singleton t

  let F : Finset 𝒞 := (hfib.image fun z => pullback.fst f g (D.I.subschemeι z)).toFinset
  have hF : ∀ x ∈ F, f x = g t := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (Set.Finite.mem_toFinset _).mp hx
    have hzt : q z = t := hz
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg g hzt

  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g t)) isOpen_univ
  obtain ⟨U, hU, hUV, hFU⟩ := hcov ⟨V, hV⟩ F fun x hx => by
    change f x ∈ V
    rw [hF x hx]
    exact htV

  refine ⟨D.supportedInLocus U, ?_, ⟨V, hV⟩, ⟨U, hU⟩, hUV, ?_⟩
  · rw [mem_supportedInLocus_iff]
    intro z hz
    exact hFU _ ((Set.Finite.mem_toFinset _).mpr ⟨z, hz, rfl⟩)
  · exact (supportedIn_pullbackAlong_iff _ _ _ _).mpr (by rw [Scheme.Opens.range_ι])

end AlgebraicGeometry.RelEffCartierDiv

theorem solution
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (V : S.affineOpens) (U : 𝒞.affineOpens)
      (_ : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
      (D.pullbackAlong W.ι rfl).SupportedIn U :=
  AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_of_forall_finset_aux f hcov r D t
end S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
