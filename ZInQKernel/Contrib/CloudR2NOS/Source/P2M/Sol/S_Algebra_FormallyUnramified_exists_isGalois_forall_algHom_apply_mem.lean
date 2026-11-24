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
  Source file    : P2M/Sol/S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem.lean
  Source sha256  : 3466033d47cbab8df61801c224bcdca1c352125e242bc5501eaf71e8bc18b22d
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

namespace P2MW.S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem
r2nos_namespace_dual

set_option autoImplicit false

universe u

namespace P2mEtaleSplitting
r2nos_namespace_dual

open IntermediateField
r2nos_open_dual "IntermediateField"

section PiFactor

variable (K : Type*) [Field K] {I : Type u} [Finite I] (Ai : I → Type u) [∀ i, Field (Ai i)]
  [∀ i, Algebra K (Ai i)] {Ω : Type*} [Field Ω] [Algebra K Ω]

noncomputable def factorHom [DecidableEq I] (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I)
    (hi : φ (Pi.single i 1) = 1) : Ai i →ₐ[K] Ω where
  toFun a := φ (Pi.single i a)
  map_one' := hi
  map_mul' a b := by rw [← map_mul, ← Pi.single_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' a b := by rw [← map_add, ← Pi.single_add]
  commutes' k := by
    rw [Algebra.algebraMap_eq_smul_one, show (Pi.single i (k • (1 : Ai i)) : Π j, Ai j) =
        k • Pi.single i (1 : Ai i) from Pi.single_smul i k (1 : Ai i), map_smul, hi,
      Algebra.algebraMap_eq_smul_one]

omit [Finite I] in
theorem factorHom_apply [DecidableEq I] (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I)
    (hi : φ (Pi.single i 1) = 1) (a : Ai i) : factorHom K Ai φ i hi a = φ (Pi.single i a) := rfl

theorem exists_eq_comp_evalAlgHom (φ : (Π i, Ai i) →ₐ[K] Ω) :
    ∃ (i : I) (ψ : Ai i →ₐ[K] Ω), ∀ x, φ x = ψ (x i) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype I

  have hsum : ∑ i, φ (Pi.single i (1 : Ai i)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : _))]
    exact map_one φ
  have hex : ∃ i, φ (Pi.single i (1 : Ai i)) ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hi0⟩ := hex
  have hidem : φ (Pi.single i (1 : Ai i)) * φ (Pi.single i (1 : Ai i)) =
      φ (Pi.single i (1 : Ai i)) := by
    rw [← map_mul, ← Pi.single_mul, mul_one]
  have hi : φ (Pi.single i (1 : Ai i)) = 1 := by
    have h := hidem
    rwa [mul_left_eq_self₀, or_iff_left hi0] at h
  refine ⟨i, factorHom K Ai φ i hi, fun x => ?_⟩
  rw [factorHom_apply]
  have hx : x = Pi.single i (x i) + x * (1 - Pi.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, map_sub, map_one, hi, sub_self, mul_zero, add_zero]

end PiFactor

theorem exists_isGalois_forall_algHom_apply_mem
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L := by
  classical
  haveI : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_formallyUnramified_of_field K E
  obtain ⟨I, hI, Ai, hF, hA, iso, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K E).mp inferInstance

  haveI hfin : ∀ i, FiniteDimensional K (Ai i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.proj i).comp iso.toLinearMap)
      ((Function.surjective_eval i).comp iso.surjective)
  let N : I → IntermediateField K Ω := fun i => normalClosure K (Ai i) Ω
  refine ⟨⨆ i, N i, ?_, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_iSup_of_finite
  · haveI : Normal K (⨆ i, N i : IntermediateField K Ω) :=
      IntermediateField.normal_iSup (F := K) (K := Ω) N
    haveI : ∀ i, Algebra.IsSeparable K (N i) := by
      intro i
      rw [← le_separableClosure_iff]
      refine (normalClosure_le_iff).mpr fun ψ => ?_
      rintro _ ⟨a, rfl⟩
      rw [mem_separableClosure_iff]
      change IsSeparable K (ψ a)
      rw [IsSeparable, minpoly.algHom_eq ψ ψ.injective]
      exact Algebra.IsSeparable.isSeparable K a
    haveI : Algebra.IsSeparable K (⨆ i, N i : IntermediateField K Ω) :=
      IntermediateField.isSeparable_iSup K Ω
    exact ⟨⟩
  · intro φ e
    obtain ⟨i, ψ, hψ⟩ := exists_eq_comp_evalAlgHom K Ai (φ.comp iso.symm.toAlgHom)
    have hφ : φ e = ψ (iso e i) := by
      have h := hψ (iso e)
      simpa using h
    rw [hφ]
    have hle : N i ≤ ⨆ j, N j := le_iSup N i
    apply hle
    exact AlgHom.fieldRange_le_normalClosure ψ ⟨iso e i, rfl⟩

end P2mEtaleSplitting

theorem solution
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L :=
  P2mEtaleSplitting.exists_isGalois_forall_algHom_apply_mem K E Ω
end S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
