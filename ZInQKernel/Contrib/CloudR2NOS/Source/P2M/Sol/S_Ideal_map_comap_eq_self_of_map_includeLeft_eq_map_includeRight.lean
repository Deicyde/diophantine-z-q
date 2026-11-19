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
  Source file    : P2M/Sol/S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight.lean
  Source sha256  : 391d791e3b8f8ccae6c067fb8c450b22b0b4f85b992423dcdff665d544b360c4
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
r2nos_namespace_dual

set_option autoImplicit false

universe u

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace Ideal
r2nos_namespace_dual
w03_export "Ideal" "map_le_iff_le_comap map_map Quotient.eq_zero_iff_mem Quotient.mkₐ comap_map_eq_self_of_faithfullyFlat Quotient.mk map_id map quotientMap_injective' ext map_comap_le quotientMapₐ mem_map_of_mem mem_comap map_mono comap Quotient.mkₐ_eq_mk"
w03_open "Ideal"

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

def DescentCondition (I : Ideal B) : Prop :=
  I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
    I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)

theorem map_comap_eq_self_of_descentCondition_of_section (σ : B →ₐ[A] A) (I : Ideal B)
    (hI : DescentCondition (A := A) I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  refine le_antisymm Ideal.map_comap_le ?_

  let θ : B ⊗[A] B →ₐ[A] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId A B).comp σ) (AlgHom.id A B) fun _ _ => Commute.all _ _
  have hθL : (θ : B ⊗[A] B →+* B).comp
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      (algebraMap A B).comp (σ : B →+* A) := by
    ext b
    simp [θ, Algebra.TensorProduct.includeLeftRingHom]
  have hθR : (θ : B ⊗[A] B →+* B).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) = RingHom.id B := by
    ext b
    simp [θ]

  have h2 : I.map (σ : B →+* A) ≤ I.comap (algebraMap A B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    change algebraMap A B (σ i) ∈ I
    have hmem : Algebra.TensorProduct.includeLeftRingHom i ∈
        I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) := by
      rw [← show I.map _ = _ from hI]
      exact Ideal.mem_map_of_mem _ hi
    have := Ideal.mem_map_of_mem (θ : B ⊗[A] B →+* B) hmem
    rw [Ideal.map_map, hθR, Ideal.map_id] at this
    convert this using 1
    exact (RingHom.congr_fun hθL i).symm

  have h1 : I ≤ (I.map (σ : B →+* A)).map (algebraMap A B) := by
    intro i hi
    have hmem : ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) i ∈
        I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) := by
      rw [show I.map _ = _ from hI]
      exact Ideal.mem_map_of_mem _ hi
    have := Ideal.mem_map_of_mem (θ : B ⊗[A] B →+* B) hmem
    rw [Ideal.map_map, hθL, ← Ideal.map_map] at this
    convert this using 1
    exact (RingHom.congr_fun hθR i).symm
  exact h1.trans (Ideal.map_mono h2)

end Ideal

namespace Ideal
r2nos_namespace_dual
w03_export "Ideal" "map_le_iff_le_comap map_map Quotient.eq_zero_iff_mem Quotient.mkₐ comap_map_eq_self_of_faithfullyFlat Quotient.mk map_id map quotientMap_injective' ext map_comap_le quotientMapₐ mem_map_of_mem mem_comap map_mono comap Quotient.mkₐ_eq_mk"
w03_open "Ideal"

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

theorem descentCondition_map (I₀ : Ideal A) : DescentCondition (A := A) (I₀.map (algebraMap A B)) := by
  unfold DescentCondition
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_one_eq_one_tmul]

theorem comap_includeLeft_map_includeRight [Module.Flat A B] (I : Ideal B) :
    (I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)).comap
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      (I.comap (algebraMap A B)).map (algebraMap A B) := by
  set I₀ := I.comap (algebraMap A B) with hI₀
  refine le_antisymm ?_ ?_
  · intro b hb
    rw [Ideal.mem_comap] at hb

    let g : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⧸ I) :=
      Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A I)
    have hker : I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) ≤
        RingHom.ker (g : B ⊗[A] B →+* B ⊗[A] (B ⧸ I)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change g ((1 : B) ⊗ₜ[A] i) = 0
      rw [show g ((1 : B) ⊗ₜ[A] i) = (AlgHom.id A B 1) ⊗ₜ[A] (Ideal.Quotient.mkₐ A I i) from
        Algebra.TensorProduct.map_tmul _ _ _ _, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hi, TensorProduct.tmul_zero]
    have hb0 : b ⊗ₜ[A] (1 : B ⧸ I) = 0 := by
      have := hker hb
      simpa [g, Algebra.TensorProduct.includeLeftRingHom] using this

    have hH : I₀ ≤ I.comap (Algebra.ofId A B : A →+* B) := le_of_eq hI₀
    let ι : (A ⧸ I₀) →ₐ[A] (B ⧸ I) := Ideal.quotientMapₐ I (Algebra.ofId A B) hH
    have hι : Function.Injective ι.toLinearMap :=
      Ideal.quotientMap_injective' (I := I) (f := (Algebra.ofId A B : A →+* B)) (H := hH)
        (le_of_eq hI₀.symm)
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := B) ι.toLinearMap hι
    have h1 : (LinearMap.lTensor B ι.toLinearMap) (b ⊗ₜ[A] (1 : A ⧸ I₀)) = 0 := by
      rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one, hb0]
    have h2 : b ⊗ₜ[A] (1 : A ⧸ I₀) = 0 := hinj (by rw [h1, map_zero])

    have h3 : (Ideal.Quotient.mk (I₀.map (algebraMap A B)) b) = 0 := by
      apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).injective
      rw [map_zero, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, h2]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap] at ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : Algebra.TensorProduct.includeLeftRingHom (algebraMap A B a) =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) (algebraMap A B a) := by
      simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [this]
    exact Ideal.mem_map_of_mem _ ha

theorem map_comap_eq_self_of_descentCondition [Module.FaithfullyFlat A B] (I : Ideal B)
    (hI : DescentCondition (A := A) I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by

  set iL : B →+* B ⊗[A] B := Algebra.TensorProduct.includeLeftRingHom with hiL
  set iR : B →+* B ⊗[A] B :=
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B) with hiR
  have hI' : I.map iL = I.map iR := hI

  let jL : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B) := Algebra.TensorProduct.includeLeftRingHom
  let jR : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)) : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B))

  let χ₁ : B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeLeft : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let χ₂ : B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    ((Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[B] (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let χ : B ⊗[A] B →ₐ[A] (B ⊗[A] B) ⊗[B] (B ⊗[A] B) :=
    Algebra.TensorProduct.lift χ₁ χ₂ fun x y => Commute.all (χ₁ x) (χ₂ y)
  have hχL : (χ : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).comp iL = jL.comp iR := by
    ext b
    simp [χ, χ₁, χ₂, iL, iR, jL, Algebra.TensorProduct.includeLeftRingHom]
    rfl
  have hχR : (χ : B ⊗[A] B →+* (B ⊗[A] B) ⊗[B] (B ⊗[A] B)).comp iR = jR.comp iR := by
    ext b
    simp [χ, χ₁, χ₂, iR, jR]
    rfl
  have hDC : DescentCondition (A := B) (I.map iR) := by
    change (I.map iR).map jL = (I.map iR).map jR
    rw [Ideal.map_map, Ideal.map_map, ← hχL, ← hχR, ← Ideal.map_map, ← Ideal.map_map, hI']

  have hsplit := map_comap_eq_self_of_descentCondition_of_section
    (Algebra.TensorProduct.lmul'' A (S := B)) (I.map iR) hDC

  have halg : algebraMap B (B ⊗[A] B) = iL := rfl
  rw [halg, comap_includeLeft_map_includeRight] at hsplit

  rw [← hI'] at hsplit
  have := congrArg (fun J => J.comap iL) hsplit
  rwa [← halg, Ideal.comap_map_eq_self_of_faithfullyFlat,
    Ideal.comap_map_eq_self_of_faithfullyFlat] at this

end Ideal

theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (I : Ideal B)
    (hI : I.map (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) =
      I.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B)) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I :=
  Ideal.map_comap_eq_self_of_descentCondition I hI
end S_Ideal_map_comap_eq_self_of_map_includeLeft_eq_map_includeRight
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
