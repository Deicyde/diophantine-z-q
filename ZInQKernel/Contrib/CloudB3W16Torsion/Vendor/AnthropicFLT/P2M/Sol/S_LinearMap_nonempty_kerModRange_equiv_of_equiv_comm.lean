/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

set_option autoImplicit false

universe u v w

namespace LinearMap
export _root_.LinearMap (mem_range range coe_coe ext submoduleMap ker mem_ker)
open LinearMap

section KerModRange

variable {R : Type u} [CommRing R] {C : ℕ → Type v} {C' : ℕ → Type w}
  [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
  (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x))

include he

theorem kerModRange_map_ker (i : ℕ) :
    (LinearMap.ker (d i)).map (e i : C i →ₗ[R] C' i) = LinearMap.ker (d' i) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he, hx, map_zero]
  · intro hy
    refine ⟨(e i).symm y, ?_, by simp⟩
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hy, map_zero]

def kerEquivOfComm (i : ℕ) : LinearMap.ker (d i) ≃ₗ[R] LinearMap.ker (d' i) :=
  ((e i).submoduleMap (LinearMap.ker (d i))).trans (LinearEquiv.ofEq _ _ (kerModRange_map_ker d d' e he i))

theorem kerEquivOfComm_apply (i : ℕ) (x : LinearMap.ker (d i)) :
    ((kerEquivOfComm d d' e he i x : LinearMap.ker (d' i)) : C' i) = e i x := rfl

theorem kerModRange_map_comap (i : ℕ) :
    ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype).map
        (kerEquivOfComm d d' e he (i + 1) : LinearMap.ker (d (i + 1)) →ₗ[R] LinearMap.ker (d' (i + 1)))
      = (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨w, hw⟩, rfl⟩
    refine ⟨e i w, ?_⟩
    rw [kerEquivOfComm_apply, ← he, hw]
  · rintro ⟨w, hw⟩
    refine ⟨(kerEquivOfComm d d' e he (i + 1)).symm y, ⟨(e i).symm w, ?_⟩, by simp⟩
    have h1 : ((kerEquivOfComm d d' e he (i + 1)).symm y : C (i + 1))
        = (e (i + 1)).symm (y : C' (i + 1)) := by
      apply (e (i + 1)).injective
      rw [LinearEquiv.apply_symm_apply, ← kerEquivOfComm_apply d d' e he, LinearEquiv.apply_symm_apply]
    rw [h1]
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hw]

theorem nonempty_kerModRange_equiv_of_equiv_comm' :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) :=
  ⟨⟨kerEquivOfComm d d' e he 0⟩, fun i =>
    ⟨Submodule.Quotient.equiv _ _ (kerEquivOfComm d d' e he (i + 1)) (kerModRange_map_comap d d' e he i)⟩⟩

end KerModRange

end LinearMap

theorem solution
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) :=
  LinearMap.nonempty_kerModRange_equiv_of_equiv_comm' d d' e he
