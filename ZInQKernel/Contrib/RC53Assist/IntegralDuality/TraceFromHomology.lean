import ZInQKernel.Contrib.RC53Assist.DerivedKummerActual.Actual
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints

/-!
# A cochain trace from a top cohomology isomorphism

A scalar isomorphism on degree-three cohomology gives a linear functional
on degree-three cycles which kills boundaries. Over a compact Hausdorff
principal ideal domain, the already proved saturated-kernel extension
extends that functional to all degree-three cochains, provided the next
term is torsion-free. Boundary annihilation and the cohomology isomorphism
are proved for the extension. No duality assertion is an input.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TraceExtension
open ZInQ.Manuscript.RC.SelmerComplex

variable {R : Type} [CommRing R]

/-- The scalar functional induced on the actual degree-three cycles. -/
def homologyTraceOnKernel (C : GCx R) (e : C.toCC.homology 3 ≃ₗ[R] R) :
    LinearMap.ker (C.d 3 4 rfl) →ₗ[R] R :=
  e.toLinearMap.comp
    ((gcxRawHomologyEquiv C 2 3 4 rfl rfl).symm.toLinearMap.comp
      (Submodule.mkQ ((LinearMap.range (C.d 2 3 rfl)).comap
        (LinearMap.ker (C.d 3 4 rfl)).subtype)))

/-- Trace zero on a cycle is exactly the condition that its class is a boundary. -/
theorem homologyTraceOnKernel_eq_zero_iff (C : GCx R)
    (e : C.toCC.homology 3 ≃ₗ[R] R) (z : LinearMap.ker (C.d 3 4 rfl)) :
    homologyTraceOnKernel C e z = 0 ↔ ∃ y : C.X 2, C.d 2 3 rfl y = z.val := by
  change e ((gcxRawHomologyEquiv C 2 3 4 rfl rfl).symm
    (Submodule.Quotient.mk z)) = 0 ↔ _
  rw [map_eq_zero_iff _ e.injective,
    map_eq_zero_iff _ (gcxRawHomologyEquiv C 2 3 4 rfl rfl).symm.injective,
    Submodule.Quotient.mk_eq_zero]
  rfl

/-- The induced functional on cycles is surjective, including at the scalar one. -/
theorem homologyTraceOnKernel_surjective (C : GCx R)
    (e : C.toCC.homology 3 ≃ₗ[R] R) :
    Function.Surjective (homologyTraceOnKernel C e) := by
  intro a
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
    ((LinearMap.range (C.d 2 3 rfl)).comap (LinearMap.ker (C.d 3 4 rfl)).subtype)
    ((gcxRawHomologyEquiv C 2 3 4 rfl rfl) (e.symm a))
  refine ⟨z, ?_⟩
  change e ((gcxRawHomologyEquiv C 2 3 4 rfl rfl).symm
    (Submodule.Quotient.mk z)) = a
  change Submodule.Quotient.mk z = _ at hz
  rw [hz, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

variable [IsDomain R] [IsPrincipalIdealRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- A functional on top cycles extends without assuming scalar self-injectivity. -/
theorem exists_traceFromHomology (C : GCx R)
    (e : C.toCC.homology 3 ≃ₗ[R] R) [Module.IsTorsionFree R (C.X 4)] :
    ∃ tr : C.X 3 →ₗ[R] R,
      ∀ z : LinearMap.ker (C.d 3 4 rfl), tr z.val = homologyTraceOnKernel C e z :=
  kernel_extension_of_compact_scalar (C.d 3 4 rfl) (homologyTraceOnKernel C e)

/-- One fixed extension of the actual cohomology functional. -/
def traceFromHomology (C : GCx R)
    (e : C.toCC.homology 3 ≃ₗ[R] R) [Module.IsTorsionFree R (C.X 4)] : C.X 3 →ₗ[R] R :=
  (exists_traceFromHomology C e).choose

/-- The fixed extension has the prescribed value on every genuine cycle. -/
theorem traceFromHomology_on_cycles (C : GCx R)
    (e : C.toCC.homology 3 ≃ₗ[R] R) [Module.IsTorsionFree R (C.X 4)]
    (z : LinearMap.ker (C.d 3 4 rfl)) :
    traceFromHomology C e z.val = homologyTraceOnKernel C e z :=
  (exists_traceFromHomology C e).choose_spec z

/-- The extension kills all degree-three boundaries. -/
theorem traceFromHomology_boundary (C : GCx R)
    (e : C.toCC.homology 3 ≃ₗ[R] R) [Module.IsTorsionFree R (C.X 4)]
    (y : C.X 2) : traceFromHomology C e (C.d 2 3 rfl y) = 0 := by
  let z : LinearMap.ker (C.d 3 4 rfl) := ⟨C.d 2 3 rfl y, C.d_d 2 3 4 rfl rfl y⟩
  rw [show C.d 2 3 rfl y = z.val from rfl, traceFromHomology_on_cycles]
  exact (homologyTraceOnKernel_eq_zero_iff C e z).2 ⟨y, rfl⟩

/-- Together with boundary annihilation, the extension induces the scalar cohomology isomorphism. -/
theorem traceFromHomology_inducesIsoH3 (C : GCx R)
    (e : C.toCC.homology 3 ≃ₗ[R] R) [Module.IsTorsionFree R (C.X 4)] :
    InducesIsoH3 (traceFromHomology C e) := by
  constructor
  · intro z hz ht
    have h : homologyTraceOnKernel C e ⟨z, hz⟩ = 0 :=
      (traceFromHomology_on_cycles C e ⟨z, hz⟩).symm.trans ht
    exact (homologyTraceOnKernel_eq_zero_iff C e ⟨z, hz⟩).1 h
  · obtain ⟨z, hz⟩ := homologyTraceOnKernel_surjective C e 1
    exact ⟨z.val, z.property, (traceFromHomology_on_cycles C e z).trans hz⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
