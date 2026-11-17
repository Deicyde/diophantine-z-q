-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.RingTheory.Ideal.Maps), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.RingTheory.Ideal.Maps

/-!
# Generators and kernels of surjective ring maps

Generators of the image of an ideal lift to generators of the ideal modulo the kernel.
-/

namespace Ideal

/-- Generators of the image of an ideal generate the original ideal together with the kernel. -/
theorem eq_span_sup_ker_of_map_eq_span {R S : Type*} [Ring R] [Ring S] {f : R →+* S}
    (hf : Function.Surjective f) {I : Ideal R} (hI : RingHom.ker f ≤ I) {s : Set R}
    (h : I.map f = span (f '' s)) : I = span s ⊔ RingHom.ker f := by
  rw [← comap_map_of_surjective' f hf (span s), map_span, ← h, comap_map_of_surjective' f hf,
    sup_eq_left.2 hI]

end Ideal
