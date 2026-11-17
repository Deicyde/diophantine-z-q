/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/NormTrace/Pi.lean
Original SHA-256: 3932dd4d9a1d6ee7e2ce70ffc8a71642250fb2bb7a103181d4c773aef464d890
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/NormTrace/Pi.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import ZInQKernel.Contrib.HilbertDifferent.Support.TracePi

noncomputable section

section

namespace TauCeti

open scoped BigOperators

universe u v

variable {K : Type u} [CommRing K]

variable {ι : Type v} [Fintype ι]

open Module

section Norm

variable {L : ι → Type*} [∀ i, Ring (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]

/- The norm of an element of a finite dependent product is the product of its component norms. -/
end Norm

section Trace

variable {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]

/- The trace of an element of a finite dependent product is the sum of its component traces. -/
@[simp]
theorem Algebra.trace_pi (x : ∀ i, L i) :
    Algebra.trace K (∀ i, L i) x = ∑ i, Algebra.trace K (L i) (x i) := by
  rw [Algebra.trace_apply]
  calc
    LinearMap.trace K (∀ i, L i) (Algebra.lmul K (∀ i, L i) x) =
        ∑ i, LinearMap.trace K (L i) (Algebra.lmul K (L i) (x i)) := by
      apply ZInQKernel.Contrib.HilbertDifferent.Support.TracePi.LinearMap.trace_pi_of_apply_eq_dependent
        (f := fun i ↦ Algebra.lmul K (L i) (x i))
      intro y i
      simp [Algebra.lmul]
    _ = ∑ i, Algebra.trace K (L i) (x i) := by
      simp_rw [Algebra.trace_apply]

end Trace

end TauCeti
