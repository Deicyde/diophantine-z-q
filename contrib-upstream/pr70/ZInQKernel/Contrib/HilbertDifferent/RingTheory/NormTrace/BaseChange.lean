/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/NormTrace/BaseChange.lean
Original SHA-256: ba9d46c23ccd79334321b79a298a7d5f2ff580e9f3e3cca4ff1465b47193441d
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
TauCeti/RingTheory/NormTrace/BaseChange.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace TauCeti

universe u

variable {K : Type u} [CommRing K]
variable {A B : Type*} [CommRing A] [Algebra K A]

section Norm

variable [Ring B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/- Norm commutes with scalar extension on a pure tensor. -/
end Norm

section Trace

variable [CommRing B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/- Trace commutes with scalar extension on a pure tensor. -/
@[simp]
theorem Algebra.trace_baseChange_tmul (x : B) :
    Algebra.trace A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K B x) := by
  rw [Algebra.trace_apply]
  calc
    LinearMap.trace A (TensorProduct K A B)
        (Algebra.lmul A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x)) =
        LinearMap.trace A (TensorProduct K A B) ((Algebra.lmul K B x).baseChange A) := by
          rw [Algebra.baseChange_lmul]
    _ = algebraMap K A (LinearMap.trace K B (Algebra.lmul K B x)) :=
      LinearMap.trace_baseChange (R := K) (M := B) (f := Algebra.lmul K B x) (A := A)
    _ = algebraMap K A (Algebra.trace K B x) := by
      rw [Algebra.trace_apply]

end Trace

end TauCeti
