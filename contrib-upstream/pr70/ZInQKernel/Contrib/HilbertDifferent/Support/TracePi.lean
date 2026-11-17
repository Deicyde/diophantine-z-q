/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/FiniteGroups/CliffordDecomposition.lean
Original SHA-256: 612b34ed0c07569332ffc25016151160e5ca607baac47f13bbe7d9b78523fa72
Changes: contribution import paths and namespace; retained proof content.
Only the dependent-product trace lemma is selected from the original module.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0. Authors: The Tau Ceti contributors.
Selected dependent-product trace lemma; no character theory is imported.
Full license and inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
variable {k : Type*} {ι : Type*} [CommRing k] [Fintype ι]
open scoped Classical in
theorem _root_.ZInQKernel.Contrib.HilbertDifferent.Support.TracePi.LinearMap.trace_pi_of_apply_eq_dependent {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Module.Free k (M i)]
    [∀ i, Module.Finite k (M i)]
    (T : ((i : ι) → M i) →ₗ[k] ((i : ι) → M i)) (f : ∀ i, M i →ₗ[k] M i)
    (hT : ∀ x i, T x i = f i (x i)) :
    LinearMap.trace k ((i : ι) → M i) T = ∑ i, LinearMap.trace k (M i) (f i) := by
  let b (i : ι) := Module.Free.chooseBasis k (M i)
  let _ (i : ι) : Fintype (Module.Free.ChooseBasisIndex k (M i)) := Fintype.ofFinite _
  let B : Module.Basis (Σ i, Module.Free.ChooseBasisIndex k (M i)) k ((i : ι) → M i) :=
    Pi.basis b
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_eq_matrix_trace k (b i), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.toMatrix_apply, B, b, hT]
