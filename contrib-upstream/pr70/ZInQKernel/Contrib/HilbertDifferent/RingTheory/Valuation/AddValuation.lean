/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/Valuation/AddValuation.lean
Original SHA-256: d9493910e151a6470d3da346f626047fa30474cdb166a47c33c0750c76084c55
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
TauCeti/RingTheory/Valuation/AddValuation.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Valuation.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace AddValuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ₀]
  (v : AddValuation R Γ₀)

/- An additive valuation of a finite product is the sum of the valuations of the factors. -/
@[simp]
theorem map_prod {ι : Type*} (s : Finset ι) (f : ι → R) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [v.map_one]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, v.map_mul, ih]

end AddValuation
