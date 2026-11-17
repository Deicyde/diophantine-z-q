/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/InertiaDegree.lean
Original SHA-256: 4eeb55db19a6203a6752f245ba9172e09453d6a9eb315bdbc9f0f35929f45ac3
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
TauCeti/NumberTheory/LocalField/InertiaDegree.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.RamificationInertia.Basic
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.IntegerRing
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.RamificationIndex
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

variable (K L) in
/- The residue degree `f(L/K)` of an extension of nonarchimedean local fields with compatible
valuations: the degree of the residue field of `L` over the residue field of `K`. -/
def inertiaDegree : ℕ := Module.finrank 𝓀[K] 𝓀[L]

variable (K L) in
/- The defining formula of `inertiaDegree`: the degree of the residue extension. -/
theorem inertiaDegree_def : inertiaDegree K L = Module.finrank 𝓀[K] 𝓀[L] := (rfl)

/- The residue degree is positive. -/
variable (K L) in
/- **The residue degree is the ideal-theoretic inertia degree** of `𝓂[L]` over `𝒪[K]`. -/
theorem inertiaDegree_eq_inertiaDeg :
    inertiaDegree K L = 𝓂[L].inertiaDeg 𝒪[K] :=
  (Ideal.inertiaDeg_eq_of_isMaximal 𝓂[K] 𝓂[L]).symm

variable (K L) in
/- The maximal ideal of `𝒪[L]` is the unique prime above the maximal ideal of `𝒪[K]`. -/
theorem primesOver_maximalIdeal_eq_singleton : Ideal.primesOver 𝓂[K] 𝒪[L] = {𝓂[L]} :=
  IsLocalRing.primesOver_eq 𝒪[L] (IsDiscreteValuationRing.not_a_field 𝒪[K])

variable (K L) in
/- **The fundamental identity** `e(L/K) · f(L/K) = [L : K]` for an extension of nonarchimedean
local fields with compatible valuations. -/
theorem ramificationIndex_mul_inertiaDegree :
    ramificationIndex K L * inertiaDegree K L = Module.finrank K L := by
  have hs := primesOver_maximalIdeal_eq_singleton K L
  have hmem : 𝓂[L] ∈ Ideal.primesOver 𝓂[K] 𝒪[L] := by rw [hs]; exact Set.mem_singleton _
  -- The sum below is indexed by the primes above `𝓂[K]`, a singleton; any `Fintype` will do.
  let : Fintype ↥(Ideal.primesOver 𝓂[K] 𝒪[L]) := by rw [hs]; infer_instance
  rw [ramificationIndex_eq_ramificationIdx, inertiaDegree_eq_inertiaDeg, ← finrank_integerRing K L,
    ← Ideal.sum_ramification_inertia_eq_finrank 𝓂[K] 𝒪[L]]
  symm
  refine Fintype.sum_eq_single (⟨𝓂[L], hmem⟩ : ↥(Ideal.primesOver 𝓂[K] 𝒪[L])) fun q hq ↦ ?_
  exact absurd (Subtype.ext (by simpa [hs] using q.2)) hq

end TauCeti
