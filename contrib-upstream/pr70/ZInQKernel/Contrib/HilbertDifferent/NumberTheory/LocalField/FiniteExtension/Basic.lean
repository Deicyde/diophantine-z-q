/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/FiniteExtension/Basic.lean
Original SHA-256: 9462603bf138d6a59033ce87fce57ab109b59a71f13883849296d78651bfa602
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
TauCeti/NumberTheory/LocalField/FiniteExtension/Basic.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Valued.NormedValued
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.NormedField
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.ValuativeRel.Extension
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.RootMonic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (M : Type*) [Field M] [Algebra K M] [Module.Finite K M]

/- The normed-field structure on a finite extension `M` of a nonarchimedean local field `K`
given by the spectral norm of `M/K` with respect to the normalized absolute value of `K`. -/
@[expose, implicit_reducible]
def finiteExtensionNormedField : NormedField M :=
  letI := normalizedNontriviallyNormedField K
  haveI := normalizedNormedField_completeSpace K
  haveI := normalizedNormedField_isUltrametricDist K
  spectralNorm.normedField K M

/- The topology on a finite extension `M` of a nonarchimedean local field `K` induced by the
norm of `finiteExtensionNormedField K M`. -/
section Uniqueness

variable {K M} {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/- The coefficients of the minimal polynomial over `K` of an element of `M` of spectral norm at
most `1` lie in `𝒪[K]`. -/
private theorem coeff_minpoly_mem_integer_of_finiteExtensionNormedField_norm_le_one {x : M}
    (hx : letI := finiteExtensionNormedField K M; ‖x‖ ≤ 1) (n : ℕ) :
    (minpoly K x).coeff n ∈ 𝒪[K] := by
  let _ := normalizedNontriviallyNormedField K
  have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : ‖(minpoly K x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hmon).1 hx n
  exact (mem_integer_iff_normalizedAbsoluteValue_le_one _).2
    (by exact_mod_cast (normalizedNormedField_norm_def ((minpoly K x).coeff n)).symm.trans_le h)

/- If a valuation `w` on `M` restricts to the valuation class of `K`, every element of `M` of
spectral norm at most `1` has `w`-valuation at most `1`: the coefficients of its minimal
polynomial over `K` are integral, so it is integral over the valuation ring of `w`. -/
private theorem valuation_le_one_of_finiteExtensionNormedField_norm_le_one {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) {x : M}
    (hx : letI := finiteExtensionNormedField K M; ‖x‖ ≤ 1) : w x ≤ 1 := by
  have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hcoeff (n : ℕ) : w (algebraMap K M ((minpoly K x).coeff n)) ≤ 1 := by
    simpa using hw.le_one_iff_le_one.2
      (coeff_minpoly_mem_integer_of_finiteExtensionNormedField_norm_le_one hx n)
  refine w.le_one_of_root_monic (hmon.map (algebraMap K M)) (fun n _ => ?_) ?_
  · simpa using hcoeff n
  · rw [Polynomial.eval_map_algebraMap, minpoly.aeval]

/- If a valuation `w` on `M` restricts to the valuation class of `K`, every element of `M` of
spectral norm less than `1` has `w`-valuation less than `1`. -/
private theorem valuation_lt_one_of_finiteExtensionNormedField_norm_lt_one {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) {x : M}
    (hx : letI := finiteExtensionNormedField K M; ‖x‖ < 1) : w x < 1 := by
  let _ := finiteExtensionNormedField K M
  -- Compare a power of `x` with an element `y` of `K` with `0 < ‖y‖ < 1`.
  obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hy0' : algebraMap K M y ≠ 0 := by simpa using hy0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hy0') hx
  have h : w (x ^ k / algebraMap K M y) ≤ 1 := by
    refine valuation_le_one_of_finiteExtensionNormedField_norm_le_one hw ?_
    rw [norm_div, norm_pow, div_le_one₀ (norm_pos_iff.2 hy0')]
    exact hk.le
  have hwy : w (algebraMap K M y) < 1 := by simpa using hw.lt_one_iff_lt_one.2 hy1
  have hwy0 : w (algebraMap K M y) ≠ 0 := by simpa using hy0'
  rw [map_div₀, map_pow, div_le_one₀ (zero_lt_iff.2 hwy0)] at h
  by_contra hx1
  exact ((one_le_pow₀ (not_lt.1 hx1)).trans h).not_gt hwy

/- A valuation `w` on a finite extension `M` of a nonarchimedean local field `K` which restricts
to the valuation class of `K` has the closed unit ball of the spectral norm of `M/K` as its
valuation ring. -/
theorem finiteExtensionNormedField_norm_le_one_iff {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) (x : M) :
    letI := finiteExtensionNormedField K M
    ‖x‖ ≤ 1 ↔ w x ≤ 1 := by
  let _ := finiteExtensionNormedField K M
  refine ⟨valuation_le_one_of_finiteExtensionNormedField_norm_le_one hw, fun h => ?_⟩
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h' := valuation_lt_one_of_finiteExtensionNormedField_norm_lt_one hw (x := x⁻¹)
    (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (not_le.1 hx))
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 (by simpa using hx0))] at h'
  exact h'.not_ge h

/- A valuation `w` on a finite extension `M` of a nonarchimedean local field `K` which restricts
to the valuation class of `K` induces the same order on `M` as the spectral norm of `M/K`. -/
theorem finiteExtensionNormedField_norm_le_norm_iff {w : Valuation M Γ}
    (hw : (w.comap (algebraMap K M)).IsEquiv (valuation K)) (x y : M) :
    letI := finiteExtensionNormedField K M
    ‖x‖ ≤ ‖y‖ ↔ w x ≤ w y := by
  let _ := finiteExtensionNormedField K M
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hwy : w y ≠ 0 := by simpa using hy
  have h := finiteExtensionNormedField_norm_le_one_iff hw (x / y)
  rwa [norm_div, div_le_one₀ (norm_pos_iff.2 hy), map_div₀, div_le_one₀ (zero_lt_iff.2 hwy)] at h

/- **Uniqueness of the extended valuation.** Any two valuations on a finite extension `M` of a
nonarchimedean local field `K` which restrict to the valuation class of `K` are equivalent. -/
@[simp]
theorem _root_.AlgEquiv.valuation_eq [ValuativeRel M] [ValuativeExtension K M] (σ : M ≃ₐ[K] M)
    (x : M) : valuation M (σ x) = valuation M x := by
  let _ := finiteExtensionNormedField K M
  let _ := normalizedNontriviallyNormedField K
  have hw := ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K)
  -- The spectral norm is invariant under `K`-algebra automorphisms.
  have h : ‖σ x‖ = ‖x‖ := (spectralNorm_eq_of_equiv σ x).symm
  exact le_antisymm ((finiteExtensionNormedField_norm_le_norm_iff hw _ _).1 h.le)
    ((finiteExtensionNormedField_norm_le_norm_iff hw _ _).1 h.ge)

/- **Embeddings respect the extended valuations.** A `K`-algebra map `ι : M →ₐ[K] N` from a
finite extension `M` of a nonarchimedean local field `K` to a field `N`, for valuative relations
on `M` and on `N` both extending that of `K`, makes `N` a valuative extension of `M` through
`ι.toAlgebra`. -/
end Uniqueness

/-! ### The ring of integers is the integral closure -/

section IntegralClosure

variable {K M} [ValuativeRel M] [ValuativeExtension K M]

/- **The integers of a finite extension are the integral elements.** Let `M` be a finite
extension of a nonarchimedean local field `K`, with a valuative relation extending that of `K`,
and let `O` be any ring of integers of `K`, that is, `(valuation K).Integers O`. An element of
`M` is integral over `O` exactly when its valuation is at most `1`; see Neukirch, Chapter II,
§4 and §6. -/
theorem _root_.Valuation.Integers.isIntegral_iff_valuation_le_one {O : Type*} [CommRing O]
    [Algebra O K] [Algebra O M] [IsScalarTower O K M] (hO : (valuation K).Integers O) (x : M) :
    IsIntegral O x ↔ valuation M x ≤ 1 := by
  have hw := ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K)
  constructor
  · -- A root of a monic polynomial with coefficients of valuation at most `1` has valuation at
    -- most `1`.
    rintro ⟨p, hp, hpx⟩
    refine (valuation M).le_one_of_root_monic (hp.map (algebraMap O M)) (fun n _ => ?_) ?_
    · rw [Polynomial.coeff_map, IsScalarTower.algebraMap_apply O K M]
      exact hw.le_one_iff_le_one.2 (hO.map_le_one _)
    · rwa [Polynomial.eval_map]
  · -- The minimal polynomial over `K` has coefficients in `𝒪[K]`, so it lifts to a monic
    -- polynomial over `O`.
    intro hx
    let _ := finiteExtensionNormedField K M
    have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
    have hlifts : minpoly K x ∈ Polynomial.lifts (algebraMap O K) :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun n => hO.exists_of_le_one
        (coeff_minpoly_mem_integer_of_finiteExtensionNormedField_norm_le_one
          ((finiteExtensionNormedField_norm_le_one_iff hw x).2 hx) n)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmon
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]

variable (K M) in
/- The ring of integers `𝒪[M]` of a finite extension `M` of a nonarchimedean local field `K`,
for a valuative relation extending that of `K`, is the integral closure of `𝒪[K]` in `M`. -/
theorem integerRing_eq_integralClosure :
    𝒪[M] = (integralClosure 𝒪[K] M).toSubring := by
  ext x
  rw [Subalgebra.mem_toSubring, mem_integralClosure_iff,
    Valuation.Integers.isIntegral_iff_valuation_le_one
      (Valuation.integer.integers (valuation K)),
    Valuation.mem_integer_iff]

end IntegralClosure

section IntegerRingEquiv

variable {K M} [ValuativeRel M] [ValuativeExtension K M]
variable {L : Type*} [Field L] [ValuativeRel L] [Algebra K L]
  [ValuativeExtension K L] [Module.Finite K L]

variable (K M) in
/- The ring of integers `𝒪[M]` of a finite extension `M` of a nonarchimedean local field `K`,
as an `𝒪[K]`-algebra, is the integral closure of `𝒪[K]` in `M`; this is the equivalence given by
`integerRing_eq_integralClosure`. -/
def integerRingEquivIntegralClosure : 𝒪[M] ≃ₐ[𝒪[K]] integralClosure 𝒪[K] M :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (integerRing_eq_integralClosure K M))
    fun _ ↦ Subtype.ext (RingEquiv.coe_subringCongr_apply _ _)

/- The equivalence `integerRingEquivIntegralClosure` does not change the underlying element. -/
@[simp]
theorem coe_integerRingEquivIntegralClosure_apply (x : 𝒪[M]) :
    (integerRingEquivIntegralClosure K M x : M) = x := by
  rw [integerRingEquivIntegralClosure, AlgEquiv.ofRingEquiv_apply]
  exact RingEquiv.coe_subringCongr_apply _ _

/- The inverse of `integerRingEquivIntegralClosure` does not change the underlying element. -/
@[simp]
theorem coe_integerRingEquivIntegralClosure_symm_apply (x : integralClosure 𝒪[K] M) :
    ((integerRingEquivIntegralClosure K M).symm x : M) = x := by
  conv_rhs => rw [← (integerRingEquivIntegralClosure K M).apply_symm_apply x]
  exact (coe_integerRingEquivIntegralClosure_apply _).symm

/- A base-field algebra equivalence restricts to an algebra equivalence of integer rings. -/
def _root_.AlgEquiv.integerRingEquiv (e : L ≃ₐ[K] M) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[M] :=
  ((integerRingEquivIntegralClosure K L).trans (e.restrictScalars 𝒪[K]).mapIntegralClosure).trans
    (integerRingEquivIntegralClosure K M).symm

/- The integer-ring equivalence acts by the original field equivalence. -/
@[simp]
theorem _root_.AlgEquiv.coe_integerRingEquiv_apply (e : L ≃ₐ[K] M) (x : 𝒪[L]) :
    (e.integerRingEquiv x : M) = e (x : L) := by
  simp [AlgEquiv.integerRingEquiv]

/- A base-field algebra map restricts to an algebra map of integer rings. -/
end IntegerRingEquiv

end TauCeti
