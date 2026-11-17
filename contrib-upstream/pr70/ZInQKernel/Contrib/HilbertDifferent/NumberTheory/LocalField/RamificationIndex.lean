/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/RamificationIndex.lean
Original SHA-256: 645927cb247f7c0682e41d0e7a5685af6eda42d712752df1f97d7f0ec88ba984
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
TauCeti/NumberTheory/LocalField/RamificationIndex.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RamificationInertia.Basic
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.NormalizedValuation
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.ValuativeRel.Extension
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

set_option maxHeartbeats 800000

noncomputable section

section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]

variable (K L) in
/- The ramification index `e(L/K)` of an extension of nonarchimedean local fields: the index in
`Multiplicative ℤ` of the image of `Kˣ` under the normalized valuation of `L`. For a compatible
extension this image is the subgroup of multiples of `e`, and `e` is characterized by
`normalizedValuation_algebraMap`. -/
def ramificationIndex : ℕ :=
  ((normalizedValuation L).comp (Units.map (algebraMap K L : K →* L))).range.index

private theorem natCast_ramificationIndex_eq {m : ℤ} (hm : 0 ≤ m)
    (h : (normalizedValuation L).comp (Units.map (algebraMap K L : K →* L)) =
        (zpowGroupHom m).comp (normalizedValuation K)) :
    (ramificationIndex K L : ℤ) = m := by
  have hrange : ((normalizedValuation L).comp (Units.map (algebraMap K L : K →* L))).range =
      Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ) ^ m) := by
    rw [h, MonoidHom.range_comp, MonoidHom.range_eq_top.2 normalizedValuation_surjective]
    ext y
    simp only [Subgroup.map_top, MonoidHom.mem_range, zpowGroupHom_apply,
      Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x.toAdd, ?_⟩
      rw [← zpow_mul, mul_comm, zpow_mul]
      congr 1
      apply Multiplicative.toAdd.injective
      simp
    · rintro ⟨k, rfl⟩
      exact ⟨Multiplicative.ofAdd (1 : ℤ) ^ k, by rw [← zpow_mul, mul_comm, zpow_mul]⟩
  rw [ramificationIndex, hrange, Subgroup.index_zpowers_zpow]
  · rw [orderOf_ofAdd_eq_addOrderOf,
      addOrderOf_eq_zero (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)]
    simp [hm]
  · refine eq_top_iff.2 fun y _ ↦ Subgroup.mem_zpowers_iff.2 ⟨y.toAdd, ?_⟩
    apply Multiplicative.toAdd.injective
    simp

section Tame

variable (K L)

/- An extension of nonarchimedean local fields is **tamely ramified** when the residue
characteristic does not divide its ramification index. For a general valued field tameness also
asks for a separable residue extension; that condition is automatic here, the residue fields of
nonarchimedean local fields being finite. -/
end Tame

variable [ValuativeExtension K L]

/- The normalized valuation of `L` vanishes on the image of `x : Kˣ` exactly when the normalized
valuation of `K` vanishes on `x`: the algebra map of a compatible extension carries the units of
`𝒪[K]`, and only those, to units of `𝒪[L]`. -/
theorem normalizedValuation_algebraMap_eq_one_iff (x : Kˣ) :
    normalizedValuation L (Units.map (algebraMap K L : K →* L) x) = 1 ↔
      normalizedValuation K x = 1 := by
  rw [normalizedValuation_eq_one_iff, normalizedValuation_eq_one_iff, Units.coe_map,
    MonoidHom.coe_ofClass, ← ValuativeExtension.mapValueGroupWithZero_valuation,
    ← map_one (ValuativeExtension.mapValueGroupWithZero K L)]
  exact ValuativeExtension.mapValueGroupWithZero_strictMono.injective.eq_iff

/- The normalized valuation of `L` restricted to `Kˣ` is a positive power of that of `K`. The
exponent is the value in `L` of a chosen uniformizer of `K`. -/
private theorem exists_normalizedValuation_algebraMap_eq_zpow :
    ∃ m : ℤ, 0 < m ∧ (normalizedValuation L).comp (Units.map (algebraMap K L : K →* L)) =
      (zpowGroupHom m).comp (normalizedValuation K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set πu : Kˣ := Units.mk0 (π : K) (fun h ↦ hπ.ne_zero (Subtype.ext h))
  set φ := (normalizedValuation L).comp (Units.map (algebraMap K L : K →* L))
  refine ⟨(φ πu).toAdd, lt_of_le_of_ne ?_ ?_, ?_⟩
  · -- `π` is integral in `K`, so its image is integral in `L`.
    have hmem : ((Units.map (algebraMap K L : K →* L) πu : Lˣ) : L) ∈ 𝒪[L] := by
      rw [Valuation.mem_integer_iff, Units.coe_map, MonoidHom.coe_ofClass,
        ← ValuativeExtension.mapValueGroupWithZero_valuation,
        ← map_one (ValuativeExtension.mapValueGroupWithZero K L),
        ValuativeExtension.mapValueGroupWithZero_strictMono.le_iff_le]
      exact π.2
    change 0 ≤ (normalizedValuation L
      (Units.map (algebraMap K L : K →* L) πu)).toAdd
    exact (mem_integer_iff_toAdd_normalizedValuation_nonneg
      (K := L) (Units.map (algebraMap K L : K →* L) πu)).1 hmem
  · -- `π` is not a unit of `𝒪[K]`, so its image is not a unit of `𝒪[L]`.
    intro h
    have h1 : φ πu = 1 := by
      rw [← toAdd_eq_zero]
      exact h.symm
    change normalizedValuation L (Units.map (algebraMap K L : K →* L) πu) = 1 at h1
    have := (normalizedValuation_algebraMap_eq_one_iff (K := K) (L := L) πu).1 h1
    rw [normalizedValuation_irreducible hπ] at this
    exact absurd this (by decide)
  · -- Write `x = u * π ^ n` with `u` a unit of `𝒪[K]`; both sides are then computed at `π`.
    refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨u, n, hu, rfl⟩ := exists_eq_mul_zpow_of_irreducible hπ x
    have hu' : φ u = 1 := (normalizedValuation_algebraMap_eq_one_iff (K := K) (L := L) u).2
      ((normalizedValuation_eq_one_iff (K := K) u).2 hu)
    simp only [MonoidHom.comp_apply, zpowGroupHom_apply] at hu' ⊢
    rw [map_mul, map_mul, map_zpow, map_zpow, hu', (normalizedValuation_eq_one_iff u).2 hu,
      normalizedValuation_irreducible hπ, one_mul]
    apply Multiplicative.toAdd.injective
    simpa using mul_comm _ _

/- The ramification index is positive. -/
theorem ramificationIndex_pos : 0 < ramificationIndex K L := by
  obtain ⟨m, hm, h⟩ := exists_normalizedValuation_algebraMap_eq_zpow (K := K) (L := L)
  have := natCast_ramificationIndex_eq hm.le h
  omega

/- **The characteristic property of the ramification index**: the normalized valuation of `L`
restricted to `Kˣ` is the `e`-th power of the normalized valuation of `K`, that is
`v_L(x) = e · v_K(x)`. -/
@[simp]
theorem normalizedValuation_algebraMap (x : Kˣ) :
    normalizedValuation L (Units.map (algebraMap K L : K →* L) x) =
      normalizedValuation K x ^ ramificationIndex K L := by
  obtain ⟨m, hm, h⟩ := exists_normalizedValuation_algebraMap_eq_zpow (K := K) (L := L)
  have he := natCast_ramificationIndex_eq hm.le h
  rw [← zpow_natCast, he]
  exact DFunLike.congr_fun h x

/- The characteristic property of the ramification index in additive form:
`v_L(x) = e · v_K(x)` for `x : Kˣ`. -/
theorem toAdd_normalizedValuation_algebraMap (x : Kˣ) :
    (normalizedValuation L (Units.map (algebraMap K L : K →* L) x)).toAdd =
      ramificationIndex K L * (normalizedValuation K x).toAdd := by
  rw [normalizedValuation_algebraMap, toAdd_pow, nsmul_eq_mul]

/- The characteristic property of the ramification index for the zero-preserving normalized
valuations, on all of `K`. -/
theorem ramificationIndex_eq_iff {n : ℕ} :
    ramificationIndex K L = n ↔ ∀ x : Kˣ,
      normalizedValuation L (Units.map (algebraMap K L : K →* L) x) =
        normalizedValuation K x ^ n := by
  refine ⟨fun h x ↦ h ▸ normalizedValuation_algebraMap x, fun h ↦ ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have := (normalizedValuation_algebraMap (L := L)
    (Units.mk0 (π : K) (fun h ↦ hπ.ne_zero (Subtype.ext h)))).symm.trans (h _)
  rw [normalizedValuation_irreducible hπ] at this
  have := congrArg Multiplicative.toAdd this
  simpa using this

/- The image in `L` of any uniformizer of `K` has normalized valuation `e(L/K)`. -/
theorem normalizedValuation_algebraMap_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    normalizedValuation L (Units.map (algebraMap K L : K →* L)
      (Units.mk0 (π : K) (fun h ↦ hπ.ne_zero (Subtype.ext h)))) =
        Multiplicative.ofAdd (ramificationIndex K L : ℤ) := by
  rw [normalizedValuation_algebraMap, normalizedValuation_irreducible hπ]
  apply Multiplicative.toAdd.injective
  simp

/- The valuation in `L` of a uniformizer `π_K` of `K` is the `e(L/K)`-th power of the valuation
of a uniformizer `π_L` of `L`. -/
theorem valuation_algebraMap_irreducible {πK : 𝒪[K]} (hπK : Irreducible πK) {πL : 𝒪[L]}
    (hπL : Irreducible πL) :
    valuation L (algebraMap K L πK) = valuation L (πL : L) ^ ramificationIndex K L := by
  have hK : (πK : K) ≠ 0 := fun h ↦ hπK.ne_zero (Subtype.ext h)
  have hL : (πL : L) ≠ 0 := fun h ↦ hπL.ne_zero (Subtype.ext h)
  apply EquivLike.injective (valueGroupWithZeroIsoInt L)
  have h₁ := valueGroupWithZeroIsoInt_valuation
    (Units.map (algebraMap K L : K →* L) (Units.mk0 (πK : K) hK))
  have h₂ := valueGroupWithZeroIsoInt_valuation (Units.mk0 (πL : L) hL)
  have h₀ := normalizedValuation_algebraMap_irreducible (L := L) hπK
  simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0,
    normalizedValuation_irreducible hπL, toAdd_ofAdd] at h₀ h₁ h₂
  rw [h₀, toAdd_ofAdd] at h₁
  rw [h₁, map_pow, h₂, ← WithZero.exp_nsmul]
  simp

/- The additive valuation on the integer ring scales under the algebra map by the ramification
index. -/
variable (K L) in
/- The maximal ideal of `𝒪[K]` generates the `e(L/K)`-th power of the maximal ideal of `𝒪[L]`.
This is the ideal-theoretic form of the characteristic property of the ramification index. -/
theorem map_maximalIdeal_eq_maximalIdeal_pow :
    𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) = 𝓂[L] ^ ramificationIndex K L := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hv : valuation L ((algebraMap 𝒪[K] 𝒪[L] π : 𝒪[L]) : L) =
      valuation L ((ϖ ^ ramificationIndex K L : 𝒪[L]) : L) := by
    push_cast
    rw [valuation_algebraMap_irreducible hπ hϖ, map_pow]
  have hint := Valuation.integer.integers (valuation L)
  have hass : Associated (algebraMap 𝒪[K] 𝒪[L] π) (ϖ ^ ramificationIndex K L) :=
    associated_of_dvd_dvd (hint.dvd_iff_le.2 hv.ge) (hint.dvd_iff_le.2 hv.le)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  exact hass

variable (K L) in
/- **The intrinsic ramification index is the ideal-theoretic one**: the index of the image of the
normalized value group is the ramification index of `𝓂[L]` over `𝒪[K]`. -/
theorem ramificationIndex_eq_ramificationIdx :
    ramificationIndex K L = 𝓂[L].ramificationIdx 𝒪[K] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx 𝓂[K] 𝓂[L]
    (IsDiscreteValuationRing.not_a_field 𝒪[K])]
  refine (Ideal.ramificationIdx'_spec
    (map_maximalIdeal_eq_maximalIdeal_pow K L).le fun hle ↦ ?_).symm
  rw [map_maximalIdeal_eq_maximalIdeal_pow K L,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton,
    pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at hle
  omega

/- **Multiplicativity of the ramification index in a tower** `M/L/K`:
`e(M/K) = e(L/K) · e(M/L)`. -/
end TauCeti
