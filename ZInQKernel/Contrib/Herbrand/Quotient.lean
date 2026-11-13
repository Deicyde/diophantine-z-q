/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream file LICENSE.
Authors: The Tau Ceti contributors

CHANGED / PORTED FILE: AI-assisted port with Metamate of
TauCeti/NumberTheory/LocalField/Herbrand/Quotient.lean at
 a6027b1d24fcb935c53bd5b50d11b40991cda418
(SHA256 5a706028202abf199fd146af6cd87a6459a9eb8fb85cee8bc2ced2954c581a67).
The full upstream source was read. Its field automorphisms, valuation rings,
and bundled index-domain function are replaced by the actual ring groups,
normalized DVR valuation, and real interval-integral function of `PkgI6`.
The arithmetic coset identity is supplied by the proved concrete `Coset` module,
not an assumed quotient-filtration property. No finite-residue, topological,
or completeness assumption is introduced. The map/kernel counting lemma is
proved for the actual supplied restriction.
Upstream license: Apache-2.0, https://www.apache.org/licenses/LICENSE-2.0 .
-/

import ZInQKernel.Contrib.Herbrand.Coset
import ZInQKernel.Contrib.Herbrand.Analysis

/-!
# Concrete Serre quotient theorem for the real lower numbering

A largest-index lift in an actual restriction coset satisfies Serre's truncated
count identity. The established arithmetic coset formula and the equality
`|H₀| = e(B/C)` give `φ_{B/C}(i_G(σ)-1) = i_{C/A}(r σ)-1`.
The exact ceiling convention then proves the lower quotient theorem at every
real index at least `-1`. Kernel identification and the real lower subgroup
rule supply its cardinality form, used by the real transitivity proof.

References: J.-P. Serre, *Corps locaux*, Chapter IV, §3, Lemmas 4 and 5.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section IndexCosets

variable (A C B : Type) [CommRing A] [CommRing C] [CommRing B]
  [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]

/-- For a largest-index lift in its actual coset, multiplication by a kernel
automorphism has index equal to the minimum of the two indices. -/
theorem lowerIndex_mul_restrictScalars_of_forall_le (σ : B ≃ₐ[A] B)
    (hσ : ∀ τ : B ≃ₐ[C] B,
      lowerIndex A B (σ * τ.restrictScalars A) ≤ lowerIndex A B σ)
    (τ : B ≃ₐ[C] B) :
    lowerIndex A B (σ * τ.restrictScalars A) =
      min (lowerIndex C B τ) (lowerIndex A B σ) := by
  rw [← lowerIndex_restrictScalars A C B τ]
  set τ' := τ.restrictScalars A
  have h₁ := min_le_lowerIndex_mul A B σ τ'
  have h₂ := min_le_lowerIndex_mul A B σ⁻¹ (σ * τ')
  rw [inv_mul_cancel_left, lowerIndex_inv, min_eq_right (hσ τ)] at h₂
  exact le_antisymm (le_min h₂ (hσ τ)) (by rw [min_comm]; exact h₁)

/-- Finiteness of the actual kernel automorphism group supplies a largest-index
lift in every actual coset. -/
theorem exists_forall_lowerIndex_mul_restrictScalars_le [Finite (B ≃ₐ[C] B)]
    (σ : B ≃ₐ[A] B) :
    ∃ τ₀ : B ≃ₐ[C] B, ∀ τ : B ≃ₐ[C] B,
      lowerIndex A B (σ * τ₀.restrictScalars A * τ.restrictScalars A) ≤
        lowerIndex A B (σ * τ₀.restrictScalars A) := by
  classical
  let : Fintype (B ≃ₐ[C] B) := Fintype.ofFinite _
  obtain ⟨τ₀, -, hτ₀⟩ := Finset.exists_max_image (Finset.univ : Finset (B ≃ₐ[C] B))
    (fun τ => lowerIndex A B (σ * τ.restrictScalars A)) Finset.univ_nonempty
  refine ⟨τ₀, fun τ => ?_⟩
  have := hτ₀ (τ₀ * τ) (Finset.mem_univ _)
  rwa [← AlgEquiv.restrictScalarsHom_apply A (τ₀ * τ), map_mul,
    AlgEquiv.restrictScalarsHom_apply, AlgEquiv.restrictScalarsHom_apply, ← mul_assoc] at this

/-- Membership in the locked real filtration is monotone in the actual index,
including the whole-group case at and below `-1`. -/
theorem mem_lowerRamR_of_lowerIndex_le {σ τ : B ≃ₐ[A] B} {u : ℝ}
    (hle : lowerIndex A B σ ≤ lowerIndex A B τ)
    (hσ : σ ∈ PkgI6.lowerRamR A B u) : τ ∈ PkgI6.lowerRamR A B u := by
  by_cases hu : u ≤ -1
  · simp [PkgI6.lowerRamR, hu]
  · rw [PkgI6.lowerRamR, ite_eq_right hu, mem_lowerRam_iff_le_lowerIndex] at hσ ⊢
    exact hσ.trans hle

end IndexCosets

section FiniteDVRTower

variable (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C]
  [Module.Finite A C] [Module.IsTorsionFree A C]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B]
  [IsGalois (FractionRing C) (FractionRing B)]
  (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
  (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c))

include hr

omit [IsDomain A] [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  [Module.Finite A C] [Module.IsTorsionFree A C] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing C) (FractionRing B)] in
/-- Kernel automorphisms do not change the actual restriction. -/
theorem restriction_mul_restrictScalars (σ : B ≃ₐ[A] B) (τ : B ≃ₐ[C] B) :
    r (σ * τ.restrictScalars A) = r σ := by
  have ht : τ.restrictScalars A ∈ r.ker := by
    rw [restriction_ker_eq_range A C B r hr]
    exact ⟨τ, rfl⟩
  rw [map_mul, (show r (τ.restrictScalars A) = 1 from ht), mul_one]

/-- Serre's concrete quotient index identity in truncated-count form. -/
theorem ramificationIndex_mul_lowerIndex_restriction_eq_sum_card (σ : B ≃ₐ[A] B) {j : ℕ}
    (hj : lowerIndex A B σ = j)
    (hσ : ∀ τ : B ≃ₐ[C] B,
      lowerIndex A B (σ * τ.restrictScalars A) ≤ lowerIndex A B σ) :
    (ramificationIndex C B : ℕ∞) * lowerIndex A C (r σ) =
      ∑ k ∈ Finset.range j, (Nat.card (PkgI6.lowerRam C B k) : ℕ∞) := by
  rw [ramificationIndex_mul_lowerIndex_restriction r hr σ]
  simp_rw [lowerIndex_mul_restrictScalars_of_forall_le A C B σ hσ, hj]
  exact sum_min_lowerIndex C B j

/-- A finite largest-index lift has a finite restriction index; the identity
coset cannot have a finite maximum. -/
theorem lowerIndex_restriction_ne_top (σ : B ≃ₐ[A] B)
    (hj : lowerIndex A B σ ≠ ⊤)
    (hσ : ∀ τ : B ≃ₐ[C] B,
      lowerIndex A B (σ * τ.restrictScalars A) ≤ lowerIndex A B σ) :
    lowerIndex A C (r σ) ≠ ⊤ := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hj
  intro htop
  have hsum := ramificationIndex_mul_lowerIndex_restriction_eq_sum_card A C B r hr σ hj.symm hσ
  have he : (ramificationIndex C B : ℕ∞) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos C B).ne'
  rw [htop, ENat.mul_top he, ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

/-- Serre's exact `i-1` formula for the actual real integral. The case `j=0`
is the `-1` endpoint, not a truncated natural subtraction. -/
theorem herbrandPhi_lowerIndex_sub_one (σ : B ≃ₐ[A] B) {j : ℕ}
    (hj : lowerIndex A B σ = j)
    (hσ : ∀ τ : B ≃ₐ[C] B,
      lowerIndex A B (σ * τ.restrictScalars A) ≤ lowerIndex A B σ) :
    PkgI6.herbrandPhi C B ((j : ℝ) - 1) =
      ((lowerIndex A C (r σ)).toNat : ℝ) - 1 := by
  let : PerfectField (ResidueField C) := Algebra.IsAlgebraic.perfectField (ResidueField A)
  have hsum := ramificationIndex_mul_lowerIndex_restriction_eq_sum_card A C B r hr σ hj hσ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (lowerIndex_restriction_ne_top A C B r hr σ (hj ▸ ENat.natCast_ne_top j) hσ)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj, ← natCard_lowerRam_zero C B] at hsum
  rw [← hn, ENat.toNat_natCast]
  have h0 : (Nat.card (PkgI6.lowerRam C B 0) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rcases j with _ | m
  · simp only [Nat.cast_zero, zero_sub]
    rw [herbrandPhi_of_le_zero C B le_rfl (by norm_num)]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · rw [show ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) by push_cast; ring,
      herbrandPhi_nat C B m, div_eq_iff h0]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m),
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (PkgI6.lowerRam C B 0) : ℝ) * n =
        Nat.card (PkgI6.lowerRam C B 0) +
          ∑ i ∈ Finset.Icc 1 m, (Nat.card (PkgI6.lowerRam C B i) : ℝ) := by
      exact_mod_cast hsum
    linear_combination -hsumR

/-- For a largest-index lift, real lower membership is exactly equivalent to
membership of its restriction at the actual Herbrand index. -/
theorem restriction_mem_lowerRamR_herbrandPhi_iff (σ : B ≃ₐ[A] B)
    (hσ : ∀ τ : B ≃ₐ[C] B,
      lowerIndex A B (σ * τ.restrictScalars A) ≤ lowerIndex A B σ)
    (u : ℝ) :
    r σ ∈ PkgI6.lowerRamR A C (PkgI6.herbrandPhi C B u) ↔
      σ ∈ PkgI6.lowerRamR A B u := by
  rcases eq_or_ne (lowerIndex A B σ) ⊤ with htop | htop
  · rw [lowerIndex_eq_top_iff] at htop
    subst σ
    rw [map_one]
    exact iff_of_true (one_mem _) (one_mem _)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp htop
  rw [mem_lowerRamR_iff_of_lowerIndex_eq A C
      (ENat.natCast_toNat (lowerIndex_restriction_ne_top A C B r hr σ htop hσ)).symm,
    ← herbrandPhi_lowerIndex_sub_one A C B r hr σ hj.symm hσ,
    mem_lowerRamR_iff_of_lowerIndex_eq A B hj.symm]
  exact (strictMono_herbrandPhi C B).le_iff_le

variable [Normal (FractionRing A) (FractionRing C)] [Normal (FractionRing A) (FractionRing B)]

/-- **Concrete lower quotient theorem.** The image of the actual lower group
is the actual quotient-ring lower group at `φ_{B/C}(u)`. -/
theorem lowerRamR_quotient (u : ℝ) (_hu : -1 ≤ u) :
    PkgI6.lowerRamR A C (PkgI6.herbrandPhi C B u) = (PkgI6.lowerRamR A B u).map r := by
  ext σ'
  rw [Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨σ, rfl⟩ := restriction_surjective A C B r hr σ'
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_restrictScalars_le A C B σ
    refine ⟨σ * τ₀.restrictScalars A, ?_, restriction_mul_restrictScalars A C B r hr σ τ₀⟩
    rw [← restriction_mem_lowerRamR_herbrandPhi_iff A C B r hr _ hτ₀,
      restriction_mul_restrictScalars A C B r hr]
    exact h
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_lowerIndex_mul_restrictScalars_le A C B σ
    have hle : lowerIndex A B σ ≤ lowerIndex A B (σ * τ₀.restrictScalars A) := by
      have := hτ₀ τ₀⁻¹
      simpa only [← AlgEquiv.restrictScalarsHom_apply, map_inv, mul_inv_cancel_right] using this
    have hmem : σ * τ₀.restrictScalars A ∈ PkgI6.lowerRamR A B u :=
      mem_lowerRamR_of_lowerIndex_le (A := A) (B := B) hle hσ
    have hres := (restriction_mem_lowerRamR_herbrandPhi_iff A C B r hr _ hτ₀ u).mpr hmem
    simpa only [restriction_mul_restrictScalars A C B r hr] using hres

omit [IsDomain A] [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  [Module.Finite A C] [Module.IsTorsionFree A C] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing C) (FractionRing B)]
  [Normal (FractionRing A) (FractionRing C)] [Normal (FractionRing A) (FractionRing B)] in
/-- The actual subgroup rule identifies the image of `Gal(B/C)_u` with the
kernel of restriction inside `Gal(B/A)_u`. -/
theorem map_restrictScalars_lowerRamR (u : ℝ) :
    (PkgI6.lowerRamR C B u).map (AlgEquiv.restrictScalarsHom A) =
      r.ker ⊓ PkgI6.lowerRamR A B u := by
  rw [lowerRamR_tower A B C, Subgroup.map_comap_eq, ← restriction_ker_eq_range A C B r hr]

/-- The map-times-kernel cardinality identity uses the genuine lower subgroup
and the genuine restriction kernel, not a finite-index proxy. -/
theorem natCard_lowerRamR_herbrandPhi_mul (u : ℝ) (hu : -1 ≤ u) :
    Nat.card (PkgI6.lowerRamR A C (PkgI6.herbrandPhi C B u)) *
        Nat.card (PkgI6.lowerRamR C B u) =
      Nat.card (PkgI6.lowerRamR A B u) := by
  rw [lowerRamR_quotient A C B r hr u hu, ← MonoidHom.domRestrict_range,
    ← Subgroup.card_map_of_injective (K := PkgI6.lowerRamR C B u)
      (show Function.Injective (AlgEquiv.restrictScalarsHom (S := C) A :
          (B ≃ₐ[C] B) →* (B ≃ₐ[A] B)) from
        fun σ τ h => AlgEquiv.ext fun x => congrArg (fun e : B ≃ₐ[A] B => e x) h),
    map_restrictScalars_lowerRamR A C B r hr,
    ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype,
    ← MonoidHom.ker_domRestrict, mul_comm, Subgroup.card_ker_mul_card_range]

end FiniteDVRTower

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.herbrandPhi_lowerIndex_sub_one
#print axioms ZInQ.Contrib.Herbrand.lowerRamR_quotient
#print axioms ZInQ.Contrib.Herbrand.natCard_lowerRamR_herbrandPhi_mul
