/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream file LICENSE.
Authors: The Tau Ceti contributors

CHANGED / PORTED FILE: AI-assisted port with Metamate of
TauCeti/NumberTheory/LocalField/Herbrand/Tower.lean at
 a6027b1d24fcb935c53bd5b50d11b40991cda418
(SHA256 cb7150f1a843647adee47fbd0c618d8fc12169221dafa8492e18787a984b17d9).
The full upstream source was read. The proof is adapted to the actual ring
automorphism groups and `PkgI6` real interval-integral and sInf definitions.
The zero-index cardinality identity comes directly from concrete restriction
and its actual kernel; no separate ramification-index tower assertion is used.
Bundled order-isomorphism and integral-inverse conclusions not needed by T22
are omitted. The all-real upper-quotient theorem and exact closed T22 provider
are added. No finite-residue or nonarchimedean-local-field premise is added.
Upstream license: Apache-2.0, https://www.apache.org/licenses/LICENSE-2.0 .
-/

import ZInQKernel.Contrib.Herbrand.Quotient

/-!
# Real Herbrand transitivity and the full upper quotient theorem

The concrete quotient theorem and the lower subgroup rule give the cardinality
identity at every lower index and at zero. Both sides of real transitivity are
affine on each natural unit interval, and these two count identities identify
the slopes. Induction and the identity on `[-1,0]` prove transitivity on the
entire required half-line. The actual sInf inverse and surjectivity of actual
restriction then prove the upper quotient theorem for every real `v`, including
all indices at and below `-1`.

The closed theorem `t22_holds` has exactly the locked conjunction as its type.
It is not an assembled proof of H or an independent protocol/Astra acceptance.
No target, registry, pin, manuscript, or protected record is changed.

Reference: J.-P. Serre, *Corps locaux*, Chapter IV, §3, Propositions 14 and 15.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section GaloisDVRTower

variable (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C]
  [Module.Finite A C] [Module.IsTorsionFree A C]
  [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B]

/-- Constancy of the actual top lower group on `(a,b]` passes to constancy of
the actual quotient lower group on `(φ_{B/C}(a),φ_{B/C}(b)]`. The intervening
preimage is obtained from the real integral's proved surjectivity. -/
theorem lowerRamR_eq_of_forall_eq_of_herbrandPhi_lt_of_le
    (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c))
    {a b t : ℝ} (ha : -1 ≤ a) (hb : -1 ≤ b)
    (ht₁ : PkgI6.herbrandPhi C B a < t) (ht₂ : t ≤ PkgI6.herbrandPhi C B b)
    (h : ∀ s : ℝ, a < s → s ≤ b → PkgI6.lowerRamR A B s = PkgI6.lowerRamR A B b) :
    PkgI6.lowerRamR A C t = PkgI6.lowerRamR A C (PkgI6.herbrandPhi C B b) := by
  let := IsGalois.tower_top_of_isGalois (FractionRing A) (FractionRing C) (FractionRing B)
  have ht : -1 ≤ t := by
    have hφa := (strictMono_herbrandPhi C B).monotone ha
    rw [herbrandPhi_of_le_zero C B le_rfl (by norm_num)] at hφa
    exact hφa.trans ht₁.le
  obtain ⟨s, hs, hsφ⟩ := exists_herbrandPhi_eq C B ht
  have hs₁ : a < s := (strictMono_herbrandPhi C B).lt_iff_lt.mp (by simpa only [hsφ] using ht₁)
  have hs₂ : s ≤ b := (strictMono_herbrandPhi C B).le_iff_le.mp (by simpa only [hsφ] using ht₂)
  rw [← hsφ, lowerRamR_quotient A C B r hr s hs, lowerRamR_quotient A C B r hr b hb,
    h s hs₁ hs₂]

/-- Equality at the left endpoint of a unit interval propagates through that
interval, using the three proved affine formulas and the actual count identities. -/
private theorem herbrandPhi_tower_of_mem_Icc_of_eq (m : ℕ) {u : ℝ}
    (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1)
    (hm : PkgI6.herbrandPhi A B m = PkgI6.herbrandPhi A C (PkgI6.herbrandPhi C B m)) :
    PkgI6.herbrandPhi A B u = PkgI6.herbrandPhi A C (PkgI6.herbrandPhi C B u) := by
  let := IsGalois.tower_top_of_isGalois (FractionRing A) (FractionRing C) (FractionRing B)
  let r := canonicalRestriction A C B
  have hr := canonicalRestriction_commutes A C B
  have ha : -1 ≤ (m : ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hu : -1 ≤ u := ha.trans h₁
  have hGM : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      PkgI6.lowerRamR A B t = PkgI6.lowerRamR A B u := fun t ht₁ ht₂ => by
    rw [lowerRamR_eq_of_sub_one_lt_of_le A B (i := m + 1)
        (by push_cast; linarith) (by push_cast; linarith),
      lowerRamR_eq_of_sub_one_lt_of_le A B (i := m + 1)
        (by push_cast; linarith) (by push_cast; linarith)]
  have hHM : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      PkgI6.lowerRamR C B t = PkgI6.lowerRamR C B u := fun t ht₁ ht₂ => by
    rw [lowerRamR_eq_of_sub_one_lt_of_le C B (i := m + 1)
        (by push_cast; linarith) (by push_cast; linarith),
      lowerRamR_eq_of_sub_one_lt_of_le C B (i := m + 1)
        (by push_cast; linarith) (by push_cast; linarith)]
  have hMK := herbrandPhi_sub_of_forall_eq A B h₁ hGM
  have hML := herbrandPhi_sub_of_forall_eq C B h₁ hHM
  have hLK := herbrandPhi_sub_of_forall_eq A C
    ((strictMono_herbrandPhi C B).monotone h₁) fun t ht₁ ht₂ =>
      lowerRamR_eq_of_forall_eq_of_herbrandPhi_lt_of_le A C B r hr ha hu ht₁ ht₂ hGM
  have hcard : (Nat.card (PkgI6.lowerRamR A C (PkgI6.herbrandPhi C B u)) : ℝ) *
      Nat.card (PkgI6.lowerRamR C B u) = Nat.card (PkgI6.lowerRamR A B u) := by
    exact_mod_cast natCard_lowerRamR_herbrandPhi_mul A C B r hr u hu
  have hcard₀ : (Nat.card (PkgI6.lowerRamR A C 0) : ℝ) *
      Nat.card (PkgI6.lowerRamR C B 0) = Nat.card (PkgI6.lowerRamR A B 0) := by
    have h := natCard_lowerRamR_herbrandPhi_mul A C B r hr 0 (by norm_num)
    rw [PkgI6.phi_zero] at h
    exact_mod_cast h
  have hslope : (Nat.card (PkgI6.lowerRamR A B u) : ℝ) / Nat.card (PkgI6.lowerRamR A B 0) =
      (Nat.card (PkgI6.lowerRamR C B u) / Nat.card (PkgI6.lowerRamR C B 0)) *
        (Nat.card (PkgI6.lowerRamR A C (PkgI6.herbrandPhi C B u)) /
          Nat.card (PkgI6.lowerRamR A C 0)) := by
    rw [div_mul_div_comm, ← hcard, ← hcard₀,
      mul_comm (Nat.card (PkgI6.lowerRamR C B u) : ℝ),
      mul_comm (Nat.card (PkgI6.lowerRamR C B 0) : ℝ)]
  rw [hslope] at hMK
  rw [hML] at hLK
  linear_combination hMK - hLK + hm

/-- Induction on natural unit intervals, without assuming transitivity on any
interval or passing to a substitute inverse function. -/
private theorem herbrandPhi_tower_of_mem_Icc (m : ℕ) :
    ∀ u : ℝ, (m : ℝ) ≤ u → u ≤ m + 1 →
      PkgI6.herbrandPhi A B u = PkgI6.herbrandPhi A C (PkgI6.herbrandPhi C B u) := by
  induction m with
  | zero =>
    intro u h₁ h₂
    exact herbrandPhi_tower_of_mem_Icc_of_eq A C B 0 h₁ h₂ (by simp [PkgI6.phi_zero])
  | succ m ih =>
    intro u h₁ h₂
    exact herbrandPhi_tower_of_mem_Icc_of_eq A C B (m + 1) h₁ h₂
      (ih ((m + 1 : ℕ) : ℝ) (by push_cast; linarith) (by push_cast; linarith))

/-- **Full real transitivity** on the locked `[-1,∞)` domain. Both fraction
extensions over `A` are Galois; no nonnormal intermediate tower is included. -/
theorem herbrandPhi_tower {u : ℝ} (hu : -1 ≤ u) :
    PkgI6.herbrandPhi A B u = PkgI6.herbrandPhi A C (PkgI6.herbrandPhi C B u) := by
  rcases le_or_gt u 0 with h | h
  · rw [herbrandPhi_of_le_zero C B hu h, herbrandPhi_of_le_zero A C hu h,
      herbrandPhi_of_le_zero A B hu h]
  · exact herbrandPhi_tower_of_mem_Icc A C B ⌊u⌋₊ u (Nat.floor_le h.le)
      (Nat.lt_floor_add_one _).le

/-- **Full upper quotient theorem for every real index.** The range `v ≥ -1`
uses the actual sInf inverse, while `v ≤ -1` uses whole groups and the actual
restriction's proved surjectivity. -/
theorem upperRam_quotient (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) (v : ℝ) :
    PkgI6.upperRam A C v = (PkgI6.upperRam A B v).map r := by
  let := IsGalois.tower_top_of_isGalois (FractionRing A) (FractionRing C) (FractionRing B)
  rcases le_or_gt v (-1) with hv | hv
  · rw [upperRam_of_le_neg_one A C hv, upperRam_of_le_neg_one A B hv,
      Subgroup.map_top_of_surjective r (restriction_surjective A C B r hr)]
  · obtain ⟨u, hu, hφ⟩ := exists_herbrandPhi_eq A B hv.le
    have hφu : -1 ≤ PkgI6.herbrandPhi C B u := by
      have h := (strictMono_herbrandPhi C B).monotone hu
      rwa [herbrandPhi_of_le_zero C B le_rfl (by norm_num)] at h
    rw [← hφ, upperRam_herbrandPhi A B hu, herbrandPhi_tower A C B hu,
      upperRam_herbrandPhi A C hφu]
    exact lowerRamR_quotient A C B r hr u hu

end GaloisDVRTower

/-- Closed discharge of the locked Herbrand quotient leaf. Finiteness of `B`
over `C` is derived from the supplied finite `A`-module structure. -/
theorem herbrandQuotient_holds : PkgI6.HerbrandQuotient := by
  intro A C B
  intros
  rename_i r hr v
  let : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  exact upperRam_quotient A C B r hr v

/-- Closed discharge of the locked full real Herbrand transitivity leaf. -/
theorem herbrandTransitivity_holds : PkgI6.HerbrandTransitivity := by
  intro A C B
  intros
  rename_i u hu
  exact herbrandPhi_tower A C B hu

/-- The exact closed T22 conjunction, with no additional premise or Fact wrapper. -/
theorem t22_holds : PkgI6.HerbrandQuotient ∧ PkgI6.HerbrandTransitivity :=
  ⟨herbrandQuotient_holds, herbrandTransitivity_holds⟩

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.herbrandPhi_tower
#print axioms ZInQ.Contrib.Herbrand.upperRam_quotient
#print axioms ZInQ.Contrib.Herbrand.herbrandQuotient_holds
#print axioms ZInQ.Contrib.Herbrand.herbrandTransitivity_holds
#print axioms ZInQ.Contrib.Herbrand.t22_holds
