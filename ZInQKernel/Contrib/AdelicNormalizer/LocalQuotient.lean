import ZInQKernel.Contrib.AdelicNormalizer.Objects
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Index

/-!
# Local denominator subgroups and all-prime coverage

The local normalizer proofs are reused unchanged from `Local.lean`.  This file
places the scalar-times-order-unit subgroup inside the actual order normalizer,
where normality is valid, and records the exceptional primes exhaustively.
-/

open Quaternion
open scoped Pointwise

namespace G1

noncomputable section

section Local

variable (p : ℕ) [Fact p.Prime]

/-- Local scalar units, as their actual image in quaternion units. -/
def localScalarGroup : Subgroup (Bp p)ˣ := (localScalar p).range

theorem localScalar_comm (c : ℚ_[p]ˣ) (u : (Bp p)ˣ) :
    localScalar p c * u = u * localScalar p c := by
  apply Units.ext
  exact Algebra.commutes (c : ℚ_[p]) (u : Bp p)

instance localScalarGroup_normal : (localScalarGroup p).Normal := by
  apply Subgroup.normal_of_le_center
  rintro _ ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.2 fun u => (localScalar_comm p c u).symm

/-- The local denominator is defined by scalars and actual order units. -/
def localDenom : Subgroup (Bp p)ˣ := localScalarGroup p ⊔ localOrderUnits p

/-- Identifies the subgroup carrier with the previously proved local set. -/
theorem mem_localDenom (x : (Bp p)ˣ) :
    x ∈ localDenom p ↔ x ∈ GlueVigneras.scalOpUnits p := by
  constructor
  · intro hx
    change x ∈ localScalarGroup p ⊔ localOrderUnits p at hx
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx
    rcases hx with ⟨a, ⟨c, rfl⟩, u, hu, rfl⟩
    refine ⟨c, u, hu, ?_⟩
    exact (Algebra.smul_def (c : ℚ_[p]) (u : Bp p)).symm
  · rintro ⟨c, u, hu, hx⟩
    have hxu : x = localScalar p c * u := by
      apply Units.ext
      simpa [localScalar, Algebra.smul_def] using hx
    rw [hxu]
    exact (localDenom p).mul_mem
      ((le_sup_left : localScalarGroup p ≤ localDenom p) ⟨c, rfl⟩)
      ((le_sup_right : localOrderUnits p ≤ localDenom p) hu)

theorem localDenom_le_normalizer : localDenom p ≤ localNormalizer p := by
  apply sup_le
  · rintro _ ⟨c, rfl⟩
    exact localScalar_mem_normalizer p c
  · exact localOrderUnits_le_normalizer p

/-- Order units regarded as a subgroup of the order normalizer. -/
def localH : Subgroup (localNormalizer p) :=
  (localOrderUnits p).subgroupOf (localNormalizer p)

/-- Scalar times order units regarded as a subgroup of the order normalizer. -/
def localS : Subgroup (localNormalizer p) :=
  (localDenom p).subgroupOf (localNormalizer p)

instance localH_normal : (localH p).Normal where
  conj_mem n hn g := by
    change ((g : (Bp p)ˣ) * (n : (Bp p)ˣ) * (g : (Bp p)ˣ)⁻¹) ∈ localOrderUnits p
    change (n : (Bp p)ˣ) ∈ localOrderUnits p at hn
    rcases hn with ⟨hn, hni⟩
    constructor
    · exact (g.property ((n : (Bp p)ˣ) : Bp p)).1 hn
    · have h := (g.property (((n : (Bp p)ˣ)⁻¹ : (Bp p)ˣ) : Bp p)).1 hni
      simpa [mul_inv_rev, mul_assoc] using h

instance localS_normal : (localS p).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (localDenom_le_normalizer p)).2
  have h1 : localNormalizer p ≤ Subgroup.normalizer (localScalarGroup p) :=
    Subgroup.le_normalizer_of_normal
  letI : ((localOrderUnits p).subgroupOf (localNormalizer p)).Normal := localH_normal p
  have h2 : localNormalizer p ≤ Subgroup.normalizer (localOrderUnits p) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (localOrderUnits_le_normalizer p)
  exact (le_inf h1 h2).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (localScalarGroup p) (localOrderUnits p))

theorem localH_le_localS : localH p ≤ localS p := by
  intro x hx
  change (x : (Bp p)ˣ) ∈ localOrderUnits p at hx
  change (x : (Bp p)ˣ) ∈ localDenom p
  exact (le_sup_right : localOrderUnits p ≤ localDenom p) hx

/-- Central membership in the order is precisely integral scalar membership,
including the prime two and the half-integral manuscript basis. -/
theorem scalar_mem_localOrder (c : ℚ_[p]) :
    algebraMap ℚ_[p] (Bp p) c ∈ localOrder p ↔ c ∈ PadicInt.subring p := by
  rw [mem_localOrder, GlueVigneras.mem_Op_iff_coord]
  constructor
  · intro h
    simpa [GlueVigneras.coord] using h 0
  · intro h k
    change ‖c‖ ≤ 1 at h
    fin_cases k <;> simp [GlueVigneras.coord, h]

theorem scalar_mem_localUnits (c : ℚ_[p]ˣ) :
    localScalar p c ∈ localOrderUnits p ↔
      c ∈ (PadicInt.subring p).toSubmonoid.units := by
  change (algebraMap ℚ_[p] (Bp p) (c : ℚ_[p]) ∈ localOrder p ∧
    algebraMap ℚ_[p] (Bp p) ((c⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) ∈ localOrder p) ↔ _
  rw [scalar_mem_localOrder, scalar_mem_localOrder]
  rfl

/-- At each ramified prime the actual local normalizer is the whole unit group. -/
theorem localNormalizer_eq_top (hp : p = 2 ∨ p = 3) : localNormalizer p = ⊤ := by
  apply SetLike.coe_injective
  exact GlueVigneras.normalizerOp_eq_univ p hp

/-- The scalar denominator is exactly the subgroup from the unchanged local proof. -/
theorem localDenom_eq_ramified (hp : p = 2 ∨ p = 3) :
    localDenom p = GlueVigneras.scalOpUnitsSubgroup p hp := by
  ext x
  exact mem_localDenom p x

/-- The local quotient has cardinality two at two and three. -/
theorem local_quotient_card_ramified (hp : p = 2 ∨ p = 3) :
    Nat.card ((localNormalizer p) ⧸ localS p) = 2 := by
  change (localDenom p).relIndex (localNormalizer p) = 2
  rw [localNormalizer_eq_top p hp, Subgroup.relIndex_top_right,
    localDenom_eq_ramified p hp]
  exact GlueVigneras.index_scalOpUnits p hp

/-- At every other prime the denominator is the whole local normalizer. -/
theorem localS_eq_top_unramified (h2 : p ≠ 2) (h3 : p ≠ 3) : localS p = ⊤ := by
  apply (Subgroup.eq_top_iff' _).2
  intro x
  change (x : (Bp p)ˣ) ∈ localDenom p
  apply (mem_localDenom p _).2
  apply GlueVigneras.unramified_normalizer p h2 h3 x
  intro y hy
  exact (x.property y).1 hy

/-- The index set is exhaustively covered; no prime is silently omitted. -/
theorem local_quotient_card (p : ℕ) [Fact p.Prime] :
    Nat.card ((localNormalizer p) ⧸ localS p) = if p = 2 ∨ p = 3 then 2 else 1 := by
  split_ifs with hp
  · exact local_quotient_card_ramified p hp
  · rw [localS_eq_top_unramified p (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))]
    simp

end Local

end

end G1
