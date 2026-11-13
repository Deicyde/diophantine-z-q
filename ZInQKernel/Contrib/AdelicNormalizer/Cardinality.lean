import ZInQKernel.Contrib.AdelicNormalizer.ScalarLifting

/-!
# Cardinality of the actual adelic normalizer at principal level three

The quotient is `GammaPrime = N / (Afˣ K3)`, with the actual scalar image and
actual congruence kernel from the preceding modules.  The index factorization
is proved inside `N`, not by assuming normality in all quaternion units.
-/

open Quaternion
open scoped Pointwise

namespace G1

noncomputable section

abbrev ProjectiveResidue := Residue.Residue3ˣ ⧸ Residue.scalarUnits.range

/-- Actual order-unit reduction, followed by the actual scalar residue quotient. -/
def projectiveReduction : K0 →* ProjectiveResidue :=
  (QuotientGroup.mk' Residue.scalarUnits.range).comp reduction3

theorem projectiveReduction_surjective : Function.Surjective projectiveReduction := by
  intro y
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨u, rfl⟩ := reduction3_surjective r
  exact ⟨u, rfl⟩

/-- The projective reduction kernel is exactly integral scalar units times K3. -/
theorem ker_projectiveReduction :
    projectiveReduction.ker = integralLevelDenom.subgroupOf K0 := by
  ext u
  change (QuotientGroup.mk (reduction3 u) : ProjectiveResidue) = 1 ↔
    u.val ∈ integralLevelDenom
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hu
    rw [← range_reduction3_integralScalar] at hu
    obtain ⟨c, hc⟩ := hu
    let z : K0 := integralScalarK0 c
    let k : K0 := z⁻¹ * u
    have hzc : reduction3 z = reduction3 u := hc
    have hk : reduction3 k = 1 := by simp [k, map_mul, map_inv, hzc]
    have hz : z.val ∈ Z0 := ⟨⟨c.val, rfl⟩, z.property⟩
    have hprod : u = z * k := by simp [k]
    rw [congrArg (fun a : K0 => a.val) hprod]
    exact integralLevelDenom.mul_mem
      ((le_sup_left : Z0 ≤ integralLevelDenom) hz)
      ((le_sup_right : K3 ≤ integralLevelDenom) ((mem_K3 k).2 hk))
  · intro hu
    change u.val ∈ Z0 ⊔ K3 at hu
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hu
    obtain ⟨z, hz, k, hk, hprod⟩ := hu
    let z0 : K0 := ⟨z, hz.2⟩
    let k0 : K0 := ⟨k, K3_le_K0 hk⟩
    have hku : reduction3 k0 = 1 := (mem_K3 k0).1 hk
    have hzu : z ∈ ZhatUnits.map scalarIdeles := Z0_eq_integralScalars ▸ hz
    obtain ⟨c, hc, hcz⟩ := hzu
    let c0 : ZhatUnits := ⟨c, hc⟩
    have hz0 : z0 = integralScalarK0 c0 := Subtype.ext hcz.symm
    have hr : reduction3 (integralScalarK0 c0) ∈ Residue.scalarUnits.range :=
      range_reduction3_integralScalar ▸
        (show reduction3 (integralScalarK0 c0) ∈ (reduction3.comp integralScalarK0).range
          from ⟨c0, rfl⟩)
    have hu0 : u = z0 * k0 := Subtype.ext hprod.symm
    rw [hu0, map_mul, hku, mul_one, hz0]
    exact hr

instance integralLevelDenom_in_K0_normal : (integralLevelDenom.subgroupOf K0).Normal := by
  rw [← ker_projectiveReduction]
  infer_instance

/-- The order-unit quotient is identified with the actual finite residue quotient. -/
def levelQuotientEquiv : K0 ⧸ integralLevelDenom.subgroupOf K0 ≃* ProjectiveResidue :=
  (QuotientGroup.quotientMulEquivOfEq ker_projectiveReduction.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective projectiveReduction
      projectiveReduction_surjective)

/-- `|K0 / (Zhatˣ K3)| = 36`, through actual maps and their kernel. -/
theorem card_level_quotient : Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0) = 36 :=
  (Nat.card_congr levelQuotientEquiv.toEquiv).trans Residue.card_quotient_scalarUnits

theorem D3_le_D0 : D3 ≤ D0 := by
  intro u hu
  exact (sup_le le_sup_left (K3_le_K0.trans le_sup_right) :
    globalLevelDenom ≤ globalDenom) hu

/-- In the actual normalizer, the intermediate denominator is the level-three
one times K0.  Normality is needed only inside N. -/
theorem D0_eq_D3_sup_K0 : D0 = D3 ⊔ K0.subgroupOf N := by
  apply le_antisymm
  · intro u hu
    obtain ⟨c, k, hk, h⟩ := (mem_globalDenom_factor u.val).1 hu
    let z : N := ⟨scalarIdeles c, scalarSubgroup_le_N ⟨c, rfl⟩⟩
    let w : N := ⟨k, K0_le_N hk⟩
    have hz : z ∈ D3 :=
      (le_sup_left : scalarSubgroup ≤ globalLevelDenom) ⟨c, rfl⟩
    have hw : w ∈ K0.subgroupOf N := hk
    have hprod : u = z * w := Subtype.ext h
    rw [hprod]
    exact (D3 ⊔ K0.subgroupOf N).mul_mem
      ((le_sup_left : D3 ≤ D3 ⊔ K0.subgroupOf N) hz)
      ((le_sup_right : K0.subgroupOf N ≤ D3 ⊔ K0.subgroupOf N) hw)
  · apply sup_le D3_le_D0
    intro u hu
    exact (le_sup_right : K0 ≤ globalDenom) hu

/-- The relative index is the quotient by integral scalars and principal level,
using the proved scalar intersection. -/
theorem relIndex_D3_D0 :
    D3.relIndex D0 = Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0) := by
  calc
    D3.relIndex D0 = D3.relIndex (K0.subgroupOf N) := by
      rw [D0_eq_D3_sup_K0, Subgroup.relIndex_sup_left]
    _ = globalLevelDenom.relIndex K0 := Subgroup.relIndex_subgroupOf K0_le_N
    _ = integralLevelDenom.relIndex K0 := by
      rw [← Subgroup.inf_relIndex_right, intersect_levelDenom_K0]
    _ = Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0) := rfl

/-- Exact manuscript bookkeeping on the actual normalizer and actual level.
Neither GammaPrime nor either factor is defined by this formula. -/
theorem card_GammaPrime_eq_indices :
    Nat.card GammaPrime = Nat.card (N ⧸ D0) *
      Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0) := by
  have h := Subgroup.relIndex_mul_index D3_le_D0
  rw [relIndex_D3_D0] at h
  change D3.index = D0.index * Nat.card (K0 ⧸ integralLevelDenom.subgroupOf K0)
  exact h.symm.trans (Nat.mul_comm _ _)

/-- The actual normalizer quotient at principal level three has cardinality 144. -/
theorem card_GammaPrime : Nat.card GammaPrime = 144 := by
  rw [card_GammaPrime_eq_indices, card_normalizer_quotient, card_level_quotient]

instance GammaPrime_finite : Finite GammaPrime :=
  Nat.finite_of_card_ne_zero (by rw [card_GammaPrime]; norm_num)

/-- The arithmetic bound used in A3, without a claim about a geometric action. -/
theorem GammaPrime_card_bounds : Nat.card GammaPrime ≤ 288 ∧ Nat.card GammaPrime ≤ 324 := by
  rw [card_GammaPrime]
  norm_num

end

end G1
