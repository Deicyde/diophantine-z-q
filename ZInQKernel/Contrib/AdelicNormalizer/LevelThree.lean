import ZInQKernel.Contrib.AdelicNormalizer.PrimeEvaluation
import ZInQKernel.Contrib.AdelicNormalizer.Residue

/-!
# Actual principal level three and its normalizer quotient

`K3` is the kernel of reduction of actual completed-order units, embedded in
`BAˣ`.  `GammaPrime` is the quotient of the actual conjugation normalizer by
finite ideles times that kernel; it is never defined as a desired product.
-/

open Quaternion
open scoped Pointwise

namespace G1

noncomputable section

abbrev primeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- Reduction of the actual adelic order units at the central level three. -/
def reduction3 : K0 →* Residue.Residue3ˣ :=
  Residue.unitReduction.comp (K0AtPrime primeThree)

theorem reduction3_surjective : Function.Surjective reduction3 :=
  Residue.unitReduction_surjective.comp (K0AtPrime_surjective primeThree)

/-- The actual principal congruence subgroup, embedded in actual adelic units. -/
def K3 : Subgroup BAˣ := reduction3.ker.map K0.subtype

theorem mem_K3 (u : K0) : (u : BAˣ) ∈ K3 ↔ reduction3 u = 1 := by
  constructor
  · rintro ⟨w, hw, h⟩
    have hw' : w = u := Subtype.ext h
    exact hw' ▸ hw
  · intro h
    exact ⟨u, h, rfl⟩

theorem K3_le_K0 : K3 ≤ K0 := by
  rintro _ ⟨u, _, rfl⟩
  exact u.property

theorem K3_le_N : K3 ≤ N := K3_le_K0.trans K0_le_N

/-- Order-normalizing conjugation preserves actual order units. -/
theorem conjugate_mem_K0 {u : BAˣ} (hu : u ∈ K0) (g : N) :
    g.val * u * g.val⁻¹ ∈ K0 := by
  rcases hu with ⟨hu, hui⟩
  constructor
  · exact (g.property (u : BA)).1 hu
  · have h := (g.property ((u⁻¹ : BAˣ) : BA)).1 hui
    simpa [mul_inv_rev, mul_assoc] using h

instance K0_in_N_normal : (K0.subgroupOf N).Normal where
  conj_mem u hu g := conjugate_mem_K0 hu g

/-- Reduction one means precisely principal congruence in the actual local order. -/
theorem unitReduction_eq_one_iff (u : localOrderUnits 3) :
    Residue.unitReduction u = 1 ↔
      ∃ z ∈ localOrder 3, ((u : (Bp 3)ˣ) : Bp 3) - 1 = 3 * z := by
  rw [Units.ext_iff, Residue.coe_unitReduction, Units.val_one,
    ← map_one Residue.localReduction]
  change Residue.localReduction ⟨((u : (Bp 3)ˣ) : Bp 3), u.property.1⟩ =
    Residue.localReduction (1 : localOrder 3) ↔ _
  exact Residue.localReduction_eq_iff_sub _ _

/-- A local order normalizer preserves principal congruence, not just units. -/
theorem conjugate_reduction_eq_one (g : (Bp 3)ˣ) (hg : g ∈ localNormalizer 3)
    (u w : localOrderUnits 3) (hu : Residue.unitReduction u = 1)
    (hw : w.val = g * u.val * g⁻¹) : Residue.unitReduction w = 1 := by
  obtain ⟨z, hz, h⟩ := (unitReduction_eq_one_iff u).1 hu
  apply (unitReduction_eq_one_iff w).2
  refine ⟨(g : Bp 3) * z * ((g⁻¹ : (Bp 3)ˣ) : Bp 3), (hg z).1 hz, ?_⟩
  have hw' := congrArg (fun a : (Bp 3)ˣ => (a : Bp 3)) hw
  calc
    ((w : (Bp 3)ˣ) : Bp 3) - 1 =
        (g : Bp 3) * (((u : (Bp 3)ˣ) : Bp 3) - 1) * ((g⁻¹ : (Bp 3)ˣ) : Bp 3) := by
      rw [hw']
      simp [mul_sub, sub_mul, mul_assoc]
    _ = (g : Bp 3) * (3 * z) * ((g⁻¹ : (Bp 3)ˣ) : Bp 3) := by rw [h]
    _ = 3 * ((g : Bp 3) * z * ((g⁻¹ : (Bp 3)ˣ) : Bp 3)) := by noncomm_ring

instance K3_in_N_normal : (K3.subgroupOf N).Normal where
  conj_mem n hn g := by
    change n.val ∈ K3 at hn
    let u : K0 := ⟨n.val, K3_le_K0 hn⟩
    let w : K0 := ⟨g.val * n.val * g.val⁻¹, conjugate_mem_K0 u.property g⟩
    have hu : Residue.unitReduction (K0AtPrime primeThree u) = 1 := (mem_K3 u).1 hn
    have hw : Residue.unitReduction (K0AtPrime primeThree w) = 1 :=
      conjugate_reduction_eq_one (unitAtPrime primeThree g.val)
        (unitAtPrime_mem_N primeThree g.property)
        (K0AtPrime primeThree u) (K0AtPrime primeThree w) hu
        (by
          change unitAtPrime primeThree (g.val * n.val * g.val⁻¹) = _
          simp [map_mul, map_inv, K0AtPrime, u])
    exact (mem_K3 w).2 hw

/-- Finite ideles times the actual principal level-three subgroup. -/
def globalLevelDenom : Subgroup BAˣ := scalarSubgroup ⊔ K3

theorem globalLevelDenom_le_N : globalLevelDenom ≤ N := sup_le scalarSubgroup_le_N K3_le_N

/-- The level-three denominator inside the actual order normalizer. -/
def D3 : Subgroup N := globalLevelDenom.subgroupOf N

instance D3_normal : D3.Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer globalLevelDenom_le_N).2
  have h1 : N ≤ Subgroup.normalizer scalarSubgroup := Subgroup.le_normalizer_of_normal
  have h2 : N ≤ Subgroup.normalizer K3 :=
    Subgroup.le_normalizer_of_normal_subgroupOf K3_le_N
  exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_sup scalarSubgroup K3)

/-- The manuscript group: quotient of the actual adelic normalizer by actual
finite ideles times principal level three. -/
abbrev GammaPrime := N ⧸ D3

/-- Integral scalar units times principal level three, in the actual adelic unit group. -/
def integralLevelDenom : Subgroup BAˣ := Z0 ⊔ K3

theorem integralLevelDenom_le_K0 : integralLevelDenom ≤ K0 := sup_le inf_le_right K3_le_K0

/-- The intersection required by index multiplication; no scalar is silently discarded. -/
theorem intersect_levelDenom_K0 : globalLevelDenom ⊓ K0 = integralLevelDenom := by
  apply le_antisymm
  · intro u hu
    rcases hu with ⟨hud, huk⟩
    change u ∈ scalarSubgroup ⊔ K3 at hud
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hud
    rcases hud with ⟨c, hc, k, hk, h⟩
    have hck : c ∈ K0 := by
      have h' : c = u * k⁻¹ := by rw [← h]; simp [mul_assoc]
      rw [h']
      exact K0.mul_mem huk (K0.inv_mem (K3_le_K0 hk))
    rw [← h]
    exact integralLevelDenom.mul_mem
      ((le_sup_left : Z0 ≤ integralLevelDenom) ⟨hc, hck⟩)
      ((le_sup_right : K3 ≤ integralLevelDenom) hk)
  · intro u hu
    refine ⟨?_, integralLevelDenom_le_K0 hu⟩
    exact (sup_le (inf_le_left.trans le_sup_left) le_sup_right :
      integralLevelDenom ≤ globalLevelDenom) hu

end

end G1
