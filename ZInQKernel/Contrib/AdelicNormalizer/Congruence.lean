import ZInQKernel.Contrib.AdelicNormalizer.Cardinality
import ZInQKernel.Contrib.AdelicNormalizer.IntegralComparison

/-!
# Principal congruence at every finite place

The kernel definition of K3 agrees with `1 + 3 completedOrder` on actual order
units.  At three the actual reduction kernel supplies divisibility.  At every
other prime, including two, the central scalar three is a local unit.
-/

open Quaternion

namespace G1

noncomputable section

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The central inverse of three in the actual adelic quaternion algebra. -/
def inverseThree : BA := algebraMap Af BA (algebraMap ℚ Af (1 / 3))

theorem inverseThree_mul_three : inverseThree * (3 : BA) = 1 := by
  change algebraMap ℚ BA (1 / 3) * 3 = 1
  rw [← map_ofNat (algebraMap ℚ BA) 3, ← map_mul]
  norm_num

theorem three_mul_inverseThree : (3 : BA) * inverseThree = 1 := by
  change (3 : BA) * algebraMap ℚ BA (1 / 3) = 1
  rw [← map_ofNat (algebraMap ℚ BA) 3, ← map_mul]
  norm_num

theorem quaternionEval_inverseThree (v : Place) :
    quaternionEval v inverseThree =
      algebraMap (Qv v) (Bv v) ((3 : Qv v)⁻¹) := by
  apply QuaternionAlgebra.ext
  · change scalarEval v (algebraMap ℚ Af (1 / 3)) = (3 : Qv v)⁻¹
    rw [scalarEval_rat]
    simp
  · change scalarEval v (0 : Af) = 0
    exact map_zero _
  · change scalarEval v (0 : Af) = 0
    exact map_zero _
  · change scalarEval v (0 : Af) = 0
    exact map_zero _

/-- Away from three, the central inverse of three belongs to the actual local order. -/
theorem inverseThree_mem_away (v : Place) (h3 : (primeAt v).1 ≠ 3) :
    quaternionEval v inverseThree ∈ localOrder (primeAt v).1 := by
  rw [quaternionEval_inverseThree, scalar_mem_localOrder]
  change ‖(3 : Qv v)⁻¹‖ ≤ 1
  have hnorm : ‖(3 : Qv v)‖ = 1 := by
    simpa using GlueVigneras.norm_int_eq_one (primeAt v).1 (k := 3) (by
      intro h
      have h' : (primeAt v).1 ∣ 3 := by exact_mod_cast h
      exact h3 ((Nat.prime_dvd_prime_iff_eq (primeAt v).2 Nat.prime_three).1 h'))
  simp [norm_inv, hnorm]

theorem quaternionAtPrime_mem_order (p : Nat.Primes) {x : BA} (hx : x ∈ completedOrder) :
    quaternionAtPrime p x ∈ localOrder p.1 := by
  change primeQuaternionEquiv p (quaternionEval (primePlace p) x) ∈ localOrder p.1
  exact (cast_mem_localOrder
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)
    (quaternionEval (primePlace p) x)).2 (hx (primePlace p))

/-- On actual order units, reduction one is exactly global principal congruence. -/
theorem mem_K3_iff_congruence (u : K0) :
    u.val ∈ K3 ↔ ∃ z ∈ completedOrder, (u.val : BA) - 1 = 3 * z := by
  constructor
  · intro hu
    obtain ⟨z3, hz3, h3⟩ := (unitReduction_eq_one_iff (K0AtPrime primeThree u)).1
      ((mem_K3 u).1 hu)
    let z : BA := inverseThree * ((u.val : BA) - 1)
    have hz : z ∈ completedOrder := by
      intro v
      by_cases hv : v = placeThree
      · subst v
        apply (cast_mem_localOrder (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply primeThree)
          (quaternionEval placeThree z)).1
        change quaternionAtPrime primeThree z ∈ localOrder 3
        have he : quaternionAtPrime primeThree z = z3 := by
          change quaternionAtPrime primeThree (inverseThree * ((u.val : BA) - 1)) = z3
          rw [map_mul, map_sub, map_one]
          change quaternionAtPrime primeThree inverseThree *
            (((K0AtPrime primeThree u).val : Bp 3) - 1) = z3
          rw [h3, ← mul_assoc]
          have hd : quaternionAtPrime primeThree inverseThree * (3 : Bp 3) = 1 := by
            rw [← map_ofNat (quaternionAtPrime primeThree) 3, ← map_mul,
              inverseThree_mul_three, map_one]
          rw [hd, one_mul]
        exact he.symm ▸ hz3
      · change quaternionEval v (inverseThree * ((u.val : BA) - 1)) ∈ _
        rw [map_mul, map_sub, map_one]
        exact (localOrder (primeAt v).1).mul_mem
          (inverseThree_mem_away v (fun h => hv ((primeAt_eq_three v).1 h)))
          ((localOrder (primeAt v).1).sub_mem (u.property.1 v) (localOrder _).one_mem)
    refine ⟨z, hz, ?_⟩
    change (u.val : BA) - 1 = 3 * (inverseThree * ((u.val : BA) - 1))
    rw [← mul_assoc, three_mul_inverseThree, one_mul]
  · rintro ⟨z, hz, h⟩
    apply (mem_K3 u).2
    apply (unitReduction_eq_one_iff (K0AtPrime primeThree u)).2
    refine ⟨quaternionAtPrime primeThree z, quaternionAtPrime_mem_order primeThree hz, ?_⟩
    have h' := congrArg (quaternionAtPrime primeThree) h
    change quaternionAtPrime primeThree (u.val : BA) - 1 =
      3 * quaternionAtPrime primeThree z
    simpa only [map_sub, map_one, map_mul, map_ofNat] using h'

end

end G1
