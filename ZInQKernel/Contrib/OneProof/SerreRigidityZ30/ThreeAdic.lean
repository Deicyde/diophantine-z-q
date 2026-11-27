import Mathlib

/-!
# Finite-order endomorphisms on `3`-power torsion

Let `G` be a commutative group whose `3 ^ j`-torsion has exactly `3 ^ (r * j)` elements for
every `j`.  An endomorphism `φ` of `G` of finite order that is trivial on the `3`-torsion is
trivial on all `3`-power torsion.

The proof splits the order `m` of `φ` into its prime-to-`3` part and its `3`-part.

* If `3 ∤ m`, induction on the torsion level works in any commutative group: if `φ` fixes the
  `3 ^ n`-torsion and `x` is killed by `3 ^ (n + 1)`, then `φ x = t * x` with `t ^ 3 = 1` and
  `φ t = t`, so `x = φ^[m] x = t ^ m * x` forces `t = 1`.
* If `φ ^ 3` is trivial on `3`-power torsion, counting shows that every element killed by
  `3 ^ (k + 1)` is the cube of an element `y` killed by `3 ^ (k + 2)`.  Writing `φ y = a * y`
  and `φ a = b * a`, one finds `b ^ 3 = 1` and `φ (φ (φ y)) = b ^ 3 * a ^ 3 * y`, so
  `a ^ 3 = 1`, i.e. `φ` fixes `y ^ 3`.  The middle binomial coefficient of `(1 + ψ) ^ 3` is
  divisible by `3`; this is where the oddness of `3` enters (the analogue for the prime `2`
  is false).
* The general case follows by strong induction on `m`, passing to `φ ^ 3` when `3 ∣ m`.
-/

set_option autoImplicit false

namespace Y3Buzzard.ThreeAdic

/-- The subgroup of elements killed by `3 ^ j`. -/
def torsionLevel (G : Type) [CommGroup G] (j : ℕ) : Subgroup G :=
  (powMonoidHom (3 ^ j) : G →* G).ker

section Lemmas

variable {G : Type} [CommGroup G]

theorem mem_torsionLevel {j : ℕ} {z : G} : z ∈ torsionLevel G j ↔ z ^ (3 ^ j) = 1 := by
  simp only [torsionLevel, MonoidHom.mem_ker, powMonoidHom_apply]

theorem pow_three_pow_succ (x : G) (n : ℕ) : x ^ (3 ^ (n + 1)) = (x ^ 3) ^ (3 ^ n) := by
  rw [← pow_mul, ← pow_succ']

/-- Counting: every element killed by `3 ^ (k + 1)` is the cube of an element killed by
`3 ^ (k + 2)`.  The cubing map from the `3 ^ (k + 2)`-torsion has kernel the `3`-torsion, so
its image has `3 ^ (r * (k + 2)) / 3 ^ r = 3 ^ (r * (k + 1))` elements and fills the
`3 ^ (k + 1)`-torsion. -/
theorem exists_cube_root (r : ℕ)
    (hcard : ∀ j : ℕ, Nat.card {x : G // x ^ (3 ^ j) = 1} = 3 ^ (r * j))
    (k : ℕ) (x : G) (hx : x ^ (3 ^ (k + 1)) = 1) :
    ∃ y : G, y ^ (3 ^ (k + 2)) = 1 ∧ y ^ 3 = x := by
  have hcardT : ∀ j, Nat.card (torsionLevel G j) = 3 ^ (r * j) := fun j => by
    rw [← hcard j]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun z => mem_torsionLevel))
  have hfinT : ∀ j, Finite (torsionLevel G j) := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hcardT]; positivity)
  -- the cubing map on the `3 ^ (k + 2)`-torsion
  obtain ⟨f, hf⟩ : ∃ f : torsionLevel G (k + 2) →* G, ∀ z, f z = (z : G) ^ 3 :=
    ⟨(powMonoidHom 3 : G →* G).domRestrict (torsionLevel G (k + 2)), fun z => rfl⟩
  have hle : torsionLevel G 1 ≤ torsionLevel G (k + 2) := by
    intro z hz
    rw [mem_torsionLevel, pow_one] at hz
    rw [mem_torsionLevel]
    calc z ^ 3 ^ (k + 2) = (z ^ 3) ^ 3 ^ (k + 1) := pow_three_pow_succ z (k + 1)
      _ = 1 := by rw [hz, one_pow]
  have hker : f.ker = (torsionLevel G 1).subgroupOf (torsionLevel G (k + 2)) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_torsionLevel, pow_one, hf]
  have hkercard : Nat.card f.ker = 3 ^ r := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardT, mul_one]
  have hrange_le : f.range ≤ torsionLevel G (k + 1) := by
    rintro _ ⟨z, rfl⟩
    have hz : (z : G) ^ 3 ^ (k + 2) = 1 := mem_torsionLevel.1 z.2
    rw [mem_torsionLevel, hf, ← pow_three_pow_succ]
    exact hz
  have hsplit : Nat.card (torsionLevel G (k + 2)) = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hrangecard : Nat.card f.range = 3 ^ (r * (k + 1)) := by
    rw [hcardT, hkercard] at hsplit
    have e : 3 ^ (r * (k + 2)) = 3 ^ (r * (k + 1)) * 3 ^ r := by
      rw [← pow_add, show r * (k + 2) = r * (k + 1) + r by ring]
    rw [e] at hsplit
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) hsplit).symm
  have := hfinT (k + 1)
  have hrange : f.range = torsionLevel G (k + 1) :=
    Subgroup.eq_of_le_of_card_ge hrange_le ((hcardT (k + 1)).trans hrangecard.symm).le
  have hxr : x ∈ f.range := by
    rw [hrange, mem_torsionLevel]
    exact hx
  obtain ⟨z, hz⟩ := hxr
  exact ⟨z, mem_torsionLevel.1 z.2, (hf z).symm.trans hz⟩

/-- The prime-to-`3` case, valid in every commutative group. -/
theorem fixes_of_coprime (φ : G →* G) (u : ℕ) (hu : Nat.Coprime 3 u)
    (hφu : ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → (φ^[u]) x = x)
    (h1 : ∀ x : G, x ^ 3 = 1 → φ x = x) :
    ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → φ x = x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, pow_one] at hx
    rw [hx, map_one]
  | succ n ih =>
    intro x hx
    obtain ⟨t, ht⟩ : ∃ t, φ x = t * x := ⟨φ x * x⁻¹, (inv_mul_cancel_right (φ x) x).symm⟩
    have hx3 : φ (x ^ 3) = x ^ 3 := ih _ (by rw [← pow_three_pow_succ]; exact hx)
    have ht3 : t ^ 3 = 1 := by
      rw [map_pow, ht, mul_pow] at hx3
      exact mul_right_cancel (hx3.trans (one_mul _).symm)
    have hφt : φ t = t := h1 t ht3
    have hiter : ∀ i : ℕ, (φ^[i]) x = t ^ i * x := by
      intro i
      induction i with
      | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
      | succ i ihi =>
        rw [Function.iterate_succ_apply', ihi, map_mul, map_pow, hφt, ht, pow_succ, mul_assoc]
    have htu : t ^ u = 1 := by
      have h := hφu (n + 1) x hx
      rw [hiter u] at h
      exact mul_right_cancel (h.trans (one_mul _).symm)
    have ht1 : t = 1 := by
      have h := pow_gcd_eq_one.2 ⟨ht3, htu⟩
      rwa [Nat.Coprime.gcd_eq_one hu, pow_one] at h
    rw [ht, ht1, one_mul]

/-- The cube step: if `φ` fixes the `3`-torsion and `y ^ 9`, and `φ ^ 3` fixes `y`, then `φ`
fixes `y ^ 3`. -/
theorem fixes_cube_of_fixes (φ : G →* G) (h1 : ∀ x : G, x ^ 3 = 1 → φ x = x) (y : G)
    (h9 : φ (y ^ 9) = y ^ 9) (h3 : φ (φ (φ y)) = y) : φ (y ^ 3) = y ^ 3 := by
  obtain ⟨a, ha⟩ : ∃ a, φ y = a * y := ⟨φ y * y⁻¹, (inv_mul_cancel_right (φ y) y).symm⟩
  have ha9 : a ^ 9 = 1 := by
    rw [map_pow, ha, mul_pow] at h9
    exact mul_right_cancel (h9.trans (one_mul _).symm)
  have ha3 : φ (a ^ 3) = a ^ 3 := h1 _ (by rw [← pow_mul]; exact ha9)
  obtain ⟨b, hb⟩ : ∃ b, φ a = b * a := ⟨φ a * a⁻¹, (inv_mul_cancel_right (φ a) a).symm⟩
  have hb3 : b ^ 3 = 1 := by
    rw [map_pow, hb, mul_pow] at ha3
    exact mul_right_cancel (ha3.trans (one_mul _).symm)
  have hφb : φ b = b := h1 b hb3
  have key : φ (φ (φ y)) = b ^ 3 * a ^ 3 * y := by
    simp only [ha, hb, hφb, map_mul]
    rw [pow_three, pow_three]
    ac_rfl
  rw [key, hb3, one_mul] at h3
  have ha1 : a ^ 3 = 1 := mul_right_cancel (h3.trans (one_mul _).symm)
  rw [map_pow, ha, mul_pow, ha1, one_mul]

/-- The case where `φ ^ 3` is trivial on `3`-power torsion. -/
theorem fixes_of_cube (r : ℕ)
    (hcard : ∀ j : ℕ, Nat.card {x : G // x ^ (3 ^ j) = 1} = 3 ^ (r * j)) (φ : G →* G)
    (h3 : ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → φ (φ (φ x)) = x)
    (h1 : ∀ x : G, x ^ 3 = 1 → φ x = x) :
    ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → φ x = x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, pow_one] at hx
    rw [hx, map_one]
  | succ n ih =>
    intro x hx
    cases n with
    | zero =>
      rw [zero_add, pow_one] at hx
      exact h1 x hx
    | succ k =>
      obtain ⟨y, hy, rfl⟩ := exists_cube_root r hcard (k + 1) x hx
      refine fixes_cube_of_fixes φ h1 y (ih _ ?_) (h3 _ y hy)
      have e : 9 * 3 ^ (k + 1) = 3 ^ (k + 1 + 2) := by ring
      rw [← pow_mul, e]
      exact hy

end Lemmas

/-- An endomorphism of finite order of a commutative group whose `3 ^ j`-torsion has
`3 ^ (r * j)` elements for every `j`, trivial on the `3`-torsion, is trivial on all `3`-power
torsion. -/
theorem fixes_threePow {G : Type} [CommGroup G] (φ : G →* G) (m : ℕ) (hm : 0 < m)
    (hφm : ∀ x, (φ^[m]) x = x) (h1 : ∀ x : G, x ^ 3 = 1 → φ x = x) (r : ℕ)
    (hcard : ∀ j : ℕ, Nat.card {x : G // x ^ (3 ^ j) = 1} = 3 ^ (r * j)) :
    ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → φ x = x := by
  have main : ∀ m : ℕ, 0 < m → ∀ ψ : G →* G,
      (∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → (ψ^[m]) x = x) →
      (∀ x : G, x ^ 3 = 1 → ψ x = x) →
      ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → ψ x = x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm ψ hψm hψ1
      by_cases h3m : 3 ∣ m
      · obtain ⟨m', rfl⟩ := h3m
        have hcube : ∀ (n : ℕ) (x : G), x ^ (3 ^ n) = 1 → ψ (ψ (ψ x)) = x := by
          refine ih m' (by omega) (by omega) (ψ.comp (ψ.comp ψ)) ?_ ?_
          · intro n x hx
            have e : (⇑(ψ.comp (ψ.comp ψ)) : G → G) = ψ^[3] := by
              funext z
              rfl
            rw [e, ← Function.iterate_mul]
            exact hψm n x hx
          · intro x hx
            simp only [MonoidHom.coe_comp, Function.comp_apply, hψ1 x hx]
        exact fixes_of_cube r hcard ψ hcube hψ1
      · exact fixes_of_coprime ψ m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3m)
          hψm hψ1
  exact main m hm φ (fun _ x _ => hφm x) h1

end Y3Buzzard.ThreeAdic
