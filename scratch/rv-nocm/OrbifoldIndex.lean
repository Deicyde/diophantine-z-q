import Mathlib

/-!
# rv-nocm: branch indices of a torsion-free normal cover equal the orbifold orders (A5, M4)

Glue for step A5 (h-b1 M4, Prop. TS, Lemma NV). The cover used there is `Y₃ → P¹_j`, i.e. on each
geometric component `Γ₃\ℍ → Γ*\ℍ`, with `Γ₃` the (torsion-free, normal) level-3 group and `Γ*`
the normalizer group. Its ramification index at the image of `τ` is the order of the stabilizer of
the orbit `Γ₃τ` in `Γ*/Γ₃`, which is `[S : Γ₃]` for `S = {g | gτ ∈ Γ₃τ}`. We prove, for any
group action, that `S = N ⊔ Stab(x)` and `[S : N] = |Stab(x)|` once `N ∩ Stab(x) = 1`, which holds
when `N` is torsion-free and `Stab(x)` finite. So the indices of `Y₃ → P¹_j` are the orbifold
(elliptic) orders `4, 6, 2` of `Γ*`, not the indices `2, 2, 2` of the degree-4 map `X₆ → X₆/W`
(whose group `Γ¹ ⊃ Γ₃` has torsion). Numerics: Riemann–Hurwitz consistency for
`[Γ* : Γ₃] = 72` (computed in `nocm_check.py`), and the labelling lemma for Lemma PR(i).
-/

namespace RvNocm

open MulAction

section Action

variable {G X : Type*} [Group G] [MulAction G X]

/-- The stabilizer in `G` of the `N`-orbit of `x`: `{g | g • x ∈ N • x}`. For the cover
`N\X → G\X`, its quotient by `N` is the stabilizer of the point `N x` in `G/N`, whose order is
the ramification index at `N x`. -/
def orbitStab (N : Subgroup G) [N.Normal] (x : X) : Subgroup G where
  carrier := {g | ∃ n ∈ N, g • x = n • x}
  one_mem' := ⟨1, N.one_mem, by simp⟩
  mul_mem' := by
    rintro g h ⟨n, hn, hg⟩ ⟨m, hm, hh⟩
    refine ⟨g * m * g⁻¹ * n, N.mul_mem (‹N.Normal›.conj_mem m hm g) hn, ?_⟩
    show (g * h) • x = (g * m * g⁻¹ * n) • x
    rw [mul_smul, hh, mul_smul (g * m * g⁻¹) n, ← hg, smul_smul, smul_smul]
    simp [mul_assoc]
  inv_mem' := by
    rintro g ⟨n, hn, hg⟩
    refine ⟨g⁻¹ * n⁻¹ * g, ?_, ?_⟩
    · have := ‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) g⁻¹
      simpa using this
    · show g⁻¹ • x = (g⁻¹ * n⁻¹ * g) • x
      rw [mul_smul, mul_smul, hg, inv_smul_smul]

theorem orbitStab_eq_sup (N : Subgroup G) [N.Normal] (x : X) :
    orbitStab N x = N ⊔ stabilizer G x := by
  apply le_antisymm
  · rintro g ⟨n, hn, hg⟩
    have hs : n⁻¹ * g ∈ stabilizer G x := by
      rw [mem_stabilizer_iff, mul_smul, hg, inv_smul_smul]
    have : g = n * (n⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hn hs
  · refine sup_le (fun n hn => ⟨n, hn, rfl⟩) (fun g hg => ⟨1, N.one_mem, ?_⟩)
    rw [mem_stabilizer_iff] at hg
    rw [hg, one_smul]

/-- **Ramification index = orbifold order.** If `N` meets the stabilizer of `x` trivially, the
index `[orbitStab N x : N]` (the ramification index of `N\X → G\X` at `N x`) equals the order of
the stabilizer of `x` in `G` (the orbifold order of `G` at `x`). -/
theorem relIndex_orbitStab (N : Subgroup G) [N.Normal] (x : X)
    (hfree : N ⊓ stabilizer G x = ⊥) :
    N.relIndex (orbitStab N x) = Nat.card (stabilizer G x) := by
  rw [orbitStab_eq_sup, Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hfree,
    Subgroup.relIndex_bot_left]

/-- Torsion-freeness of `N` (neatness of `K₃`) gives the hypothesis of `relIndex_orbitStab`
whenever the stabilizer is finite (elliptic points of a Fuchsian group). -/
theorem inf_stabilizer_eq_bot (N : Subgroup G) (x : X) [Finite (stabilizer G x)]
    (htf : ∀ g ∈ N, IsOfFinOrder g → g = 1) : N ⊓ stabilizer G x = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hgN, hgS⟩
  rw [Subgroup.mem_bot]
  apply htf g hgN
  have h : IsOfFinOrder (⟨g, hgS⟩ : stabilizer G x) := isOfFinOrder_of_finite _
  exact (stabilizer G x).subtype.isOfFinOrder h

/-- The combined statement used for `Y₃ → P¹_j`. -/
theorem ramification_eq_orbifold_order (N : Subgroup G) [N.Normal] (x : X)
    [Finite (stabilizer G x)] (htf : ∀ g ∈ N, IsOfFinOrder g → g = 1) :
    N.relIndex (orbitStab N x) = Nat.card (stabilizer G x) :=
  relIndex_orbitStab N x (inf_stabilizer_eq_bot N x htf)

end Action

/-! ## Numerics -/

/-- Riemann–Hurwitz for a geometric component of `Y₃` over `P¹_j`, of degree `72`
(`[Γ* : Γ₃] = 4·36/2`, `nocm_check.py` Part D): the indices `4, 6, 2` give genus `4`. -/
theorem rh_462 : (72 : ℚ) * (-2 + (1 - 1/4) + (1 - 1/6) + (1 - 1/2)) = 2 * 4 - 2 := by norm_num

/-- With indices `2, 2, 2` (those of `X₆ → X₆/W`) a degree-72 cover of `P¹` branched only over
three points would have negative genus: impossible. -/
theorem rh_222_impossible (g : ℕ) :
    (72 : ℚ) * (-2 + (1 - 1/2) + (1 - 1/2) + (1 - 1/2)) ≠ 2 * g - 2 := by
  intro h
  have : (2 : ℚ) * g = -34 := by linarith
  have : (0 : ℚ) ≤ 2 * g := by positivity
  linarith

/-- Orbifold Euler characteristics: `Γ¹` of signature `(0;2,2,3,3)` and `Γ*` of signature
`(0;2,4,6)` have ratio `4 = |W|`; the stabilizer orders in `W` are `4/2, 6/3, 2/1 = 2`. -/
theorem euler_ratio :
    (-2 + 2 * (1 - (1:ℚ)/2) + 2 * (1 - 1/3)) = 4 * (-2 + (1 - 1/2) + (1 - 1/4) + (1 - 1/6)) := by
  norm_num

/-- **Labelling (Lemma PR(i)).** At `p ≥ 17` with `p ∤ M_S(u)`, the intersection multiplicities of
`J(u)` with `0, ∞, −16/27` lie in `4ℕ, 6ℕ, 2ℕ` (`m₀ = 2v_p(F)`, `v_p(F)` even; `m_∞ = 6v_p(G)`;
`m = 2v_p(H)`). Among the assignments of indices `(e₀, e_∞, e_{−16/27})` that are permutations
of `(4, 6, 2)`, the conclusion "all inertia orders `e/gcd(e,m)` equal 1" holds for all such
multiplicities only for `(4, 6, 2)`. Checked on the generators `m = 4, 6, 2`. -/
theorem labelling (e₀ e₁ e₂ : ℕ) (hperm : [e₀, e₁, e₂].Perm [4, 6, 2]) :
    (e₀ ∣ 4 ∧ e₁ ∣ 6 ∧ e₂ ∣ 2) ↔ (e₀ = 4 ∧ e₁ = 6 ∧ e₂ = 2) := by
  have h : (e₀, e₁, e₂) ∈ ([(4,6,2), (4,2,6), (6,4,2), (6,2,4), (2,4,6), (2,6,4)] :
      List (ℕ × ℕ × ℕ)) := by
    have hmem : ∀ a ∈ [e₀, e₁, e₂], a ∈ [4, 6, 2] := fun a ha => hperm.subset ha
    have h0 := hmem e₀ (by simp)
    have h1 := hmem e₁ (by simp)
    have h2 := hmem e₂ (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h1 h2
    have hnd := hperm.nodup_iff.mpr (by decide)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd
    rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
      rcases h2 with rfl | rfl | rfl <;> simp_all
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide

/-- **Robustness of A5's needed direction.** If the true indices divide `(4, 6, 2)` (for instance
`(2, 2, 2)`), the needed direction "multiplicities in `4ℕ, 6ℕ, 2ℕ` ⇒ trivial inertia" still
holds; the exact values `(4, 6, 2)` are needed only for the converse (the "iff" of
`GlueRepo.PR.inertia_orders_eq_one_iff`). -/
theorem inertia_trivial_of_dvd {e₀ e₁ e₂ m₀ m₁ m₂ : ℕ} (h₀ : e₀ ∣ 4) (h₁ : e₁ ∣ 6) (h₂ : e₂ ∣ 2)
    (hm₀ : 4 ∣ m₀) (hm₁ : 6 ∣ m₁) (hm₂ : 2 ∣ m₂) :
    e₀ / Nat.gcd e₀ m₀ = 1 ∧ e₁ / Nat.gcd e₁ m₁ = 1 ∧ e₂ / Nat.gcd e₂ m₂ = 1 := by
  have key : ∀ e m : ℕ, e ∣ m → e / Nat.gcd e m = 1 ∨ e = 0 := by
    intro e m hem
    rcases Nat.eq_zero_or_pos e with h | h
    · exact Or.inr h
    · left; rw [Nat.gcd_eq_left hem, Nat.div_self h]
  have p0 : 0 < e₀ := Nat.pos_of_dvd_of_pos h₀ (by norm_num)
  have p1 : 0 < e₁ := Nat.pos_of_dvd_of_pos h₁ (by norm_num)
  have p2 : 0 < e₂ := Nat.pos_of_dvd_of_pos h₂ (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rcases key e₀ m₀ (h₀.trans hm₀) with h | h; exact h; omega
  · rcases key e₁ m₁ (h₁.trans hm₁) with h | h; exact h; omega
  · rcases key e₂ m₂ (h₂.trans hm₂) with h | h; exact h; omega

end RvNocm

#print axioms RvNocm.relIndex_orbitStab
#print axioms RvNocm.ramification_eq_orbifold_order
#print axioms RvNocm.rh_462
#print axioms RvNocm.rh_222_impossible
#print axioms RvNocm.euler_ratio
#print axioms RvNocm.labelling
#print axioms RvNocm.inertia_trivial_of_dvd
