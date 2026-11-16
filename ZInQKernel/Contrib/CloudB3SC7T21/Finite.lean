import ZInQKernel.Contrib.CloudB3SC7T21.Hurwitz

/-!
# t21-proof: the finite computations (kernel `decide`)

Task t21-proof. Integer data in Hurwitz coordinates:
* `unitList`: the 24 units of the Hurwitz order; `mem_unitList`: every integral element of norm `1`
  is one of them;
* the 8 admissible embeddings `τ : ℚ(√−3) → B` are indexed by sign bits `s` (`τ(√−3) = ±i ± j ± k`),
  `ωH s` = Hurwitz coordinates of `τ((1 + √−3)/2)`;
* `βZ t` = Hurwitz coordinates of TYZ's representative `1 + 2x_t` (L646–651);
* `mod4_check`: for `t ∉ {0, t*(s)}` no `μ β_t` (`μ` a unit) lies in `ℤ + ℤω + 4O_B` modulo 4;
* `partner_eq`: `β_{t*(s)} ∈ ℤ + ℤω + 4O_B`.
All checks are by `decide` (kernel).
-/

set_option linter.style.longLine false

namespace ZInQ.Contrib.T21Proof

/-- The 24 units of the Hurwitz order, in Hurwitz coordinates. -/
def unitList : List (H4 ℤ) :=
  [⟨-1,0,0,0⟩, ⟨0,-1,0,0⟩, ⟨0,0,-1,0⟩, ⟨-1,1,1,-2⟩, ⟨1,-1,-1,2⟩, ⟨0,0,1,0⟩, ⟨0,1,0,0⟩, ⟨1,0,0,0⟩,
   ⟨1,0,0,1⟩, ⟨0,1,1,-1⟩, ⟨1,0,-1,1⟩, ⟨0,1,0,-1⟩, ⟨1,-1,0,1⟩, ⟨0,0,1,-1⟩, ⟨1,-1,-1,1⟩, ⟨0,0,0,-1⟩,
   ⟨0,0,0,1⟩, ⟨-1,1,1,-1⟩, ⟨0,0,-1,1⟩, ⟨-1,1,0,-1⟩, ⟨0,-1,0,1⟩, ⟨-1,0,1,-1⟩, ⟨0,-1,-1,1⟩, ⟨-1,0,0,-1⟩]

/-- The integer `k - 2` for `k : Fin 5`. -/
def f5 (k : Fin 5) : ℤ := (k : ℤ) - 2

theorem box_check : ∀ a0 a1 a2 a3 : Fin 5,
    nrdH (⟨f5 a0, f5 a1, f5 a2, f5 a3⟩ : H4 ℤ) = 1 → (⟨f5 a0, f5 a1, f5 a2, f5 a3⟩ : H4 ℤ) ∈ unitList := by
  decide +kernel

theorem exists_f5 {x : ℤ} (h1 : -2 ≤ x) (h2 : x ≤ 2) : ∃ k : Fin 5, f5 k = x :=
  ⟨⟨(x + 2).toNat, by omega⟩, by simp only [f5]; omega⟩

/-- **The units of the Hurwitz order.** -/
theorem mem_unitList {a : H4 ℤ} (h : nrdH a = 1) : a ∈ unitList := by
  have h4 : (2 * a.a0 - a.a3) ^ 2 + (2 * a.a1 + a.a3) ^ 2 + (2 * a.a2 + a.a3) ^ 2 + a.a3 ^ 2 = 4 := by
    rw [← show 4 * nrdH a = 4 by rw [h]; norm_num]; simp only [nrdH]; ring
  have s0 := sq_nonneg (2 * a.a0 - a.a3)
  have s1 := sq_nonneg (2 * a.a1 + a.a3)
  have s2 := sq_nonneg (2 * a.a2 + a.a3)
  have s3 := sq_nonneg a.a3
  have b3 : -2 ≤ a.a3 ∧ a.a3 ≤ 2 := by constructor <;> nlinarith
  have b0 : -2 ≤ a.a0 ∧ a.a0 ≤ 2 := by constructor <;> nlinarith
  have b1 : -2 ≤ a.a1 ∧ a.a1 ≤ 2 := by constructor <;> nlinarith
  have b2 : -2 ≤ a.a2 ∧ a.a2 ≤ 2 := by constructor <;> nlinarith
  obtain ⟨k0, e0⟩ := exists_f5 b0.1 b0.2
  obtain ⟨k1, e1⟩ := exists_f5 b1.1 b1.2
  obtain ⟨k2, e2⟩ := exists_f5 b2.1 b2.2
  obtain ⟨k3, e3⟩ := exists_f5 b3.1 b3.2
  have := box_check k0 k1 k2 k3
  rw [e0, e1, e2, e3] at this
  exact this h

/-- Sign bits of an admissible embedding: bit `0` is `+1`, bit `1` is `−1`. -/
abbrev Signs : Type := Fin 2 × Fin 2 × Fin 2

/-- The sign `±1` of a bit. -/
def sg (b : Fin 2) : ℤ := 1 - 2 * (b : ℤ)

/-- Hurwitz coordinates of `ω_s = (1 + s₁ i + s₂ j + s₃ k)/2`. -/
def ωH (s : Signs) : H4 ℤ :=
  ⟨1 - (s.2.2 : ℤ), (s.2.2 : ℤ) - (s.1 : ℤ), (s.2.2 : ℤ) - (s.2.1 : ℤ), sg s.2.2⟩

/-- Hurwitz coordinates of TYZ's representative `1 + 2(a i + b j + c ζ)` (`twoRepQ`). -/
def βZ (t : Fin 2 × Fin 2 × Fin 2) : H4 ℤ := ⟨1, 2 * (t.1 : ℤ), 2 * (t.2.1 : ℤ), 2 * (t.2.2 : ℤ)⟩

/-- The partner class `t*(s)` (the second class of `B^× \ B̂^× / ℚ̂^× U_3` meeting `1`). -/
def tstar (s : Signs) : Fin 2 × Fin 2 × Fin 2 :=
  (if s.1 = s.2.2 then 0 else 1, if s.2.1 = s.2.2 then 0 else 1, 1)

/-- The mod-4 obstruction. -/
def Mod4Rel (ω β : H4 ℤ) (X Y : ZMod 4) : Prop :=
  mapH (Int.castRingHom (ZMod 4)) β =
    ⟨X + Y * (ω.a0 : ZMod 4), Y * (ω.a1 : ZMod 4), Y * (ω.a2 : ZMod 4), Y * (ω.a3 : ZMod 4)⟩

instance (ω β : H4 ℤ) (X Y : ZMod 4) : Decidable (Mod4Rel ω β X Y) := by
  unfold Mod4Rel; infer_instance

/-- **The finite obstruction**: for `t ∉ {0, t*(s)}`, no `μ β_t` (`μ` a Hurwitz unit) is
congruent to an element of `ℤ + ℤ ω_s` modulo `4 O_B`. -/
theorem mod4_check : ∀ s : Signs, ∀ t : Fin 2 × Fin 2 × Fin 2, t ≠ (0, 0, 0) → t ≠ tstar s →
    ∀ μ ∈ unitList, ∀ X Y : ZMod 4, ¬ Mod4Rel (ωH s) (mulH μ (βZ t)) X Y := by
  decide +kernel

/-- `x` and `q` of `β_{t*(s)} = x + 2 ω_s + 4 q`. -/
def px (s : Signs) : ℤ := if s.2.2 = 0 then 3 else 1

def pq (s : Signs) : H4 ℤ := if s.2.2 = 0 then ⟨-1, s.1, s.2.1, 0⟩ else ⟨0, 0, 0, 1⟩

theorem partner_eq : ∀ s : Signs, βZ (tstar s) =
    ⟨px s + 2 * (ωH s).a0 + 4 * (pq s).a0, 2 * (ωH s).a1 + 4 * (pq s).a1,
      2 * (ωH s).a2 + 4 * (pq s).a2, 2 * (ωH s).a3 + 4 * (pq s).a3⟩ := by
  decide +kernel

theorem tstar_ne_zero : ∀ s : Signs, tstar s ≠ (0, 0, 0) := by decide

theorem nrdH_βZ_odd (t : Fin 2 × Fin 2 × Fin 2) : Odd (nrdH (βZ t)) := by
  refine ⟨2 * (t.2.2 : ℤ) ^ 2 + 2 * (t.2.1 : ℤ) * t.2.2 + 2 * (t.2.1 : ℤ) ^ 2 + 2 * (t.1 : ℤ) * t.2.2 +
    2 * (t.1 : ℤ) ^ 2 - t.2.2, ?_⟩
  simp only [nrdH, βZ]; ring

/-- `χ₀(1 + 2x_t) = (−1)^c` (TYZ L632–637), as in `chi0Rep`. -/
def chi0Z (t : Fin 2 × Fin 2 × Fin 2) : ℤ := (-1) ^ (t.2.2 : ℕ)

/-- The values of the test vector on the 8 classes sum to `0`, also against `χ₀`. -/
theorem sums_check : ∀ s : Signs,
    (∑ t : Fin 2 × Fin 2 × Fin 2, (if t = (0, 0, 0) ∨ t = tstar s then (-3 : ℤ) else 1)) = 0 ∧
    (∑ t : Fin 2 × Fin 2 × Fin 2, chi0Z t * (if t = (0, 0, 0) ∨ t = tstar s then (-3 : ℤ) else 1)) = 0 := by
  decide +kernel

end ZInQ.Contrib.T21Proof
