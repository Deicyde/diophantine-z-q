import Mathlib

/-!
# The `𝔽₂` linear algebra of S12's `par:simultaneous-matrices`

ELLIOT (supplement S12, `parity-frozen-4eaee875.tex` lines 543–683, Lemma
`par:simultaneous-matrices`). Vectors are functions `ℕ → 𝔽₂` indexed by primes and read on a
finite support `S`; `σ k i` stands for the symbol `[q_k/q_i]`.

* `KS σ S x i = Σ_{k ∈ S, k ≠ i} σ k i (x_k + x_i)`: the manuscript's `K` (tex L1038).
* `KSharp`: `K♯ = K + λaᵗ` (S12 L587).
* `sharp_targets` (S12 L590–604): with `K1_B = 0`, `aᵗ1 = 0`, `aᵗ1_B = 1` and
  `ker K♯ = ⟨1⟩`, the two targets `ker K = ⟨1, 1_B⟩` and `λ ∉ im K` hold.
* `sharp_ker_of_deleted` (S12 L606–613): `ker K♯ = ⟨1⟩` from the nonsingularity of the matrix
  with the `q₀` row and column deleted.
* `exists_toggle_injOn` (S12 L658–666): the Boolean-cube step. S12 argues with the determinant
  as a multilinear polynomial in the toggled diagonal bits; this file proves the same statement
  by a kernel argument (induction on the toggled set; ON THE SPOT proof of S12's claim, which is
  standard linear algebra).
* `block_injOn` (S12 L631–652): the nonsingularity of the deleted matrix
  `[[A, C], [Cᵗ, 0]]`, `1_Bᵗ A 1_B = 1`, with the columns of `C` equal to `e_b + e_{b*}`.
-/

namespace ZInQ.Manuscript.PoleS12

open Finset

/-! ### Elementary `𝔽₂` facts -/

theorem z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem z2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

/-! ### The matrix `K`, `K♯ = K + λaᵗ`, and dot products on a support -/

/-- `(Kx)_i = Σ_{k ∈ S, k ≠ i} σ_{k i} (x_k + x_i)` (tex L1038, S12 L274). -/
def KS (σ : ℕ → ℕ → ZMod 2) (S : Finset ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  ∑ k ∈ S.erase i, σ k i * (x k + x i)

/-- `aᵗx` on the support `S`. -/
def dotS (S : Finset ℕ) (a x : ℕ → ZMod 2) : ZMod 2 := ∑ k ∈ S, a k * x k

/-- `K♯x = Kx + λ (aᵗx)` (S12 L587). -/
def KSharp (σ : ℕ → ℕ → ZMod 2) (S : Finset ℕ) (lam a x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  KS σ S x i + lam i * dotS S a x

variable {σ : ℕ → ℕ → ZMod 2} {S : Finset ℕ}

theorem KS_add (x y : ℕ → ZMod 2) (i : ℕ) : KS σ S (x + y) i = KS σ S x i + KS σ S y i := by
  simp only [KS, Pi.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => by ring

theorem KS_smul (c : ZMod 2) (x : ℕ → ZMod 2) (i : ℕ) : KS σ S (c • x) i = c * KS σ S x i := by
  simp only [KS, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun k _ => by ring

theorem KS_const (c : ZMod 2) (i : ℕ) : KS σ S (fun _ => c) i = 0 := by
  simp [KS, z2_add_self]

theorem KS_congr {x y : ℕ → ZMod 2} (h : ∀ k ∈ S, x k = y k) {i : ℕ} (hi : i ∈ S) :
    KS σ S x i = KS σ S y i := by
  unfold KS
  refine sum_congr rfl fun k hk => ?_
  rw [h k (mem_of_mem_erase hk), h i hi]

theorem dotS_add (a x y : ℕ → ZMod 2) : dotS S a (x + y) = dotS S a x + dotS S a y := by
  simp only [dotS, Pi.add_apply, mul_add, sum_add_distrib]

theorem dotS_smul (a x : ℕ → ZMod 2) (c : ZMod 2) : dotS S a (c • x) = c * dotS S a x := by
  simp only [dotS, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun k _ => by ring

theorem dotS_const (a : ℕ → ZMod 2) (c : ZMod 2) :
    dotS S a (fun _ => c) = c * dotS S a (fun _ => 1) := by
  simp only [dotS, mul_sum]
  refine sum_congr rfl fun k _ => by ring

theorem dotS_congr {a x y : ℕ → ZMod 2} (h : ∀ k ∈ S, x k = y k) :
    dotS S a x = dotS S a y := by
  unfold dotS
  exact sum_congr rfl fun k hk => by rw [h k hk]

/-! ### Both targets from `ker K♯ = ⟨1⟩` (S12 L590–604) -/

/-- **S12 L590–604.** If `K1_B = 0`, `aᵗ1 = 0`, `aᵗ1_B = 1` and `ker K♯ = ⟨1⟩` (on `S`), then
`ker K = ⟨1, 1_B⟩` and `λ ∉ im K`. ELLIOT (supplement). -/
theorem sharp_targets {lam a b : ℕ → ZMod 2}
    (hb : ∀ i ∈ S, KS σ S b i = 0) (ha1 : dotS S a (fun _ => 1) = 0) (hab : dotS S a b = 1)
    (hsharp : ∀ x, (∀ i ∈ S, KSharp σ S lam a x i = 0) → ∃ c, ∀ i ∈ S, x i = c) :
    (∀ x, (∀ i ∈ S, KS σ S x i = 0) → ∃ c e : ZMod 2, ∀ i ∈ S, x i = c + e * b i) ∧
      ¬ ∃ x, ∀ i ∈ S, KS σ S x i = lam i := by
  constructor
  · intro x hx
    obtain ⟨c, hc⟩ := hsharp (x + dotS S a x • b) fun i hi => by
      rw [KSharp, KS_add, KS_smul, hx i hi, hb i hi, dotS_add, dotS_smul, hab, mul_one,
        z2_add_self, mul_zero, mul_zero, add_zero, add_zero]
    refine ⟨c, dotS S a x, fun i hi => ?_⟩
    have := hc i hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this, add_assoc, z2_add_self, add_zero]
  · rintro ⟨x, hx⟩
    set d := dotS S a x
    obtain ⟨c, hc⟩ := hsharp (x + d • b + b) fun i hi => by
      rw [KSharp, KS_add, KS_add, KS_smul, hx i hi, hb i hi, dotS_add, dotS_add, dotS_smul, hab]
      have : d + d * 1 + 1 = 1 := by rw [mul_one, z2_add_self, zero_add]
      rw [this]; simp [z2_add_self]
    have h1 : dotS S a (x + d • b + b) = 1 := by
      rw [dotS_add, dotS_add, dotS_smul, hab, mul_one, z2_add_self, zero_add]
    rw [dotS_congr (y := fun _ => c) hc, dotS_const, ha1, mul_zero] at h1
    exact zero_ne_one h1

/-! ### `ker K♯ = ⟨1⟩` from the deleted matrix (S12 L606–613) -/

/-- **S12 L606–613.** If `aᵗ1 = 0` and every `x` with `x_{q₀} = 0` killed by `K♯` off the `q₀`
row vanishes on `S`, then `ker K♯ = ⟨1⟩`. ELLIOT (supplement). -/
theorem sharp_ker_of_deleted {lam a : ℕ → ZMod 2} {q₀ : ℕ}
    (ha1 : dotS S a (fun _ => 1) = 0)
    (hdel : ∀ x, x q₀ = 0 → (∀ i ∈ S.erase q₀, KSharp σ S lam a x i = 0) → ∀ i ∈ S, x i = 0) :
    ∀ x, (∀ i ∈ S, KSharp σ S lam a x i = 0) → ∃ c, ∀ i ∈ S, x i = c := by
  intro x hx
  refine ⟨x q₀, fun i hi => ?_⟩
  have h := hdel (x + fun _ => x q₀) (by simp [z2_add_self]) (fun i hi' => by
    have hi := mem_of_mem_erase hi'
    rw [KSharp, KS_add, KS_const, dotS_add, dotS_const, ha1, mul_zero, add_zero, add_zero]
    exact hx i hi) i hi
  simp only [Pi.add_apply] at h
  calc x i = x i + (x i + x q₀) := by rw [h, add_zero]
    _ = x q₀ := by rw [← add_assoc, z2_add_self, zero_add]

/-! ### Matrices on a finite support, and the Boolean-cube step (S12 L658–666) -/

/-- `(Nx)_i = Σ_{k ∈ U} N_{ik} x_k`. -/
def mulS (N : ℕ → ℕ → ZMod 2) (U : Finset ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  ∑ k ∈ U, N i k * x k

/-- The matrix `(N_{ik})_{i,k ∈ U}` is nonsingular. -/
def InjOnS (N : ℕ → ℕ → ZMod 2) (U : Finset ℕ) : Prop :=
  ∀ x, (∀ i ∈ U, mulS N U x i = 0) → ∀ i ∈ U, x i = 0

/-- `N + diag(d)`. -/
def addDiag (N : ℕ → ℕ → ZMod 2) (d : ℕ → ZMod 2) : ℕ → ℕ → ZMod 2 :=
  fun i k => N i k + if i = k then d i else 0

theorem mulS_congr {N : ℕ → ℕ → ZMod 2} {U : Finset ℕ} {x y : ℕ → ZMod 2}
    (h : ∀ k ∈ U, x k = y k) (i : ℕ) : mulS N U x i = mulS N U y i :=
  sum_congr rfl fun k hk => by rw [h k hk]

theorem injOnS_congr {N N' : ℕ → ℕ → ZMod 2} {U : Finset ℕ}
    (h : ∀ i ∈ U, ∀ k ∈ U, N i k = N' i k) (hN : InjOnS N U) : InjOnS N' U := by
  intro x hx
  refine hN x fun i hi => ?_
  rw [← hx i hi]
  exact sum_congr rfl fun k hk => by rw [h i hi k hk]

theorem mulS_addDiag (N : ℕ → ℕ → ZMod 2) (d : ℕ → ZMod 2) (U : Finset ℕ) (x : ℕ → ZMod 2)
    {i : ℕ} (hi : i ∈ U) : mulS (addDiag N d) U x i = mulS N U x i + d i * x i := by
  simp only [mulS, addDiag, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq, if_pos hi]

theorem mulS_add (N : ℕ → ℕ → ZMod 2) (U : Finset ℕ) (x y : ℕ → ZMod 2) (i : ℕ) :
    mulS N U (x + y) i = mulS N U x i + mulS N U y i := by
  simp only [mulS, Pi.add_apply, mul_add, sum_add_distrib]

theorem mulS_insert_of_zero (N : ℕ → ℕ → ZMod 2) {U : Finset ℕ} {j : ℕ} (hj : j ∉ U)
    {x : ℕ → ZMod 2} (hx : x j = 0) (i : ℕ) : mulS N (insert j U) x i = mulS N U x i := by
  rw [mulS, sum_insert hj, hx, mul_zero, zero_add]; rfl

/-- One toggle step: if `N` is nonsingular on `U` and `j ∉ U`, then `N` or `N + e_j e_jᵗ` is
nonsingular on `U ∪ {j}`. -/
theorem toggle_step {N : ℕ → ℕ → ZMod 2} {U : Finset ℕ} {j : ℕ} (hj : j ∉ U)
    (hN : InjOnS N U) :
    ∃ t : ZMod 2, InjOnS (addDiag N (fun i => if i = j then t else 0)) (insert j U) := by
  classical
  -- rows in `U` are not affected by a toggle at `j`
  have hrow : ∀ (t : ZMod 2) (x : ℕ → ZMod 2) (i : ℕ), i ∈ U →
      mulS (addDiag N (fun i => if i = j then t else 0)) (insert j U) x i =
        mulS N (insert j U) x i := by
    intro t x i hi
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    rw [mulS_addDiag _ _ _ _ (mem_insert_of_mem hi), if_neg hne, zero_mul, add_zero]
  -- a vector with `x_j = 0` killed by the rows of `U` vanishes
  have key : ∀ x, (∀ i ∈ U, mulS N (insert j U) x i = 0) → x j = 0 →
      ∀ i ∈ insert j U, x i = 0 := by
    intro x hx hxj i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact hxj
    refine hN x (fun i' hi' => ?_) i hi
    rw [← mulS_insert_of_zero _ hj hxj]
    exact hx i' hi'
  by_cases h0 : InjOnS (addDiag N (fun i => if i = j then (0 : ZMod 2) else 0)) (insert j U)
  · exact ⟨0, h0⟩
  refine ⟨1, fun x1 hx1 => ?_⟩
  simp only [InjOnS, not_forall] at h0
  obtain ⟨x0, hx0, i0, hi0, hx0i⟩ := h0
  have hx0U : ∀ i ∈ U, mulS N (insert j U) x0 i = 0 := fun i hi => by
    rw [← hrow 0 x0 i hi]; exact hx0 i (mem_insert_of_mem hi)
  have hx1U : ∀ i ∈ U, mulS N (insert j U) x1 i = 0 := fun i hi => by
    rw [← hrow 1 x1 i hi]; exact hx1 i (mem_insert_of_mem hi)
  have hx0j : x0 j = 1 := by
    rcases z2_cases (x0 j) with h | h
    · exact absurd (key x0 hx0U h i0 hi0) hx0i
    · exact h
  rcases z2_cases (x1 j) with hx1j | hx1j
  · exact key x1 hx1U hx1j
  exfalso
  have hy := key (x0 + x1) (fun i hi => by rw [mulS_add, hx0U i hi, hx1U i hi, add_zero])
    (by simp [hx0j, hx1j, z2_add_self])
  have heq : ∀ k ∈ insert j U, x1 k = x0 k := fun k hk => by
    have := hy k hk
    simp only [Pi.add_apply] at this
    calc x1 k = x0 k + x1 k + x0 k := by rw [add_comm (x0 k), add_assoc, z2_add_self, add_zero]
      _ = x0 k := by rw [this, zero_add]
  have e0 := hx0 j (mem_insert_self j U)
  have e1 := hx1 j (mem_insert_self j U)
  rw [mulS_addDiag _ _ _ _ (mem_insert_self j U), if_pos rfl, zero_mul, add_zero] at e0
  rw [mulS_addDiag _ _ _ _ (mem_insert_self j U), if_pos rfl, mulS_congr heq, e0, hx1j] at e1
  simp at e1

/-- **The Boolean-cube step** (S12 L658–666). If `N` is nonsingular on `U₀` and `T` is disjoint
from `U₀`, some diagonal toggle `d` supported on `T` makes `N + diag(d)` nonsingular on `U₀ ∪ T`.
ELLIOT (supplement) for the statement; S12 proves it with the determinant as a multilinear
polynomial in the toggles, whose top coefficient is `det N|_{U₀} = 1`. The proof here is a kernel
argument (ON THE SPOT, standard linear algebra). -/
theorem exists_toggle_injOn {N : ℕ → ℕ → ZMod 2} {U₀ : Finset ℕ} (hN : InjOnS N U₀)
    (T : Finset ℕ) (hT : Disjoint U₀ T) :
    ∃ d : ℕ → ZMod 2, (∀ i, i ∉ T → d i = 0) ∧ InjOnS (addDiag N d) (U₀ ∪ T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, fun _ _ => rfl, ?_⟩
    rw [union_empty]
    refine injOnS_congr (fun i _ k _ => ?_) hN
    simp [addDiag]
  | insert j T hjT ih =>
    have hT' : Disjoint U₀ T := disjoint_of_subset_right (subset_insert _ _) hT
    obtain ⟨d, hd, hinj⟩ := ih hT'
    have hjU : j ∉ U₀ ∪ T := by
      rw [mem_union, not_or]
      exact ⟨fun h => disjoint_left.mp hT h (mem_insert_self _ _), hjT⟩
    obtain ⟨t, ht⟩ := toggle_step hjU hinj
    refine ⟨fun i => d i + if i = j then t else 0, fun i hi => ?_, ?_⟩
    · have hiT : i ∉ T := fun h => hi (mem_insert_of_mem h)
      have hij : i ≠ j := fun h => hi (h ▸ mem_insert_self _ _)
      show d i + (if i = j then t else 0) = 0
      rw [hd i hiT, if_neg hij, add_zero]
    · rw [show U₀ ∪ insert j T = insert j (U₀ ∪ T) by
        ext x; simp only [mem_union, mem_insert]; tauto]
      refine injOnS_congr (fun i _ k _ => ?_) ht
      simp only [addDiag]
      split_ifs <;> ring

/-! ### The matrix of `K♯` with the `q₀` row and column deleted -/

/-- The matrix of `K♯` on a support `U` (without `q₀`), with the `q₀` symbols `cq i = σ q₀ i`
moved to the diagonal: `N_{ik} = [i = k](Σ_{k' ∈ U, k' ≠ i} σ_{k' i} + cq_i) + [i ≠ k] σ_{k i} +
λ_i a_k`. -/
def NMat (σ : ℕ → ℕ → ZMod 2) (U : Finset ℕ) (cq lam a : ℕ → ZMod 2) : ℕ → ℕ → ZMod 2 :=
  fun i k => (if i = k then (∑ k' ∈ U.erase i, σ k' i) + cq i else σ k i) + lam i * a k

theorem mulS_NMat (U : Finset ℕ) (cq lam a x : ℕ → ZMod 2) {i : ℕ} (hi : i ∈ U) :
    mulS (NMat σ U cq lam a) U x i = KS σ U x i + cq i * x i + lam i * dotS U a x := by
  classical
  simp only [mulS, NMat, add_mul, sum_add_distrib, KS, dotS, mul_sum, mul_assoc]
  rw [← add_sum_erase _ _ hi, if_pos rfl]
  have h : ∑ k ∈ U.erase i, (if i = k then (∑ k' ∈ U.erase i, σ k' i) + cq i else σ k i) * x k =
      ∑ k ∈ U.erase i, σ k i * x k :=
    sum_congr rfl fun k hk => by rw [if_neg (Ne.symm (ne_of_mem_erase hk))]
  rw [h]
  simp only [mul_add, sum_add_distrib, ← sum_mul]
  ring

/-- **Deleting `q₀`.** For `x` with `x_{q₀} = 0`, the rows of `K♯` on `insert q₀ U` other than
`q₀` are the rows of `NMat σ U (σ q₀ ·)`. -/
theorem KSharp_eq_mulS {U : Finset ℕ} {q₀ : ℕ} (hq₀ : q₀ ∉ U) (lam a : ℕ → ZMod 2)
    {x : ℕ → ZMod 2} (hx : x q₀ = 0) {i : ℕ} (hi : i ∈ U) :
    KSharp σ (insert q₀ U) lam a x i = mulS (NMat σ U (fun i => σ q₀ i) lam a) U x i := by
  rw [mulS_NMat U _ lam a x hi, KSharp]
  have hne : q₀ ≠ i := fun h => hq₀ (h ▸ hi)
  have h1 : KS σ (insert q₀ U) x i = KS σ U x i + σ q₀ i * x i := by
    unfold KS
    rw [erase_insert_of_ne hne, sum_insert (fun h => hq₀ (mem_of_mem_erase h)), hx, zero_add,
      add_comm]
  have h2 : dotS (insert q₀ U) a x = dotS U a x := by
    unfold dotS
    rw [sum_insert hq₀, hx, mul_zero, zero_add]
  rw [h1, h2]

/-! ### The nonsingular block (S12 L606–652) -/

/-- **The deleted matrix is nonsingular** (S12 L631–652, the block `[[A, C], [Cᵗ, 0]]`). Here `B`
is the support of `β`, `b* ∈ B`, the auxiliary primes are `g b` for `b ∈ B ∖ {b*}`, the column
of `C` at `g b` is `e_b + e_{b*}` (tex L1044), `a = e_{b*}` on `U₀ = B ∪ I`, the `I`–`I` symbols
vanish, `λ = cq = 0` on `I`, `cq_b = Σ_{i ∈ I} [q_i/q_b]` (S12 L620, the prescription of
`[q₀/q_b]`) and `Σ_B λ = 1` (S12 L561). ELLIOT (supplement). -/
theorem block_injOn {B : Finset ℕ} {bs : ℕ} (hbs : bs ∈ B) {g : ℕ → ℕ}
    (hg : Set.InjOn g (B.erase bs)) (hdisj : Disjoint B ((B.erase bs).image g))
    (cq lam : ℕ → ZMod 2)
    (h1 : ∀ b ∈ B.erase bs, ∀ b' ∈ B,
      σ b' (g b) = (if b' = b then 1 else 0) + (if b' = bs then 1 else 0))
    (h2 : ∀ b ∈ B.erase bs, ∀ b'' ∈ B.erase bs, b'' ≠ b → σ (g b'') (g b) = 0)
    (h3 : ∀ b ∈ B.erase bs, ∀ b' ∈ B, σ (g b) b' = σ b' (g b))
    (h4 : ∀ b ∈ B.erase bs, lam (g b) = 0 ∧ cq (g b) = 0)
    (h6 : ∀ b ∈ B, cq b = ∑ k ∈ (B.erase bs).image g, σ k b)
    (h7 : ∑ b ∈ B, lam b = 1) :
    InjOnS (NMat σ (B ∪ (B.erase bs).image g) cq lam (fun k => if k = bs then 1 else 0))
      (B ∪ (B.erase bs).image g) := by
  classical
  set I := (B.erase bs).image g with hI
  set U := B ∪ I with hU
  intro x hx
  have hbsU : bs ∈ U := mem_union_left _ hbs
  have hdot : dotS U (fun k => if k = bs then 1 else 0) x = x bs := by
    simp only [dotS, ite_mul, one_mul, zero_mul, sum_ite_eq', if_pos hbsU]
  have hgI : ∀ b ∈ B.erase bs, g b ∈ I := fun b hb => mem_image_of_mem g hb
  have hgB : ∀ b ∈ B.erase bs, g b ∉ B := fun b hb h =>
    disjoint_left.mp hdisj h (hgI b hb)
  -- sums of the column pattern
  have hcol : ∀ b ∈ B.erase bs, ∀ f : ℕ → ZMod 2,
      ∑ b' ∈ B, σ b' (g b) * f b' = f b + f bs := by
    intro b hb f
    rw [sum_congr rfl fun b' hb' => by rw [h1 b hb b' hb']]
    simp only [add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq',
      if_pos (mem_of_mem_erase hb), if_pos hbs]
  -- Step 1: the `I` rows make `x` constant on `B`
  have hconst : ∀ b ∈ B, x b = x bs := by
    intro b hb
    by_cases hbb : b = bs
    · rw [hbb]
    have hb' : b ∈ B.erase bs := mem_erase.mpr ⟨hbb, hb⟩
    have hrow := hx (g b) (mem_union_right _ (hgI b hb'))
    rw [mulS_NMat U cq _ _ x (mem_union_right _ (hgI b hb')), (h4 b hb').1, (h4 b hb').2,
      zero_mul, zero_mul, add_zero, add_zero] at hrow
    have hKS : KS σ U x (g b) = x b + x bs := by
      unfold KS
      rw [hU, erase_union_distrib, erase_eq_of_notMem (hgB b hb'), sum_union
        (disjoint_of_subset_right (erase_subset _ _) hdisj)]
      have hz : ∑ k ∈ I.erase (g b), σ k (g b) * (x k + x (g b)) = 0 := by
        refine sum_eq_zero fun k hk => ?_
        obtain ⟨b'', hb'', rfl⟩ := mem_image.mp (mem_of_mem_erase hk)
        have : b'' ≠ b := fun h => (ne_of_mem_erase hk) (h ▸ rfl)
        rw [h2 b hb' b'' hb'' this, zero_mul]
      rw [hz, add_zero, hcol b hb' (fun k => x k + x (g b))]
      ring_nf
      rw [show x (g b) * 2 = 0 by
        rw [show (2 : ZMod 2) = 0 from rfl, mul_zero], add_zero]
    rw [hKS] at hrow
    calc x b = x b + x bs + x bs := by rw [add_assoc, z2_add_self, add_zero]
      _ = x bs := by rw [hrow, zero_add]
  -- the `B` rows
  have hBrow : ∀ b ∈ B, ∑ k ∈ I, σ k b * x k + lam b * x bs = 0 := by
    intro b hb
    have hrow := hx b (mem_union_left _ hb)
    rw [mulS_NMat U cq _ _ x (mem_union_left _ hb), hdot] at hrow
    have hKS : KS σ U x b = ∑ k ∈ I, σ k b * x k + cq b * x b := by
      unfold KS
      have hbI : b ∉ I := fun h => disjoint_left.mp hdisj hb h
      rw [hU, erase_union_distrib, erase_eq_of_notMem hbI,
        sum_union (disjoint_of_subset_left (erase_subset _ _) hdisj)]
      have hz : ∑ k ∈ B.erase b, σ k b * (x k + x b) = 0 :=
        sum_eq_zero fun k hk => by
          rw [hconst k (mem_of_mem_erase hk), hconst b hb, z2_add_self, mul_zero]
      rw [hz, zero_add, h6 b hb]
      simp only [mul_add, sum_add_distrib, sum_mul]
    rw [hKS] at hrow
    calc ∑ k ∈ I, σ k b * x k + lam b * x bs
        = ∑ k ∈ I, σ k b * x k + cq b * x b + cq b * x b + lam b * x bs := by
          rw [add_assoc (∑ k ∈ I, σ k b * x k), z2_add_self, add_zero]
      _ = 0 := hrow
  -- summing the `B` rows gives `x_{b*} = 0`
  have hbs0 : x bs = 0 := by
    have hsum := sum_congr rfl hBrow
    rw [sum_add_distrib, ← sum_mul, h7, one_mul, sum_comm] at hsum
    have hz : ∑ k ∈ I, ∑ b ∈ B, σ k b * x k = 0 := by
      rw [hI, sum_image fun a ha b hb h => hg ha hb h]
      refine sum_eq_zero fun b'' hb'' => ?_
      rw [← sum_mul, sum_congr rfl fun b' hb' => h3 b'' hb'' b' hb']
      have := hcol b'' hb'' (fun _ => 1)
      simp only [mul_one] at this
      rw [this, z2_add_self, zero_mul]
    rw [hz, zero_add] at hsum
    simpa using hsum
  intro i hi
  rcases mem_union.mp hi with hiB | hiI
  · rw [hconst i hiB, hbs0]
  · obtain ⟨b, hb, rfl⟩ := mem_image.mp hiI
    have hrow := hBrow b (mem_of_mem_erase hb)
    rw [hbs0, mul_zero, add_zero, hI, sum_image fun a ha b hb h => hg ha hb h] at hrow
    rw [sum_congr rfl fun b'' hb'' => by
      rw [h3 b'' hb'' b (mem_of_mem_erase hb), h1 b'' hb'' b (mem_of_mem_erase hb)]] at hrow
    simp only [add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq,
      if_pos hb, if_neg (show bs ∉ B.erase bs from notMem_erase _ _)] at hrow
    simpa [if_neg (ne_of_mem_erase hb)] using hrow

end ZInQ.Manuscript.PoleS12
