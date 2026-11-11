import ZInQKernel.RouteK.Redei.Entry
import ZInQKernel.RouteK.Redei.Kernel
import ZInQKernel.RouteK.Rank5b.Sec3.RedeiStatement
import ZInQKernel.RouteK.Rank.Statements

/-!
# Rédei's formula from the 4-rank statement (`docs/research/redei-plan.md` §3.2, step 8)

* `OddGClStatement`: the 4-rank statement `odd_gCl_iff` of `scratch/redei-plan/Probe.lean` §3.6
  (step 6, to be proved from steps 3–5), universally quantified over odd squarefree `n`: `g(n)` is
  odd iff the kernel of the Rédei matrix `redeiEntry n` is `{0, e_n}`.
* `gCl_dProd_eq_gBit`: for odd `d` and nonempty `B ⊆ d.primeFactors`, `OddGClStatement` gives
  `#2Cl(ℚ(√−d_B)) ≡ gBit d B (mod 2)`. Proof: `(d_B).primeFactors` is `B` (`redeiB_primeFactors`);
  `d_B ≡ 3 (mod 4)` iff `y(B) = 1` (`redeiB_mod4_iff`); on the vectors supported on
  `ramSet d_B`, the Rédei matrix is `L_B = lapl (aBit d) B` bordered by the column
  `z_B` (`zBit`, `R_{q2} = (2/q)`) exactly when `2 ∈ ramSet d_B`, i.e. when `y(B) = 0`
  (`redeiB_sum_entry`, with `legBit_prod` for the diagonal); so the kernel conditions agree
  (`redeiB_kernel_iff`), and `kernel_trivial_iff_redeiG` (step 7, with `recip_bits`) turns the
  latter into `redeiG = 1`.
* `redeiFormula_of_oddGClStatement : OddGClStatement → RedeiFormula`;
* `certifiedRankTYZRk_of_oddGClStatement`: `OddGClStatement` and `CertifiedRankTYZClRk` give
  `CertifiedRankTYZRk` (through `T5bCl_eq_T5b`).
-/

noncomputable section

namespace ZInQ.RouteK.Redei

open Finset ZInQ.RouteK.Rank5b ZInQ.RouteK.Rank5b.Sec3

/-- **The 4-rank statement** (`scratch/redei-plan/Probe.lean` §3.6, `odd_gCl_iff`; Rédei's theorem
in its 4-rank-0 form): for odd squarefree `n > 1`, `g(n) = #2Cl(ℚ(√−n))` is odd iff every vector
`e ∈ 𝔽₂^{ramSet n}` killed by the Rédei matrix is `0` or the vector `e_n` of `(√−n)` (`1` on the
primes of `n`, `0` at `2`).

The hypothesis `1 < n` is needed: for `n = 1` (`ℚ(i)`, trivial class group) `g(1) = 1` is odd,
while `e_1 = 0` and the nonzero vector supported at `2 ∈ ramSet 1` is killed by the (empty) Rédei
matrix. The plan only uses `n = d_B ≥ 3`. -/
def OddGClStatement : Prop :=
  ∀ (n : ℕ) [NeZero n], Odd n → Squarefree n → 1 < n →
    (Odd (gCl n) ↔ ∀ e : ramSet n → ZMod 2, (∀ q, ∑ p, redeiEntry n q p * e p = 0) →
      e = 0 ∨ e = fun p : ramSet n => if (p : ℕ) ∈ n.primeFactors then (1 : ZMod 2) else 0)

variable {d : ℕ}

theorem redeiB_prime (p : d.primeFactors) : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2

theorem redeiB_ne_two (hd : Odd d) (p : d.primeFactors) : (p : ℕ) ≠ 2 := by
  have := Selmer.odd_prime_of_mem_primeFactors hd p
  omega

/-- `(d_B).primeFactors = B`. -/
theorem redeiB_primeFactors (B : Finset d.primeFactors) :
    (dProd B).primeFactors = B.map (Function.Embedding.subtype _) := by
  have h : dProd B = ∏ p ∈ B.map (Function.Embedding.subtype _), p := by
    rw [Finset.prod_map]; rfl
  rw [h]
  refine Nat.primeFactors_prod fun p hp => ?_
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hp
  exact redeiB_prime q

theorem redeiB_mem_primeFactors {B : Finset d.primeFactors} {q : d.primeFactors} (hq : q ∈ B) :
    (q : ℕ) ∈ (dProd B).primeFactors := by
  rw [redeiB_primeFactors]
  exact Finset.mem_map_of_mem _ hq

theorem redeiB_mem_primeFactors_iff {B : Finset d.primeFactors} {p : ℕ} :
    p ∈ (dProd B).primeFactors ↔ ∃ q ∈ B, (q : ℕ) = p := by
  rw [redeiB_primeFactors, Finset.mem_map]
  rfl

theorem redeiB_two_not_mem (hd : Odd d) (B : Finset d.primeFactors) :
    2 ∉ (dProd B).primeFactors := by
  rw [redeiB_mem_primeFactors_iff]
  rintro ⟨q, -, hq⟩
  exact redeiB_ne_two hd q hq

theorem redeiB_odd (hd : Odd d) (B : Finset d.primeFactors) : Odd (dProd B) := by
  rw [Nat.odd_iff]
  by_contra h
  apply redeiB_two_not_mem hd B
  rw [Nat.mem_primeFactors]
  exact ⟨Nat.prime_two, by omega, NeZero.ne _⟩

theorem redeiB_squarefree (B : Finset d.primeFactors) : Squarefree (dProd B) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p _ q _ hpq => ?_)
    fun p _ => (redeiB_prime p).squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (redeiB_prime p) (redeiB_prime q)).2
    fun h => hpq (Subtype.val_injective h)

theorem redeiB_mem_ramSet {B : Finset d.primeFactors} {q : d.primeFactors} (hq : q ∈ B) :
    (q : ℕ) ∈ ramSet (dProd B) := by
  unfold ramSet
  split_ifs
  · exact redeiB_mem_primeFactors hq
  · exact Finset.mem_insert_of_mem (redeiB_mem_primeFactors hq)

theorem redeiB_two_mem_ramSet_iff (hd : Odd d) (B : Finset d.primeFactors) :
    2 ∈ ramSet (dProd B) ↔ ¬dProd B % 4 = 3 := by
  unfold ramSet
  split_ifs with h
  · exact ⟨fun h2 => absurd h2 (redeiB_two_not_mem hd B), fun h' => absurd h h'⟩
  · exact ⟨fun _ => h, fun _ => Finset.mem_insert_self _ _⟩

theorem redeiB_mem_ramSet_cases {B : Finset d.primeFactors} {p : ℕ} (hp : p ∈ ramSet (dProd B)) :
    p = 2 ∨ ∃ q ∈ B, (q : ℕ) = p := by
  unfold ramSet at hp
  split_ifs at hp
  · exact Or.inr (redeiB_mem_primeFactors_iff.1 hp)
  · rcases Finset.mem_insert.1 hp with h | h
    · exact Or.inl h
    · exact Or.inr (redeiB_mem_primeFactors_iff.1 h)

/-- `d_B ≡ 3 (mod 4)` iff `y(B) = Σ_{q∈B} y_q = 1` (`lam8_prod`, through `sum_yBit_eq`). -/
theorem redeiB_mod4_iff (hd : Odd d) (B : Finset d.primeFactors) :
    ∑ q ∈ B, yBit d q = 1 ↔ dProd B % 4 = 3 := by
  rw [sum_yBit_eq hd, ← ZMod.natCast_mod (dProd B) 8,
    show dProd B % 4 = 3 ↔ dProd B % 8 = 3 ∨ dProd B % 8 = 7 by omega]
  have h8 := Nat.mod_lt (dProd B) (show 8 > 0 by norm_num)
  generalize dProd B % 8 = m at h8 ⊢
  interval_cases m <;> decide

/-- `d_B > 1` for nonempty `B`. -/
theorem redeiB_one_lt {B : Finset d.primeFactors} (hB : B.Nonempty) : 1 < dProd B := by
  obtain ⟨q, hq⟩ := hB
  have h := redeiB_mem_primeFactors hq
  exact (Nat.prime_of_mem_primeFactors h).one_lt.trans_le (Nat.le_of_mem_primeFactors h)

/-- `d_B / q = Π_{k ∈ B, k ≠ q} k`. -/
theorem redeiB_div_eq {B : Finset d.primeFactors} {q : d.primeFactors} (hq : q ∈ B) :
    dProd B / q = ∏ k ∈ B.erase q, (k : ℕ) := by
  rw [dProd, ← Finset.mul_prod_erase B (fun k : d.primeFactors => (k : ℕ)) hq]
  exact Nat.mul_div_cancel_left _ (redeiB_prime q).pos

/-- The Rédei matrix on the columns `p ∈ B` is `L_B = lapl (aBit d) B`. -/
theorem redeiB_entry_eq_lapl (hd : Odd d) {B : Finset d.primeFactors} {q p : d.primeFactors}
    (hq : q ∈ B) :
    (if (p : ℕ) = 2 then legBit q 2
      else if (p : ℕ) = q then legBit q ((dProd B / q : ℕ) : ℤ) else legBit q (p : ℤ)) =
      lapl (aBit d) B q p := by
  rw [ite_eq_right (redeiB_ne_two hd p), lapl]
  by_cases hpq : p = q
  · subst hpq
    rw [ite_eq_left rfl, ite_eq_left rfl, redeiB_div_eq hq, Nat.cast_prod]
    have : Fact (p : ℕ).Prime := ⟨redeiB_prime p⟩
    rw [legBit_prod]
    · rfl
    · intro k hk
      exact natCast_zmod_ne_zero_of_prime_ne (redeiB_prime p) (redeiB_prime k)
        fun h => Finset.ne_of_mem_erase hk (Subtype.val_injective h).symm
  · rw [ite_eq_right fun h => hpq (Subtype.val_injective h), ite_eq_right (Ne.symm hpq)]
    rfl

/-- **The Rédei matrix in the bits**: for `q ∈ B` and any `F : ℕ → 𝔽₂`,
`Σ_{p ∈ ramSet d_B} R_{qp} F(p) = Σ_{p∈B} (L_B)_{qp} F(p) + [2 ∈ ramSet d_B] z_q F(2)`. -/
theorem redeiB_sum_entry (hd : Odd d) {B : Finset d.primeFactors} (F : ℕ → ZMod 2)
    {q : d.primeFactors} (hq : q ∈ B) :
    ∑ p : ramSet (dProd B), redeiEntry (dProd B) ⟨q, redeiB_mem_primeFactors hq⟩ p * F p =
      ∑ p ∈ B, lapl (aBit d) B q p * F p +
        (if dProd B % 4 = 3 then 0 else zBit d q * F 2) := by
  set f : ℕ → ZMod 2 := fun p => (if p = 2 then legBit q 2
      else if p = q then legBit q ((dProd B / q : ℕ) : ℤ) else legBit q (p : ℤ)) * F p with hf
  have h1 : ∑ p : ramSet (dProd B), redeiEntry (dProd B) ⟨q, redeiB_mem_primeFactors hq⟩ p * F p =
      ∑ p ∈ ramSet (dProd B), f p := Finset.sum_coe_sort _ f
  have h2 : ∑ p ∈ (dProd B).primeFactors, f p = ∑ p ∈ B, lapl (aBit d) B q p * F p := by
    rw [redeiB_primeFactors, Finset.sum_map]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hf, Function.Embedding.coe_subtype]
    rw [redeiB_entry_eq_lapl hd hq]
  rw [h1]
  unfold ramSet
  split_ifs with h3
  · rw [h2, add_zero]
  · rw [Finset.sum_insert (redeiB_two_not_mem hd B), h2, add_comm]
    simp only [hf]
    rfl

/-- **The two kernel conditions agree**: the kernel of the Rédei matrix of `ℚ(√−d_B)` is
`{0, e_{d_B}}` iff the kernel of `(L_B | z_B)` (the column `z_B` only when `y(B) = 0`) is the trivial
one. -/
theorem redeiB_kernel_iff (hd : Odd d) (B : Finset d.primeFactors) :
    (∀ e : ramSet (dProd B) → ZMod 2, (∀ q, ∑ p, redeiEntry (dProd B) q p * e p = 0) →
      e = 0 ∨ e = fun p : ramSet (dProd B) =>
        if (p : ℕ) ∈ (dProd B).primeFactors then (1 : ZMod 2) else 0) ↔
    (∀ (e : d.primeFactors → ZMod 2) (e₂ : ZMod 2), (∀ i ∉ B, e i = 0) →
        (∑ i ∈ B, yBit d i = 1 → e₂ = 0) →
        (∀ q ∈ B, ∑ p ∈ B, lapl (aBit d) B q p * e p + e₂ * zBit d q = 0) →
        e₂ = 0 ∧ ((∀ i ∈ B, e i = 0) ∨ (∀ i ∈ B, e i = 1))) := by
  rw [redeiB_mod4_iff hd]
  constructor
  · intro hP e e₂ heB hy heq
    set F : ℕ → ZMod 2 := fun p =>
      if p = 2 then e₂ else if h : p ∈ d.primeFactors then e ⟨p, h⟩ else 0 with hF
    have hFi : ∀ i : d.primeFactors, F i = e i := fun i => by
      simp only [hF, ite_eq_right (redeiB_ne_two hd i), dite_eq_left i.2]
    have hF2 : F 2 = e₂ := by simp [hF]
    have hE := hP (fun p => F p) (by
      rintro ⟨q, hq⟩
      obtain ⟨i, hi, rfl⟩ := redeiB_mem_primeFactors_iff.1 hq
      rw [redeiB_sum_entry hd F hi]
      simp only [hFi, hF2]
      split_ifs with h3
      · have := heq i hi
        rw [hy h3, zero_mul] at this
        exact this
      · rw [mul_comm]
        exact heq i hi)
    have he₂ : e₂ = 0 := by
      by_cases h3 : dProd B % 4 = 3
      · exact hy h3
      · have h2 := (redeiB_two_mem_ramSet_iff hd B).2 h3
        rcases hE with h | h
        · have := congrFun h ⟨2, h2⟩
          simpa [hF2] using this
        · have := congrFun h ⟨2, h2⟩
          simpa [hF2, redeiB_two_not_mem hd B] using this
    refine ⟨he₂, ?_⟩
    rcases hE with h | h
    · left
      intro i hi
      have := congrFun h ⟨i, redeiB_mem_ramSet hi⟩
      simpa [hFi] using this
    · right
      intro i hi
      have := congrFun h ⟨i, redeiB_mem_ramSet hi⟩
      simpa [hFi, redeiB_mem_primeFactors hi] using this
  · intro hS E hE
    set F : ℕ → ZMod 2 := fun p => if h : p ∈ ramSet (dProd B) then E ⟨p, h⟩ else 0 with hF
    have hEF : ∀ p : ramSet (dProd B), E p = F p := fun p => by simp [hF, p.2]
    have hF2 : dProd B % 4 = 3 → F 2 = 0 := fun h3 => by
      simp only [hF]
      rw [dite_eq_right]
      rw [redeiB_two_mem_ramSet_iff hd B]
      exact not_not.2 h3
    set e : d.primeFactors → ZMod 2 := fun i => if i ∈ B then F i else 0 with he
    obtain ⟨he₂, hc⟩ := hS e (F 2) (fun i hi => by simp [he, hi]) hF2 (fun q hq => by
      have h := hE ⟨q, redeiB_mem_primeFactors hq⟩
      simp only [hEF] at h
      rw [redeiB_sum_entry hd F hq] at h
      have hs : ∑ p ∈ B, lapl (aBit d) B q p * e p = ∑ p ∈ B, lapl (aBit d) B q p * F p :=
        Finset.sum_congr rfl fun p hp => by simp [he, hp]
      rw [hs]
      split_ifs at h with h3
      · rwa [hF2 h3, zero_mul, add_zero, ← add_zero (∑ p ∈ B, _)]
      · rwa [mul_comm])
    rcases hc with h | h
    · left
      funext p
      rw [hEF, Pi.zero_apply]
      rcases redeiB_mem_ramSet_cases p.2 with h2 | ⟨i, hi, hip⟩
      · rw [h2, he₂]
      · rw [← hip]
        have := h i hi
        simpa [he, hi] using this
    · right
      funext p
      rw [hEF]
      rcases redeiB_mem_ramSet_cases p.2 with h2 | ⟨i, hi, hip⟩
      · rw [h2, he₂, ite_eq_right (redeiB_two_not_mem hd B)]
      · rw [← hip, ite_eq_left (redeiB_mem_primeFactors hi)]
        have := h i hi
        simpa [he, hi] using this

/-- **Rédei's formula from the 4-rank statement**: for odd `d` and nonempty `B ⊆ d.primeFactors`,
`#2Cl(ℚ(√−d_B)) ≡ gBit d B (mod 2)`. -/
theorem gCl_dProd_eq_gBit (h : OddGClStatement) (hd : Odd d) {B : Finset d.primeFactors}
    (hB : B.Nonempty) : ((gCl (dProd B) : ℕ) : ZMod 2) = gBit d B := by
  have key : Odd (gCl (dProd B)) ↔ gBit d B = 1 := by
    rw [h (dProd B) (redeiB_odd hd B) (redeiB_squarefree B) (redeiB_one_lt hB),
      redeiB_kernel_iff hd B,
      kernel_trivial_iff_redeiG (recip_bits hd) hB]
    rfl
  rcases Nat.even_or_odd (gCl (dProd B)) with he | ho
  · rw [ZMod.natCast_eq_zero_iff_even.2 he]
    rcases redeiK_zmod2_cases (gBit d B) with h0 | h1
    · exact h0.symm
    · exact absurd (key.2 h1) (Nat.not_odd_iff_even.2 he)
  · rw [ZMod.natCast_eq_one_iff_odd.2 ho, key.1 ho]

/-- **Step 8**: the 4-rank statement implies Rédei's formula `RedeiFormula`. -/
theorem redeiFormula_of_oddGClStatement (h : OddGClStatement) : RedeiFormula :=
  fun _ hd _ _ hB _ => gCl_dProd_eq_gBit h hd hB

/-- Under the 4-rank statement, CR₃ in class-number form is CR₃^TYZ. -/
theorem certifiedRankTYZ_iff_of_oddGClStatement (h : OddGClStatement) :
    CertifiedRankTYZCl ↔ CertifiedRankTYZ :=
  certifiedRankTYZ_iff_of_redeiFormula (redeiFormula_of_oddGClStatement h)

/-- **The main-theorem consequence**: the 4-rank statement and CR₃^TYZ_Cl,Rk (Tian–Yuan–Zhang with
their own class numbers, and Gross–Zagier) give CR₃^TYZ,Rk, with no Rédei Prop. -/
theorem certifiedRankTYZRk_of_oddGClStatement (h : OddGClStatement)
    (hCl : Rank.CertifiedRankTYZClRk) : Rank.CertifiedRankTYZRk := fun d hd5 hsq hT =>
  hCl d hd5 hsq (by
    rw [T5bCl_eq_T5b (redeiFormula_of_oddGClStatement h) (Nat.odd_iff.2 (by omega)) hsq]
    exact hT)

end ZInQ.RouteK.Redei
