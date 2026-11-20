import ZInQKernel.Contrib.OneProof.PoleS12.Primes

/-!
# `MatrixConditions` for one support, from the symbol choices (S12 L581–652)

`mc_of_choice`: for the support `S = {q₀} ∪ B ∪ I ∪ J'` (`J' = ∅` for `n`, `J' = J` for `nθ`)
with the symbol pattern of S12's `par:simultaneous-matrices` and a nonsingular deleted matrix,
`MatrixConditions (∏ S) β` holds. ELLIOT (supplement): the steps are S12 L581–604 (`K♯`, `T`),
L606–613 (deletion), L622–629 (`K1_B = 0` on both supports).
-/

namespace ZInQ.Manuscript.PoleS12

open Finset ZInQ.Manuscript.PoleRC

/-- `λ_i = [3/q_i]`. -/
noncomputable def lamS (i : ℕ) : ZMod 2 := lsym 3 i

theorem lsym_three_of_one {k : ℕ} (hk : k.Prime) (h : k % 12 = 1) : lsym 3 k = 0 := by
  have := Fact.mk hk
  rw [lsym_three k (by omega) (by omega), if_neg (by omega), if_neg (by omega), add_zero]

/-- `K 1_B` at a row outside `B` is the sum of the symbols of `B`. -/
theorem KS_ind_notMem {S B : Finset ℕ} (hBS : B ⊆ S) {i : ℕ} (hiB : i ∉ B) :
    KS lsymS S (fun k => if k ∈ B then 1 else 0) i = ∑ k ∈ B, lsymS k i := by
  classical
  simp only [KS, if_neg hiB, add_zero, mul_ite, mul_one, mul_zero]
  rw [sum_ite_mem]
  congr 1
  ext k
  simp only [mem_inter, mem_erase]
  exact ⟨fun h => h.2, fun h => ⟨⟨fun hk => hiB (hk ▸ h), hBS h⟩, h⟩⟩

theorem mc_of_choice {β : ℕ} {B I J' : Finset ℕ} {bs q₀ : ℕ} {g : ℕ → ℕ}
    (hB : B = β.primeFactors) (hβ0 : β ≠ 0)
    (hprime : ∀ k ∈ insert q₀ (B ∪ I ∪ J'), Odd3 k)
    (hBI : Disjoint B I) (hBJ : Disjoint B J') (hIJ : Disjoint I J') (hq₀ : q₀ ∉ B ∪ I ∪ J')
    (hbs : bs ∈ B) (hI : I = (B.erase bs).image g) (hg : Set.InjOn g (B.erase bs))
    (hI1 : ∀ k ∈ I, k % 12 = 1) (hq₀7 : q₀ % 12 = 7)
    (hcol : ∀ b ∈ B.erase bs, ∀ b' ∈ B,
      lsym (g b : ℤ) b' = (if b' = b then 1 else 0) + (if b' = bs then 1 else 0))
    (hBJs : ∀ j ∈ J', ∑ b ∈ B, lsym (b : ℤ) j = 0)
    (hJB : ∀ b ∈ B, ∑ j ∈ J', lsym (j : ℤ) b = 0)
    (hβ4 : ∑ b ∈ B, lsym (-1) b = 0)
    (hq₀B : ∀ b ∈ B, lsym (q₀ : ℤ) b = ∑ k ∈ I, lsym (k : ℤ) b)
    (hinj : InjOnS (NMat lsymS (B ∪ I ∪ J') (fun i => lsymS q₀ i) lamS
      (fun k => if k = bs then 1 else 0)) (B ∪ I ∪ J')) :
    MatrixConditions (∏ k ∈ insert q₀ (B ∪ I ∪ J'), k) β := by
  classical
  set U := B ∪ I ∪ J' with hU
  set S := insert q₀ U with hS
  have hSpf : (∏ k ∈ S, k).primeFactors = S :=
    Nat.primeFactors_prod fun p hp => (hprime p hp).1
  have hBU : B ⊆ U := fun k hk => mem_union_left _ (mem_union_left _ hk)
  have hBS : B ⊆ S := fun k hk => mem_insert_of_mem (hBU hk)
  have hdvd : ∀ k ∈ S, (k ∣ β ↔ k ∈ B) := by
    intro k hk
    rw [hB, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨(hprime k hk).1, h, hβ0⟩, fun h => h.2.1⟩
  have hq₀B' : q₀ ∉ B := fun h => hq₀ (hBU h)
  have hq₀S : q₀ ∈ S := mem_insert_self _ _
  have hbsS : bs ∈ S := hBS hbs
  have hbsq : bs ≠ q₀ := fun h => hq₀B' (h ▸ hbs)
  -- the rows of `I` in `B`
  have hrowI : ∀ k ∈ I, ∑ b ∈ B, lsym (k : ℤ) b = 0 := by
    intro k hk
    rw [hI] at hk
    obtain ⟨b'', hb'', rfl⟩ := mem_image.mp hk
    rw [sum_congr rfl fun b' hb' => hcol b'' hb'' b' hb']
    simp only [sum_add_distrib, sum_ite_eq', if_pos (mem_of_mem_erase hb''), if_pos hbs]
    exact z2_add_self 1
  have hrecI : ∀ k ∈ I, ∀ b ∈ S, b ≠ k → lsymS b k = lsym (k : ℤ) b := by
    intro k hk b hb hbk
    exact lsym_recip_one (hprime k (mem_insert_of_mem (mem_union_left _ (mem_union_right _ hk)))).1
      (hprime b hb).1 (by have := hI1 k hk; omega) (hprime b hb).2.1 (Ne.symm hbk)
  -- `K 1_B = 0` on `S` (S12 L622–629)
  have hKb : ∀ i ∈ S, KS lsymS S (fun k => if k ∣ β then 1 else 0) i = 0 := by
    intro i hi
    rw [KS_congr (y := fun k => if k ∈ B then 1 else 0)
      (fun k hk => by simp only [hdvd k hk]) hi]
    by_cases hiB : i ∈ B
    · -- a row of `B`
      have hiI : i ∉ I := fun h => disjoint_left.mp hBI hiB h
      have hiJ : i ∉ J' := fun h => disjoint_left.mp hBJ hiB h
      have hqi : q₀ ≠ i := fun h => hq₀B' (h ▸ hiB)
      have hE : S.erase i = insert q₀ (B.erase i ∪ I ∪ J') := by
        rw [hS, erase_insert_of_ne hqi, hU, erase_union_distrib, erase_union_distrib,
          erase_eq_of_notMem hiI, erase_eq_of_notMem hiJ]
      have hq₀' : q₀ ∉ B.erase i ∪ I ∪ J' := fun h => hq₀ (by
        rcases mem_union.mp h with h | h
        · rcases mem_union.mp h with h | h
          · exact mem_union_left _ (mem_union_left _ (mem_of_mem_erase h))
          · exact mem_union_left _ (mem_union_right _ h)
        · exact mem_union_right _ h)
      have hd1 : Disjoint (B.erase i) I := disjoint_of_subset_left (erase_subset _ _) hBI
      have hd2 : Disjoint (B.erase i ∪ I) J' :=
        disjoint_union_left.mpr ⟨disjoint_of_subset_left (erase_subset _ _) hBJ, hIJ⟩
      unfold KS
      simp only [if_pos hiB]
      have hsplit : ∀ k, lsymS k i * ((if k ∈ B then (1 : ZMod 2) else 0) + 1) =
          lsymS k i + (if k ∈ B then lsymS k i else 0) := by
        intro k; split_ifs <;> ring
      rw [sum_congr rfl fun k _ => hsplit k, sum_add_distrib, sum_ite_mem, hE,
        sum_insert hq₀', sum_union hd2, sum_union hd1]
      have hinter : insert q₀ (B.erase i ∪ I ∪ J') ∩ B = B.erase i := by
        ext k
        simp only [mem_inter, mem_insert, mem_union, mem_erase]
        constructor
        · rintro ⟨h, hkB⟩
          refine ⟨fun hk => ?_, hkB⟩
          rcases h with h | ((h | h) | h)
          · exact hq₀B' (h ▸ hkB)
          · exact h.1 hk
          · exact disjoint_left.mp hBI hkB h
          · exact disjoint_left.mp hBJ hkB h
        · rintro ⟨hk, hkB⟩
          exact ⟨Or.inr (Or.inl (Or.inl ⟨hk, hkB⟩)), hkB⟩
      rw [hinter]
      simp only [lsymS]
      rw [hq₀B i hiB, hJB i hiB]
      have : ∀ x y : ZMod 2, x + (y + x + 0) + y = 0 := by
        intro x y; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
      exact this _ _
    · rw [KS_ind_notMem hBS hiB]
      rcases mem_insert.mp hi with rfl | hi'
      · -- the row of `q₀`
        have hq₀4 : i % 4 = 3 := by omega
        have := Fact.mk (hprime i hq₀S).1
        have hrec : ∀ b ∈ B, lsymS b i = lsym (i : ℤ) b + lsym (-1) b := by
          intro b hb
          have := Fact.mk (hprime b (hBS hb)).1
          rw [lsymS, lsym_recip b i (hprime b (hBS hb)).2.1 (by omega)
            (fun h => hq₀B' (h ▸ hb)), lsym_neg_one i, if_pos hq₀4, mul_one]
        rw [sum_congr rfl hrec, sum_add_distrib, hβ4, add_zero, sum_congr rfl hq₀B, sum_comm]
        exact sum_eq_zero hrowI
      · rcases mem_union.mp hi' with h | hiJ
        · rcases mem_union.mp h with h | hiI
          · exact absurd h hiB
          · rw [sum_congr rfl fun b hb => hrecI i hiI b (hBS hb) (fun h => hiB (h ▸ hb))]
            exact hrowI i hiI
        · exact hBJs i hiJ
  -- the rank-one correction and the deleted matrix
  set a : ℕ → ZMod 2 := fun k => (if k = q₀ then 1 else 0) + (if k = bs then 1 else 0) with ha
  have ha1 : dotS S a (fun _ => 1) = 0 := by
    simp only [dotS, ha, mul_one, sum_add_distrib, sum_ite_eq', if_pos hq₀S, if_pos hbsS]
    exact z2_add_self 1
  have hab : dotS S a (fun k => if k ∣ β then 1 else 0) = 1 := by
    simp only [dotS, ha, add_mul, ite_mul, one_mul, zero_mul, sum_add_distrib, sum_ite_eq',
      if_pos hq₀S, if_pos hbsS, if_pos (Nat.mem_primeFactors.mp (hB ▸ hbs)).2.1,
      if_neg (fun h => hq₀B' ((hdvd q₀ hq₀S).mp h)), zero_add]
  have hdel : ∀ x, x q₀ = 0 → (∀ i ∈ S.erase q₀, KSharp lsymS S lamS a x i = 0) →
      ∀ i ∈ S, x i = 0 := by
    intro x hx0 hrows
    rw [hS, erase_insert hq₀] at hrows
    have hU0 : ∀ i ∈ U, x i = 0 := by
      refine (injOnS_congr (N' := NMat lsymS U (fun i => lsymS q₀ i) lamS a)
        (fun i _ k hk => ?_) hinj) x fun i hi => ?_
      · simp only [NMat, ha]
        have hkq : k ≠ q₀ := fun h => hq₀ (h ▸ hk)
        rw [if_neg hkq, zero_add]
      · rw [← KSharp_eq_mulS hq₀ lamS a hx0 hi]
        exact hrows i hi
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact hx0
    · exact hU0 i hi
  obtain ⟨hK, hlam⟩ := sharp_targets hKb ha1 hab (sharp_ker_of_deleted ha1 hdel)
  refine matrixConditions_of_KS ?_ ?_ ?_ ?_ ?_ <;> rw [hSpf]
  · exact ⟨bs, hbsS, (Nat.mem_primeFactors.mp (hB ▸ hbs)).2.1⟩
  · exact ⟨q₀, hq₀S, fun h => hq₀B' ((hdvd q₀ hq₀S).mp h)⟩
  · exact hKb
  · exact hK
  · exact hlam

end ZInQ.Manuscript.PoleS12
