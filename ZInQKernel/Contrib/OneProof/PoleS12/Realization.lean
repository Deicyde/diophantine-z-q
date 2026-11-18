import ZInQKernel.Contrib.OneProof.PoleS12.Choice

/-!
# `MatrixRealization` is proved (S12's `par:simultaneous-matrices`)

`ZInQ.Manuscript.PoleS12.matrixRealization : ZInQ.Manuscript.PoleRC.MatrixRealization`.

ELLIOT (supplement S12, lines 543–683; the manuscript delegates this step to S11–S12 at tex
L1033–1060). The construction: `B = supp β`, `J = supp θ`, `b* ∈ B`; auxiliary primes `g b ≡ 1`
(mod 12) for `b ∈ B ∖ {b*}` with cross columns `e_b + e_{b*}`; the deleted block on `B ∪ I` is
nonsingular (`block_injOn`); it stays nonsingular on `B ∪ I ∪ J` after toggling the `J`-diagonal
(`exists_toggle_injOn`), the toggles being the symbols `[q₀/q_j]`; finally `q₀ ≡ 7 (mod 12)` with
the prescribed symbols (`exists_prime_lsym`: CRT + Dirichlet), and `n = q₀ β ∏ g b`.

Correction (d) of the design review is visible in the proof: the toggles `d` are supported on `J`
(`hd`), so they do not enter the matrix of the smaller support `B ∪ I` (`hinjn` uses `d i = 0`
for `i ∉ J`); only one determinant varies.
-/

namespace ZInQ.Manuscript.PoleS12

open Finset ZInQ.Manuscript.PoleRC

theorem odd3_of_dvd {m q : ℕ} (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) (hq : q ∈ m.primeFactors) :
    Odd3 q := by
  obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.mp hq
  refine ⟨hqp, ?_, ?_⟩
  · rcases hqp.eq_two_or_odd with h | h
    · rw [h] at hqd; omega
    · exact h
  · rintro rfl; omega

theorem lsym_eq_zero_of_isSquare {m q : ℕ} (h : IsSquare (m : ZMod q)) : lsym (m : ℤ) q = 0 :=
  lsym_of_isSquare (by simpa using h)

/-- **`MatrixRealization` holds** (S12's `par:simultaneous-matrices`, ELLIOT (supplement)). -/
theorem matrixRealization : MatrixRealization := by
  classical
  intro β θ hβ hθ hβ24 hθ24 hcop hβsq hθsq
  set B := β.primeFactors with hBdef
  set J := θ.primeFactors with hJdef
  have hβ0 : β ≠ 0 := by omega
  have hθ0 : θ ≠ 0 := by omega
  have hBodd : ∀ q ∈ B, Odd3 q := fun q hq => odd3_of_dvd (by omega) (by omega) hq
  have hJodd : ∀ q ∈ J, Odd3 q := fun q hq => odd3_of_dvd (by omega) (by omega) hq
  have hBJ : Disjoint B J := Nat.Coprime.disjoint_primeFactors hcop
  obtain ⟨bs, hbs⟩ : B.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨g, hg, hginj, hmut⟩ := exists_aux_primes B J bs hBodd hJodd hBJ (B.erase bs)
  set I := (B.erase bs).image g with hIdef
  have hIprop : ∀ k ∈ I, k.Prime ∧ k % 12 = 1 ∧ k ∉ B ∧ k ∉ J := by
    intro k hk
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hk
    exact ⟨(hg b hb).1, (hg b hb).2.1, (hg b hb).2.2.1, (hg b hb).2.2.2.1⟩
  have hBI : Disjoint B I := disjoint_right.mpr fun k hk => (hIprop k hk).2.2.1
  have hIJ : Disjoint I J := disjoint_left.mpr fun k hk => (hIprop k hk).2.2.2
  have hBIJ : Disjoint (B ∪ I) J := disjoint_union_left.mpr ⟨hBJ, hIJ⟩
  have hIodd : ∀ k ∈ I, Odd3 k := fun k hk =>
    odd3_of_mod12 (hIprop k hk).1 (Or.inl (hIprop k hk).2.1)
  -- reciprocity with an auxiliary prime
  have hrecI : ∀ k ∈ I, ∀ q, Odd3 q → q ≠ k → lsymS q k = lsym (k : ℤ) q := fun k hk q hq hqk =>
    lsym_recip_one (hIprop k hk).1 hq.1 (by have := (hIprop k hk).2.1; omega) hq.2.1
      (Ne.symm hqk)
  -- the fixed symbol sums (S12 L556–565)
  have hJsq : ∀ b ∈ B, ∑ j ∈ J, lsym (j : ℤ) b = 0 := by
    intro b hb
    have hbp := (hBodd b hb).1
    have := Fact.mk hbp
    rw [sum_lsym_primeFactors b θ hθ fun h => disjoint_left.mp hBJ hb
      (Nat.mem_primeFactors.mpr ⟨hbp, h, hθ0⟩)]
    exact lsym_eq_zero_of_isSquare (hθsq b hbp (Nat.mem_primeFactors.mp hb).2.1)
  have hBsq : ∀ j ∈ J, ∑ b ∈ B, lsym (b : ℤ) j = 0 := by
    intro j hj
    have hjp := (hJodd j hj).1
    have := Fact.mk hjp
    rw [sum_lsym_primeFactors j β hβ fun h => disjoint_right.mp hBJ hj
      (Nat.mem_primeFactors.mpr ⟨hjp, h, hβ0⟩)]
    exact lsym_eq_zero_of_isSquare (hβsq j hjp (Nat.mem_primeFactors.mp hj).2.1)
  have hβ4 : ∑ b ∈ B, lsym (-1) b = 0 := by
    rw [sum_sgn_eq β hβ (by omega), if_neg (by omega)]
  have hβlam : ∑ b ∈ B, lamS b = 1 := by
    simp only [lamS]
    rw [sum_lam_eq β hβ (by omega) (by omega), if_pos (by omega), if_neg (by omega), add_zero]
  -- the block on `B ∪ I`
  set cq : ℕ → ZMod 2 := fun i => if i ∈ B then ∑ k ∈ I, lsymS k i else 0 with hcq
  set a0 : ℕ → ZMod 2 := fun k => if k = bs then 1 else 0 with ha0
  have hcolS : ∀ b ∈ B.erase bs, ∀ b' ∈ B,
      lsymS b' (g b) = (if b' = b then 1 else 0) + (if b' = bs then 1 else 0) := by
    intro b hb b' hb'
    rw [hrecI (g b) (mem_image_of_mem g hb) b' (hBodd b' hb')
      (fun h => (hg b hb).2.2.1 (h ▸ hb'))]
    exact (hg b hb).2.2.2.2.1 b' hb'
  have hblock : InjOnS (NMat lsymS (B ∪ I) cq lamS a0) (B ∪ I) := by
    refine block_injOn hbs hginj hBI cq lamS hcolS (fun b hb b'' hb'' hne => hmut b hb b'' hb'' hne)
      (fun b hb b' hb' => ?_) (fun b hb => ⟨?_, ?_⟩) (fun b hb => by simp only [hcq, if_pos hb]; rfl)
      hβlam
    · have h1 := hrecI (g b) (mem_image_of_mem g hb) b' (hBodd b' hb')
        (fun h => (hg b hb).2.2.1 (h ▸ hb'))
      rw [h1]; rfl
    · exact lsym_three_of_one (hg b hb).1 (hg b hb).2.1
    · simp only [hcq, if_neg (hg b hb).2.2.1]
  -- the block is unchanged on `B ∪ I ∪ J` (S12 L654–658)
  have hJzero : ∀ i ∈ B ∪ I, ∑ j ∈ J, lsymS j i = 0 := by
    intro i hi
    rcases mem_union.mp hi with hiB | hiI
    · exact hJsq i hiB
    · rw [sum_congr rfl fun j hj => hrecI i hiI j (hJodd j hj)
        (fun h => (hIprop i hiI).2.2.2 (h ▸ hj))]
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hiI
      exact sum_eq_zero fun j hj => (hg b hb).2.2.2.2.2 j hj
  have hblockJ : InjOnS (NMat lsymS (B ∪ I ∪ J) cq lamS a0) (B ∪ I) := by
    refine injOnS_congr (fun i hi k _ => ?_) hblock
    simp only [NMat]
    by_cases hik : i = k
    · rw [if_pos hik, if_pos hik]
      have hiJ : i ∉ J := fun h => disjoint_left.mp hBIJ hi h
      rw [show (B ∪ I ∪ J).erase i = (B ∪ I).erase i ∪ J by
          rw [erase_union_distrib, erase_eq_of_notMem hiJ],
        sum_union (disjoint_of_subset_left (erase_subset _ _) hBIJ), hJzero i hi, add_zero]
    · rw [if_neg hik, if_neg hik]
  obtain ⟨d, hd, hinjd⟩ := exists_toggle_injOn hblockJ J hBIJ
  -- the prime `q₀` (S12 L668–679)
  have hQ : ∀ q ∈ B ∪ I ∪ J, Odd3 q := by
    intro q hq
    rcases mem_union.mp hq with hq | hq
    · rcases mem_union.mp hq with hq | hq
      · exact hBodd q hq
      · exact hIodd q hq
    · exact hJodd q hq
  obtain ⟨q₀, hq₀p, hq₀12, hq₀F, hq₀e⟩ := exists_prime_lsym 7 (by norm_num) (B ∪ I ∪ J) hQ
    (fun i => cq i + d i) (B ∪ I ∪ J)
  have hq₀7 : q₀ % 12 = 7 := by omega
  have hq₀B : ∀ b ∈ B, lsym (q₀ : ℤ) b = ∑ k ∈ I, lsym (k : ℤ) b := by
    intro b hb
    rw [hq₀e b (mem_union_left _ (mem_union_left _ hb)), hd b (disjoint_left.mp hBJ hb),
      add_zero]
    simp only [hcq, if_pos hb]; rfl
  have hq₀sym : ∀ i ∈ B ∪ I ∪ J, lsymS q₀ i = cq i + d i := fun i hi => hq₀e i hi
  have hprime : ∀ J' ⊆ J, ∀ k ∈ insert q₀ (B ∪ I ∪ J'), Odd3 k := by
    intro J' hJ' k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact odd3_of_mod12 hq₀p (Or.inr (Or.inl hq₀7))
    · rcases mem_union.mp hk with hk | hk
      · exact hQ k (mem_union_left _ hk)
      · exact hQ k (mem_union_right _ (hJ' hk))
  -- the support of `n`
  have hinjn : InjOnS (NMat lsymS (B ∪ I ∪ ∅) (fun i => lsymS q₀ i) lamS a0) (B ∪ I ∪ ∅) := by
    rw [union_empty]
    refine injOnS_congr (fun i hi k _ => ?_) hblock
    simp only [NMat]
    rw [hq₀sym i (mem_union_left _ hi), hd i (fun h => disjoint_left.mp hBIJ hi h), add_zero]
  have hMn := mc_of_choice (J' := ∅) hBdef hβ0 (hprime ∅ (empty_subset _)) hBI
    (disjoint_empty_right _) (disjoint_empty_right _)
    (by rw [union_empty]; exact fun h => hq₀F (mem_union_left _ h)) hbs hIdef hginj
    (fun k hk => (hIprop k hk).2.1) hq₀7 (fun b hb b' hb' => (hg b hb).2.2.2.2.1 b' hb')
    (fun j hj => absurd hj (notMem_empty j)) (fun b _ => sum_empty) hβ4 hq₀B hinjn
  -- the support of `nθ`
  have hinjnθ : InjOnS (NMat lsymS (B ∪ I ∪ J) (fun i => lsymS q₀ i) lamS a0) (B ∪ I ∪ J) := by
    refine injOnS_congr (fun i hi k _ => ?_) hinjd
    simp only [addDiag, NMat]
    rw [hq₀sym i hi]
    split_ifs <;> ring
  have hMnθ := mc_of_choice (J' := J) hBdef hβ0 (hprime J subset_rfl) hBI hBJ hIJ hq₀F hbs hIdef
    hginj (fun k hk => (hIprop k hk).2.1) hq₀7 (fun b hb b' hb' => (hg b hb).2.2.2.2.1 b' hb')
    hBsq hJsq hβ4 hq₀B hinjnθ
  rw [union_empty] at hMn
  -- `n` and `nθ` as products
  have hq₀BI : q₀ ∉ B ∪ I := fun h => hq₀F (mem_union_left _ h)
  have hprodB : ∏ k ∈ B, k = β := Nat.prod_primeFactors_of_squarefree hβ
  have hprodJ : ∏ k ∈ J, k = θ := Nat.prod_primeFactors_of_squarefree hθ
  have hnθ : ∏ k ∈ insert q₀ (B ∪ I ∪ J), k = (∏ k ∈ insert q₀ (B ∪ I), k) * θ := by
    rw [prod_insert hq₀F, prod_insert hq₀BI, prod_union hBIJ, hprodJ, mul_assoc]
  have hn : ∏ k ∈ insert q₀ (B ∪ I), k = q₀ * (β * ∏ k ∈ I, k) := by
    rw [prod_insert hq₀BI, prod_union hBI, hprodB]
  have hI12 : (∏ k ∈ I, k) % 12 = 1 := by
    rw [prod_nat_mod, prod_congr rfl fun k hk => (hIprop k hk).2.1, prod_const_one]
    rfl
  refine ⟨∏ k ∈ insert q₀ (B ∪ I), k, ?_, ?_, ?_, ?_, hMn, ?_⟩
  · exact prod_pos fun k hk => (hprime ∅ (empty_subset _) k (by rwa [union_empty])).1.pos
  · rw [← hnθ]
    exact squarefree_prod_primes _ fun k hk => (hprime J subset_rfl k hk).1
  · rw [hn, Nat.mul_mod, Nat.mul_mod β, hI12, hq₀7, show β % 12 = 5 by omega]
  · rw [hn]; exact ⟨q₀ * ∏ k ∈ I, k, by ring⟩
  · rw [← hnθ]; exact hMnθ

end ZInQ.Manuscript.PoleS12
