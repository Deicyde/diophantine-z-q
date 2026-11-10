import ZInQKernel.RouteK.Rank5b.Sec3.Props

/-!
# Proposition 3.4 of tyz-5b (partition form)

`det_M5bG_eq_class73`: if `y(V) = 0`, `det M_5b` is the sum of `Π_B g(B)` over the partitions of `V`
with exactly one block of class 7 and all other blocks of class 3.
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The block weight with one marked block `B₇` of class 7, the others of class 3. -/
noncomputable def markW' (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (B7 B : Finset ι) : ZMod 2 :=
  if B = B7 then w7 a y z B else w3 a y z B

theorem class73_eq_marked (a : ι → ι → ZMod 2) (y z : ι → ZMod 2)
    (P : Finpartition (univ : Finset ι)) :
    (if (P.parts.filter fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0).card = 1 ∧
        ∀ B ∈ P.parts, (∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0) ∨
          (∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1) then ∏ B ∈ P.parts, redeiG a y z B else 0) =
      ∑ B7 ∈ P.parts, ∏ B ∈ P.parts, markW' a y z B7 B := by
  split_ifs with hc
  · obtain ⟨h7c, hall⟩ := hc
    obtain ⟨B7, hB7⟩ := Finset.card_eq_one.1 h7c
    have hB7m : B7 ∈ P.parts.filter (fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0) :=
      hB7 ▸ Finset.mem_singleton_self B7
    obtain ⟨hB7p, hc7⟩ := Finset.mem_filter.1 hB7m
    have huniq : ∀ B ∈ P.parts, (∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0) → B = B7 := fun B hB hc => by
      have : B ∈ P.parts.filter (fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0) :=
        Finset.mem_filter.2 ⟨hB, hc⟩
      rw [hB7] at this; exact Finset.mem_singleton.1 this
    rw [Finset.sum_eq_single B7]
    · refine Finset.prod_congr rfl fun B hB => ?_
      unfold markW'
      split_ifs with h1
      · subst h1; rw [w7, if_pos hc7]
      · rw [w3, if_pos]
        rcases hall B hB with h | h
        · exact absurd (huniq B hB h) h1
        · exact h
    · intro B7' hB7' hne
      refine Finset.prod_eq_zero hB7' ?_
      rw [markW', if_pos rfl]
      exact w7_eq_zero fun hc => hne (huniq B7' hB7' hc)
    · intro h; exact absurd hB7p h
  · symm
    refine Finset.sum_eq_zero fun B7 hB7 => ?_
    by_contra hne
    have hfac := Finset.prod_ne_zero_iff.1 hne
    have hc7 : ∑ i ∈ B7, y i = 1 ∧ ∑ i ∈ B7, z i = 0 := by
      by_contra h
      have := hfac B7 hB7
      rw [markW', if_pos rfl, w7_eq_zero h] at this
      exact this rfl
    have hc3 : ∀ B ∈ P.parts, B ≠ B7 → ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1 := fun B hB hne' => by
      by_contra h
      have := hfac B hB
      rw [markW', if_neg hne', w3_eq_zero h] at this
      exact this rfl
    apply hc
    refine ⟨Finset.card_eq_one.2 ⟨B7, ?_⟩, fun B hB => ?_⟩
    · ext B
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hB, hc'⟩
        by_contra hne'
        rw [(hc3 B hB hne').2] at hc'; exact one_ne_zero hc'.2
      · rintro rfl; exact ⟨hB7, hc7⟩
    · by_cases h : B = B7
      · subst h; exact Or.inl hc7
      · exact Or.inr (hc3 B hB h)

/-- The block factor of the marked partition, as a function of the roots of the block. -/
def markE' (y z : ι → ZMod 2) (B7 B S : Finset ι) : ZMod 2 :=
  if B = B7 then (if S.card = 1 then ∑ ρ ∈ S, (y ρ + z ρ) else 0)
  else (if S.card = 1 then ∏ ρ ∈ S, z ρ else 0)

theorem prod_markW'_eq {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2)
    (P : Finpartition (univ : Finset ι)) (B7 : Finset ι) :
    ∏ B ∈ P.parts, markW' a y z B7 B = ∑ f ∈ allF (univ : Finset ι),
      if Resp f P then (∏ B ∈ P.parts, markE' y z B7 B (B ∩ rootsOf univ f)) *
        (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) else 0 := by
  classical
  have hW : ∀ B, markW' a y z B7 B = ∑ g ∈ allF B,
      (if B = B7 then blockH a y 1 (fun F => ∑ ρ ∈ F, (y ρ + z ρ)) B g
        else blockH a y 1 (fun F => ∏ ρ ∈ F, z ρ) B g) := fun B => by
    unfold markW'
    split_ifs
    · exact w7_eq hrec z B
    · exact w3_eq hrec z B
  rw [Finset.prod_congr rfl fun B _ => hW B, prod_sum_allF, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f hf => ?_
  by_cases hP : Resp f P
  · rw [if_pos hP, if_pos (show ∀ i, f i ∈ P.part i from hP)]
    have hblock : ∀ B ∈ P.parts, (if B = B7 then blockH a y 1 (fun F => ∑ ρ ∈ F, (y ρ + z ρ)) B
        (restrict B f) else blockH a y 1 (fun F => ∏ ρ ∈ F, z ρ) B (restrict B f)) =
        markE' y z B7 B (B ∩ rootsOf univ f) * (∏ i ∈ B ∩ (univ \ rootsOf univ f), a i (f i)) *
          ∏ ρ ∈ B ∩ rootsOf univ f, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v := by
      intro B hB
      by_cases h : B = B7
      · rw [if_pos h, blockH_restrict a y P hP hB, markE', if_pos h]
      · rw [if_neg h, blockH_restrict a y P hP hB, markE', if_neg h]
    rw [Finset.prod_congr rfl hblock, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      prod_parts_inter, prod_parts_inter, wt, treeY, mul_assoc]
  · rw [if_neg hP, if_neg (show ¬∀ i, f i ∈ P.part i from hP)]

/-- For a compatible partition, the marked sum is `Σ_{ρ∈R} (y_ρ + z_ρ) z^{R∖ρ}` if every block has
one root, and `0` otherwise. -/
theorem sum_marked'_eq (y z : ι → ZMod 2) {f : ι → ι} (hf : f ∈ allF (univ : Finset ι))
    {P : Finpartition (univ : Finset ι)} (hP : Resp f P) :
    ∑ B7 ∈ P.parts, ∏ B ∈ P.parts, markE' y z B7 B (B ∩ rootsOf univ f) =
      if P ∈ setAgen f (rootsOf univ f) then
        ∑ ρ7 ∈ rootsOf univ f, (y ρ7 + z ρ7) * ∏ ρ ∈ (rootsOf univ f).erase ρ7, z ρ else 0 := by
  classical
  set R := rootsOf univ f
  split_ifs with hA
  · have hE : ∀ ρ ∈ R, P.part ρ ∩ R = {ρ} := (Finset.mem_filter.1 hA).2.2.1
    have hblock : ∀ B ∈ P.parts, ∃ ρ ∈ R, P.part ρ = B := fun B hB => by
      obtain ⟨i, hi⟩ := Finpartition.nonempty_of_mem_parts P hB
      exact ⟨root f i, root_mem_rootsOf hf i, by rw [part_root hP, P.part_eq_of_mem hB hi]⟩
    symm
    refine Finset.sum_bij (fun ρ _ => P.part ρ) (fun ρ _ => part_mem_univ P ρ) ?_ ?_ ?_
    · intro ρ hρ ρ' hρ' h
      have : ρ' ∈ P.part ρ ∩ R := by rw [h]; exact Finset.mem_inter.2 ⟨mem_part_univ P ρ', hρ'⟩
      rw [hE ρ hρ, Finset.mem_singleton] at this; exact this.symm
    · intro B hB
      obtain ⟨ρ, hρ, rfl⟩ := hblock B hB
      exact ⟨ρ, hρ, rfl⟩
    · intro ρ hρ
      set S := R.erase ρ
      rw [← Finset.mul_prod_erase _ _ (part_mem_univ P ρ), ← prod_parts_inter P S z,
        ← Finset.mul_prod_erase _ _ (part_mem_univ P ρ)]
      have hS : P.part ρ ∩ S = ∅ := by
        ext i
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
        intro hi hiS
        have : i ∈ P.part ρ ∩ R := Finset.mem_inter.2 ⟨hi, Finset.mem_of_mem_erase hiS⟩
        rw [hE ρ hρ, Finset.mem_singleton] at this
        exact Finset.ne_of_mem_erase hiS this
      rw [hS, Finset.prod_empty, one_mul]
      unfold markE'
      rw [if_pos rfl, hE ρ hρ, Finset.card_singleton, if_pos rfl, Finset.sum_singleton]
      congr 1
      refine Finset.prod_congr rfl fun B hB => ?_
      obtain ⟨hBne, hBp⟩ := Finset.mem_erase.1 hB
      obtain ⟨σ, hσ, rfl⟩ := hblock B hBp
      rw [if_neg hBne, hE σ hσ, Finset.card_singleton, if_pos rfl]
      have hσρ : σ ≠ ρ := fun h => hBne (by rw [h])
      have : P.part σ ∩ S = {σ} := by
        rw [← hE σ hσ]
        ext i
        simp only [Finset.mem_inter, S, Finset.mem_erase]
        constructor
        · rintro ⟨hi, -, hiR⟩; exact ⟨hi, hiR⟩
        · rintro ⟨hi, hiR⟩
          refine ⟨hi, fun h => hσρ ?_, hiR⟩
          have : i ∈ P.part σ ∩ R := Finset.mem_inter.2 ⟨hi, hiR⟩
          rw [hE σ hσ, Finset.mem_singleton] at this
          rw [← this, h]
      rw [this]
  · -- some block does not have exactly one root
    have hnot : ¬∀ B ∈ P.parts, (B ∩ R).card = 1 := fun h =>
      hA ((resp_blocks_iff hf P hP (Or.inl rfl)).1 h)
    push_neg at hnot
    obtain ⟨B, hB, hcard⟩ := hnot
    refine Finset.sum_eq_zero fun B7 _ => Finset.prod_eq_zero hB ?_
    unfold markE'
    split_ifs <;> rfl

/-- **Proposition 3.4** (tyz-5b §3.1): if `y(V) = 0`, `det M_5b` is the sum of `Π_B g(B)` over the
partitions of `V` with exactly one block of class 7 and all other blocks of class 3. -/
theorem det_M5bG_eq_class73 {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (hy0 : ∑ i, y i = 0) (z : ι → ZMod 2) :
    (M5bG a y z).det = ∑ P : Finpartition (univ : Finset ι),
      (if (P.parts.filter fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0).card = 1 ∧
        ∀ B ∈ P.parts, (∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0) ∨
          (∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1) then ∏ B ∈ P.parts, redeiG a y z B else 0) := by
  classical
  rw [Finset.sum_congr rfl fun P _ => class73_eq_marked a y z P]
  simp_rw [prod_markW'_eq hrec z]
  have swap : ∀ P : Finpartition (univ : Finset ι),
      (∑ B7 ∈ P.parts, ∑ f ∈ allF (univ : Finset ι),
        if Resp f P then (∏ B ∈ P.parts, markE' y z B7 B (B ∩ rootsOf univ f)) *
          (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) else 0) =
      ∑ f ∈ allF (univ : Finset ι), (if Resp f P then ∑ B7 ∈ P.parts,
        ∏ B ∈ P.parts, markE' y z B7 B (B ∩ rootsOf univ f) else 0) *
          (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) := by
    intro P
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hP : Resp f P
    · simp only [if_pos hP, Finset.sum_mul]
    · simp only [if_neg hP, Finset.sum_const_zero, zero_mul]
  rw [Finset.sum_congr rfl fun P _ => swap P, Finset.sum_comm, det_M5bG_forest hrec, hy0,
    add_zero, one_mul]
  rw [show (∑ F ∈ (univ : Finset ι).powerset, (∑ k ∈ F, y k * ∏ ρ ∈ F.erase k, z ρ) *
      ∑ f ∈ forests univ F, wt a (univ \ F) f *
        ∏ ρ ∈ F, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v) =
      ∑ F ∈ (univ : Finset ι).powerset, ∑ f ∈ forests univ F,
        (∑ k ∈ F, y k * ∏ ρ ∈ F.erase k, z ρ) * (wt a (univ \ F) f * treeY y univ F f) from
    Finset.sum_congr rfl fun F _ => by rw [Finset.mul_sum]; rfl]
  rw [sum_allF]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [← Finset.sum_mul]
  by_cases htree : treeY y univ (rootsOf univ f) f = 0
  · rw [htree, mul_zero, mul_zero, mul_zero]
  congr 1
  have heven := even_card_roots hy0 hf htree
  -- the compatible partitions with one root per block: only the tree partition
  have h1 : ∀ P : Finpartition (univ : Finset ι), (if Resp f P then ∑ B7 ∈ P.parts,
      ∏ B ∈ P.parts, markE' y z B7 B (B ∩ rootsOf univ f) else 0) =
      if P ∈ setAgen f (rootsOf univ f) then ∑ ρ7 ∈ rootsOf univ f,
        (y ρ7 + z ρ7) * ∏ ρ ∈ (rootsOf univ f).erase ρ7, z ρ else 0 := by
    intro P
    by_cases hP : Resp f P
    · rw [if_pos hP, sum_marked'_eq y z hf hP]
    · rw [if_neg hP, if_neg fun hA => hP (Finset.mem_filter.1 hA).2.1]
  rw [Finset.sum_congr rfl fun P _ => h1 P, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, card_setAgen_roots hf, one_smul]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun ρ7 h7 => Finset.mul_prod_erase (rootsOf univ f) z h7,
    Finset.sum_const, nsmul_eq_mul, ZMod.natCast_eq_zero_iff_even.2 heven, zero_mul, add_zero]

end ZInQ.RouteK.Rank5b.Sec3
