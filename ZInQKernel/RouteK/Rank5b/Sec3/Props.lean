import ZInQKernel.RouteK.Rank5b.Sec3.Thm36

/-!
# Propositions 3.3 and 3.5 of tyz-5b (partition forms)

* `card_setAgen`: for a forest `f` with roots `R` and `E ⊆ R`, the set partitions compatible with
  `f` in which the roots of `E` are alone in their blocks and every other block has exactly two
  roots correspond to the fixed-point-free involutions of `R ∖ E`;
* `sum_prod_uniform`: `Σ_π Π_{B∈π} Σ_{g ∈ allF B} [g has k roots] z^{roots} wt(g) treeY` as a forest sum
  with the number of compatible partitions into blocks of `k` roots;
* **Proposition 3.3** (`det_M1G_eq_class3`, `det_M1G_eq_zero`): if `y(V) = 0`, `det M₁` is the sum of
  `Π g(B)` over the partitions into blocks of class 3; if `y(V) = 1`, `det M₁ = 0`;
* **Proposition 3.5** (`sum_class1_eq_sum_class3`): if `y(V) = 0`, the sums of `Π g(B)` over the
  partitions into blocks of class 1 and over the partitions into blocks of class 3 are equal. It is
  stated for the whole index type; for a subset `S` apply it to the subtype `S` (the bits restricted to
  `S`).
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Count

variable {f : ι → ι}

/-- The set partitions compatible with `f` in which the roots in `E` are alone among the roots of
their blocks, and every other block contains exactly two roots. -/
def setAgen (f : ι → ι) (E : Finset ι) : Finset (Finpartition (univ : Finset ι)) :=
  univ.filter fun P => Resp f P ∧ (∀ ρ ∈ E, P.part ρ ∩ rootsOf univ f = {ρ}) ∧
    ∀ ρ ∈ rootsOf univ f, ρ ∉ E → (P.part ρ ∩ rootsOf univ f).card = 2

theorem card_setAgen (hf : f ∈ allF (univ : Finset ι)) {E : Finset ι} (hE : E ⊆ rootsOf univ f) :
    (setAgen f E).card = (fpfi (rootsOf univ f \ E)).card := by
  classical
  set R := rootsOf univ f with hR
  set X := R \ E with hX
  have hmemX : ∀ ρ, ρ ∈ X ↔ ρ ∈ R ∧ ρ ∉ E := fun ρ => Finset.mem_sdiff
  have hb1 : ∀ s : ι → ι, ∀ i, i ∈ bS f s i := fun s i => by simp [bS]
  have hb2 : ∀ s ∈ fpfi X, ∀ i j, j ∈ bS f s i → bS f s j = bS f s i := by
    intro s hs i j hj
    have hinv := fpfi_invol hs
    simp only [bS, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    ext k
    simp only [bS, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with hj | hj
    · rw [hj]
    · rw [hj, hinv]; tauto
  symm
  refine Finset.card_bij (fun s hs => ofPartFun (bS f s) (hb1 s) (hb2 s hs)) ?_ ?_ ?_
  · intro s hs
    have hid := (mem_fpfi.1 hs).1
    have hXs := (mem_fpfi.1 hs).2
    have hpart : ∀ i, (ofPartFun (bS f s) (hb1 s) (hb2 s hs)).part i = bS f s i :=
      part_ofPartFun _ _ _
    have hsing : ∀ ρ ∈ R, ρ ∉ X → bS f s ρ ∩ R = {ρ} := by
      intro ρ hρ hρX
      ext j
      simp only [bS, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, root_eq_self hρ, hid ρ hρX]
      constructor
      · rintro ⟨h | h, hj⟩ <;> rwa [root_eq_self hj] at h
      · rintro rfl; exact ⟨Or.inl (root_eq_self hρ), hρ⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => ?_, fun ρ hρE => ?_,
      fun ρ hρ hρE => ?_⟩
    · rw [hpart]; simp [bS, root_apply (mem_allF.1 hf).2.2]
    · rw [hpart, hsing ρ (hE hρE) (fun h => ((hmemX ρ).1 h).2 hρE)]
    · have hρX : ρ ∈ X := (hmemX ρ).2 ⟨hρ, hρE⟩
      obtain ⟨hsX, hsne, -⟩ := hXs ρ hρX
      have hsR : s ρ ∈ R := ((hmemX _).1 hsX).1
      rw [hpart]
      have : bS f s ρ ∩ R = {ρ, s ρ} := by
        ext j
        simp only [bS, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton, root_eq_self hρ]
        constructor
        · rintro ⟨h, hj⟩; rwa [root_eq_self hj] at h
        · rintro (rfl | rfl)
          · exact ⟨Or.inl (root_eq_self hρ), hρ⟩
          · exact ⟨Or.inr (root_eq_self hsR), hsR⟩
      rw [this, Finset.card_pair (Ne.symm hsne)]
  · intro s hs t ht hst
    have hpart := fun i => congrArg (fun P : Finpartition (univ : Finset ι) => P.part i) hst
    simp only [part_ofPartFun] at hpart
    funext ρ
    by_cases hρX : ρ ∈ X
    · have hρ : ρ ∈ R := ((hmemX ρ).1 hρX).1
      obtain ⟨hsX, hsne, -⟩ := (mem_fpfi.1 hs).2 ρ hρX
      have hsR : s ρ ∈ R := ((hmemX _).1 hsX).1
      have hmem : s ρ ∈ bS f s ρ := by simp [bS, root_eq_self hρ, root_eq_self hsR]
      rw [hpart ρ] at hmem
      simp only [bS, Finset.mem_filter, Finset.mem_univ, true_and, root_eq_self hρ,
        root_eq_self hsR] at hmem
      rcases hmem with h | h
      · exact absurd h hsne
      · exact h
    · rw [(mem_fpfi.1 hs).1 ρ hρX, (mem_fpfi.1 ht).1 ρ hρX]
  · intro P hP
    obtain ⟨-, hresp, hPE, hP2⟩ := Finset.mem_filter.1 hP
    replace hPE : ∀ ρ ∈ E, P.part ρ ∩ R = {ρ} := hPE
    replace hP2 : ∀ ρ ∈ R, ρ ∉ E → (P.part ρ ∩ R).card = 2 := hP2
    have hex : ∀ ρ ∈ X, ∃ σ, (P.part ρ ∩ R).erase ρ = {σ} := fun ρ hρX => by
      obtain ⟨hρ, hρE⟩ := (hmemX ρ).1 hρX
      apply Finset.card_eq_one.1
      rw [Finset.card_erase_of_mem (Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩), hP2 ρ hρ hρE]
    let s : ι → ι := fun ρ => if h : ρ ∈ X then Classical.choose (hex ρ h) else ρ
    have hs_spec : ∀ ρ (h : ρ ∈ X), (P.part ρ ∩ R).erase ρ = {s ρ} := fun ρ h => by
      simp only [s, dif_pos h]; exact Classical.choose_spec (hex ρ h)
    have hs_mem : ∀ ρ ∈ X, s ρ ∈ P.part ρ ∧ s ρ ∈ R ∧ s ρ ≠ ρ := fun ρ h => by
      have : s ρ ∈ (P.part ρ ∩ R).erase ρ := by rw [hs_spec ρ h]; exact Finset.mem_singleton_self _
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 this
      exact ⟨(Finset.mem_inter.1 hmem).1, (Finset.mem_inter.1 hmem).2, hne⟩
    have hpartR : ∀ ρ ∈ X, P.part ρ ∩ R = {ρ, s ρ} := fun ρ h => by
      rw [← hs_spec ρ h, Finset.insert_erase (Finset.mem_inter.2 ⟨mem_part_univ P ρ,
        ((hmemX ρ).1 h).1⟩)]
    have hsX : ∀ ρ ∈ X, s ρ ∈ X := by
      intro ρ h
      obtain ⟨hsP, hsR, hsne⟩ := hs_mem ρ h
      obtain ⟨hρ, hρE⟩ := (hmemX ρ).1 h
      refine (hmemX _).2 ⟨hsR, fun hsE => ?_⟩
      have : ρ ∈ P.part (s ρ) ∩ R := by
        rw [part_eq_part_of_mem P hsP]; exact Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩
      rw [hPE _ hsE, Finset.mem_singleton] at this
      exact hsne this.symm
    have hss : ∀ ρ ∈ X, s (s ρ) = ρ := by
      intro ρ h
      obtain ⟨hsP, hsR, hsne⟩ := hs_mem ρ h
      have h1 := hpartR (s ρ) (hsX ρ h)
      rw [part_eq_part_of_mem P hsP, hpartR ρ h] at h1
      have : s (s ρ) ∈ ({ρ, s ρ} : Finset ι) := by
        rw [h1]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rcases Finset.mem_insert.1 this with h' | h'
      · exact h'
      · exact absurd (Finset.mem_singleton.1 h') (hs_mem (s ρ) (hsX ρ h)).2.2
    have hsf : s ∈ fpfi X := mem_fpfi.2 ⟨fun ρ h => by simp [s, h],
      fun ρ h => ⟨hsX ρ h, (hs_mem ρ h).2.2, hss ρ h⟩⟩
    refine ⟨s, hsf, finpartition_ext_part fun i => ?_⟩
    rw [part_ofPartFun]
    set ρ := root f i with hρdef
    have hρ : ρ ∈ R := root_mem_rootsOf hf i
    rw [← part_root hresp i]
    ext j
    simp only [bS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hρdef, mem_part_iff_root hresp]
    have hrj := root_mem_rootsOf hf j
    have key : root f j ∈ P.part ρ ↔ root f j ∈ P.part ρ ∩ R := by
      rw [Finset.mem_inter]; tauto
    rw [key]
    by_cases hρX : ρ ∈ X
    · rw [hpartR ρ hρX]; simp
    · have hsρ : s ρ = ρ := by simp [s, hρX]
      have hρE : ρ ∈ E := by
        by_contra hne; exact hρX ((hmemX ρ).2 ⟨hρ, hne⟩)
      rw [hsρ, hPE ρ hρE]; simp

/-- Compatible partitions into blocks with exactly `k` roots (`k = 1, 2`) are `setAgen`. -/
theorem resp_blocks_iff (hf : f ∈ allF (univ : Finset ι)) (P : Finpartition (univ : Finset ι))
    (hP : Resp f P) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    (∀ B ∈ P.parts, (B ∩ rootsOf univ f).card = k) ↔
      P ∈ setAgen f (if k = 1 then rootsOf univ f else ∅) := by
  set R := rootsOf univ f
  have hblock : ∀ B ∈ P.parts, ∃ ρ ∈ R, P.part ρ = B := fun B hB => by
    obtain ⟨i, hi⟩ := Finpartition.nonempty_of_mem_parts P hB
    exact ⟨root f i, root_mem_rootsOf hf i, by rw [part_root hP, P.part_eq_of_mem hB hi]⟩
  rcases hk with rfl | rfl
  · simp only [if_true]
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hP, fun ρ hρ => ?_, fun ρ hρ hρE => absurd hρ hρE⟩
      obtain ⟨σ, hσ⟩ := Finset.card_eq_one.1 (h _ (part_mem_univ P ρ))
      have : ρ ∈ P.part ρ ∩ R := Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩
      rw [hσ, Finset.mem_singleton] at this
      rw [hσ, this]
    · intro h B hB
      obtain ⟨-, -, hE, -⟩ := Finset.mem_filter.1 h
      obtain ⟨ρ, hρ, rfl⟩ := hblock B hB
      rw [hE ρ hρ, Finset.card_singleton]
  · simp only [show (2 : ℕ) ≠ 1 by decide, if_false]
    constructor
    · intro h
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hP, fun ρ hρ => absurd hρ (Finset.notMem_empty ρ),
        fun ρ hρ _ => h _ (part_mem_univ P ρ)⟩
    · intro h B hB
      obtain ⟨-, -, -, h2⟩ := Finset.mem_filter.1 h
      obtain ⟨ρ, hρ, rfl⟩ := hblock B hB
      exact h2 ρ hρ (Finset.notMem_empty ρ)

end Count

theorem blockH_restrict (a : ι → ι → ZMod 2) (y : ι → ZMod 2)
    (P : Finpartition (univ : Finset ι)) {f : ι → ι} (hP : Resp f P) {B : Finset ι}
    (hB : B ∈ P.parts) (k : ℕ) (e : Finset ι → ZMod 2) :
    blockH a y k e B (restrict B f) =
      (if (B ∩ rootsOf univ f).card = k then e (B ∩ rootsOf univ f) else 0) *
        (∏ i ∈ B ∩ (univ \ rootsOf univ f), a i (f i)) *
          ∏ ρ ∈ B ∩ rootsOf univ f, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v := by
  set R := rootsOf univ f
  have hmap : ∀ i ∈ B, f i ∈ B := fun i hi => by
    rw [← P.part_eq_of_mem hB hi]; exact hP i
  have hrB : ∀ i ∈ B, restrict B f i ∈ B := fun i hi => by simp [restrict, hi, hmap i hi]
  have hwt : wt a (B \ (B ∩ R)) (restrict B f) = ∏ i ∈ B ∩ (univ \ R), a i (f i) := by
    rw [wt]
    have : B \ (B ∩ R) = B ∩ (univ \ R) := by ext i; simp
    rw [this]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [restrict, (Finset.mem_inter.1 hi).1]
  have htree : treeY y B (B ∩ R) (restrict B f) =
      ∏ ρ ∈ B ∩ R, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v := by
    rw [treeY]
    refine Finset.prod_congr rfl fun ρ hρ => ?_
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv, h⟩
      rw [(root_agree (f := f) hrB (fun j hj => by simp [restrict, hj]) hv).1]; exact h
    · intro h
      have hvB : v ∈ B := by
        rw [← P.part_eq_of_mem hB (Finset.mem_inter.1 hρ).1, ← h, part_root hP]
        exact mem_part_univ P v
      exact ⟨hvB, by
        rw [← (root_agree (f := f) hrB (fun j hj => by simp [restrict, hj]) hvB).1]; exact h⟩
  unfold blockH
  rw [rootsOf_restrict, hwt, htree]
  split_ifs <;> ring

/-- **Glued product, uniform weights**: for a forest `f` compatible with `P`,
`Π_B blockH_k(B, f|_B) = [every block has k roots] z^R wt(f) Π_{ρ∈R} y(T_ρ)`. -/
theorem prod_blockH_restrict (a : ι → ι → ZMod 2) (y z : ι → ZMod 2)
    (P : Finpartition (univ : Finset ι)) {f : ι → ι} (hP : Resp f P) (k : ℕ) :
    ∏ B ∈ P.parts, blockH a y k (fun F => ∏ ρ ∈ F, z ρ) B (restrict B f) =
      (if ∀ B ∈ P.parts, (B ∩ rootsOf univ f).card = k then ∏ ρ ∈ rootsOf univ f, z ρ else 0) *
        (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) := by
  rw [Finset.prod_congr rfl fun B hB => blockH_restrict a y P hP hB k _, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, prod_parts_inter, prod_parts_inter, Finset.prod_ite_zero,
    prod_parts_inter, wt, treeY, mul_assoc]
  by_cases h : ∀ B ∈ P.parts, (B ∩ rootsOf univ f).card = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- **Uniform partition sums as forest sums**: `Σ_π Π_{B∈π} Σ_{g ∈ allF B} blockH_k(B, g) =
Σ_f #{compatible partitions into blocks of k roots} z^R wt(f) Π_ρ y(T_ρ)`. -/
theorem sum_prod_uniform (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (k : ℕ) :
    ∑ P : Finpartition (univ : Finset ι), ∏ B ∈ P.parts,
      ∑ g ∈ allF B, blockH a y k (fun F => ∏ ρ ∈ F, z ρ) B g =
      ∑ f ∈ allF (univ : Finset ι), ((univ.filter fun P : Finpartition (univ : Finset ι) =>
        Resp f P ∧ ∀ B ∈ P.parts, (B ∩ rootsOf univ f).card = k).card : ZMod 2) *
        (∏ ρ ∈ rootsOf univ f, z ρ) *
          (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) := by
  classical
  simp_rw [prod_sum_allF, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases hP : Resp f P
  · rw [if_pos (show ∀ i, f i ∈ P.part i from hP), prod_blockH_restrict a y z P hP k]
    by_cases hk : ∀ B ∈ P.parts, (B ∩ rootsOf univ f).card = k
    · rw [if_pos hk, if_pos ⟨hP, hk⟩, Nat.cast_one, one_mul]
    · rw [if_neg hk, if_neg fun h => hk h.2]; simp
  · rw [if_neg (show ¬∀ i, f i ∈ P.part i from hP), if_neg fun h => hP h.1]; simp

theorem card_uniform_eq {f : ι → ι}
    (hfa : f ∈ allF (univ : Finset ι)) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    (univ.filter fun P : Finpartition (univ : Finset ι) =>
        Resp f P ∧ ∀ B ∈ P.parts, (B ∩ rootsOf univ f).card = k).card =
      (setAgen f (if k = 1 then rootsOf univ f else ∅)).card := by
  congr 1
  ext P
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hP, h⟩; exact (resp_blocks_iff hfa P hP hk).1 h
  · intro h
    have hP : Resp f P := (Finset.mem_filter.1 h).2.1
    exact ⟨hP, (resp_blocks_iff hfa P hP hk).2 h⟩

theorem card_setAgen_roots {f : ι → ι} (hf : f ∈ allF (univ : Finset ι)) :
    (setAgen f (rootsOf univ f)).card = 1 := by
  rw [card_setAgen hf subset_rfl, Finset.sdiff_self]
  have : fpfi (∅ : Finset ι) = {id} := by
    ext s
    simp only [mem_fpfi, Finset.notMem_empty, not_false_eq_true, forall_const,
      IsEmpty.forall_iff, implies_true, and_true, Finset.mem_singleton]
    exact ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩
  rw [this, Finset.card_singleton]

/-- Partitions into blocks of class 3, as a forest sum: `Σ_f z^R wt(f) Π_ρ y(T_ρ)`. -/
theorem sum_class3_eq_forest {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (z : ι → ZMod 2) :
    ∑ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) =
      ∑ f ∈ allF (univ : Finset ι), (∏ ρ ∈ rootsOf univ f, z ρ) *
        (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) := by
  have h1 : ∀ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) =
      ∏ B ∈ P.parts, ∑ g ∈ allF B, blockH a y 1 (fun F => ∏ ρ ∈ F, z ρ) B g := by
    intro P
    rw [Finset.prod_congr rfl fun B _ => (w3_eq hrec z B).symm]
    unfold w3
    rw [Finset.prod_ite_zero]
    by_cases h : ∀ B ∈ P.parts, ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun P _ => h1 P, sum_prod_uniform]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [card_uniform_eq hf (Or.inl rfl), if_pos rfl, card_setAgen_roots hf, Nat.cast_one, one_mul]

/-- Partitions into blocks of class 1, as a forest sum:
`Σ_f #(pairings of the roots) z^R wt(f) Π_ρ y(T_ρ)`. -/
theorem sum_class1_eq_forest {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (z : ι → ZMod 2) :
    ∑ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 0 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) =
      ∑ f ∈ allF (univ : Finset ι), ((fpfi (rootsOf univ f)).card : ZMod 2) *
        (∏ ρ ∈ rootsOf univ f, z ρ) *
          (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) := by
  have h1 : ∀ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 0 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) =
      ∏ B ∈ P.parts, ∑ g ∈ allF B, blockH a y 2 (fun F => ∏ ρ ∈ F, z ρ) B g := by
    intro P
    rw [Finset.prod_congr rfl fun B _ => (w1_eq hrec z B).symm]
    unfold w1
    rw [Finset.prod_ite_zero]
    by_cases h : ∀ B ∈ P.parts, ∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun P _ => h1 P, sum_prod_uniform]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [card_uniform_eq hf (Or.inr rfl), if_neg (by decide), card_setAgen hf (Finset.empty_subset _),
    Finset.sdiff_empty]

/-- **Proposition 3.5** (tyz-5b §3.2): if `y(V) = 0`, the sum of `Π_B g(B)` over the partitions
into blocks of class 1 equals the sum over the partitions into blocks of class 3. -/
theorem sum_class1_eq_sum_class3 {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (hy0 : ∑ i, y i = 0) (z : ι → ZMod 2) :
    ∑ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 0 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) =
    ∑ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) := by
  rw [sum_class1_eq_forest hrec, sum_class3_eq_forest hrec]
  refine Finset.sum_congr rfl fun f hf => ?_
  by_cases htree : treeY y univ (rootsOf univ f) f = 0
  · rw [htree]; ring
  · rw [card_fpfi, if_pos (even_card_roots hy0 hf htree), one_mul]

/-- `det P(z, y)` is the sum over partitions into blocks of class 3 (the forest form of `det P`,
regrouped by blocks). -/
theorem det_Pmat_eq_class3 {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (z : ι → ZMod 2) :
    (Pmat a z y).det = ∑ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) := by
  rw [sum_class3_eq_forest hrec, det_Pmat, ← sum_allF univ (fun F f => (∏ ρ ∈ F, z ρ) *
    (wt a (univ \ F) f * treeY y univ F f))]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.mul_sum]
  rfl

/-- **Proposition 3.3** (tyz-5b §3.1), case `y(V) = 0`: `det M₁` is the sum of `Π_B g(B)` over the
partitions of `V` into blocks of class 3. -/
theorem det_M1G_eq_class3 {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (hy0 : ∑ i, y i = 0) (z : ι → ZMod 2) :
    (M1G a z).det = ∑ P : Finpartition (univ : Finset ι),
      (if ∀ B ∈ P.parts, ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1 then
        ∏ B ∈ P.parts, redeiG a y z B else 0) := by
  rw [det_M1G hrec, hy0, add_zero, mul_one, det_Pmat_eq_class3 hrec]

/-- **Proposition 3.3** (tyz-5b §3.1), case `y(V) = 1`: `det M₁ = 0`. -/
theorem det_M1G_eq_zero {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (hy1 : ∑ i, y i = 1) (z : ι → ZMod 2) : (M1G a z).det = 0 := by
  rw [det_M1G hrec, hy1, CharTwo.add_self_eq_zero, mul_zero]

end ZInQ.RouteK.Rank5b.Sec3
