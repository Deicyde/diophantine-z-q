import ZInQKernel.RouteK.Rank5b.Sec3.Genus

/-!
# Theorem 3.6 (Smith's row 5b): `T_5b = det M_5b`

`genusSum5b_eq_forest`: under reciprocity and `y(V) = 0`,
`T_5b = Σ_{f forest of ι} (Σ_{k root} y_k z^{R∖k}) wt(f) Π_{ρ root} y(T_ρ)`:
the marked form of `T_5b`, each block weight written as a forest sum (`w7_eq`, `w3_eq`, `w1_eq`),
glued along the partition (`prod_sum_allF`); for a fixed forest the compatible marked partitions are
counted by the pairings of the remaining roots (`card_setA`, `card_fpfi`), an odd number.

`det_M5bG_eq_genusSum5b` (**Theorem 3.6**, generic): with `det_M5bG_forest` (Proposition 3.4,
forest form), `det M_5b = T_5b` for bits with reciprocity and `y(V) = 0`.
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prod_parts_inter (P : Finpartition (univ : Finset ι)) (S : Finset ι) (φ : ι → ZMod 2) :
    ∏ B ∈ P.parts, ∏ i ∈ B ∩ S, φ i = ∏ i ∈ S, φ i := by
  rw [← Finset.prod_biUnion]
  · congr 1
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨B, -, -, h⟩; exact h
    · intro h; exact ⟨P.part i, part_mem_univ P i, mem_part_univ P i, h⟩
  · intro B hB B' hB' hne
    simp only [Function.onFun]
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (P.disjoint hB hB' hne))

/-- The block factor of a marked partition, as a function of the roots `S = B ∩ R` of the block. -/
def markE (y z : ι → ZMod 2) (B7 B3 B S : Finset ι) : ZMod 2 :=
  if B = B7 then (if S.card = 1 then ∑ ρ ∈ S, (y ρ + z ρ) else 0)
  else if B = B3 then (if S.card = 1 then ∏ ρ ∈ S, z ρ else 0)
  else (if S.card = 2 then ∏ ρ ∈ S, z ρ else 0)

/-- The forest weight of a block of a marked partition. -/
def markH (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (B7 B3 B : Finset ι) (g : ι → ι) : ZMod 2 :=
  if B = B7 then blockH a y 1 (fun F => ∑ ρ ∈ F, (y ρ + z ρ)) B g
  else if B = B3 then blockH a y 1 (fun F => ∏ ρ ∈ F, z ρ) B g
  else blockH a y 2 (fun F => ∏ ρ ∈ F, z ρ) B g

theorem markW_eq {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2)
    (B7 B3 B : Finset ι) : markW a y z B7 B3 B = ∑ g ∈ allF B, markH a y z B7 B3 B g := by
  unfold markW markH
  split_ifs
  · exact w7_eq hrec z B
  · exact w3_eq hrec z B
  · exact w1_eq hrec z B

theorem rootsOf_restrict (B : Finset ι) (f : ι → ι) :
    rootsOf B (restrict B f) = B ∩ rootsOf univ f := by
  ext i
  rw [Finset.mem_inter]
  unfold rootsOf
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, restrict]
  constructor
  · rintro ⟨hi, h⟩; rw [if_pos hi] at h; exact ⟨hi, h⟩
  · rintro ⟨hi, h⟩; exact ⟨hi, by rw [if_pos hi]; exact h⟩

/-- **Evaluation of a glued product**: for a forest `f` compatible with `P`,
`Π_B markH(B, f|_B) = (Π_B markE(B, B ∩ R)) wt(f) Π_{ρ∈R} y(T_ρ)`. -/
theorem prod_markH_restrict (a : ι → ι → ZMod 2) (y z : ι → ZMod 2)
    (P : Finpartition (univ : Finset ι)) {f : ι → ι} (hf : f ∈ allF (univ : Finset ι))
    (hP : Resp f P) (B7 B3 : Finset ι) :
    ∏ B ∈ P.parts, markH a y z B7 B3 B (restrict B f) =
      (∏ B ∈ P.parts, markE y z B7 B3 B (B ∩ rootsOf univ f)) *
        wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f := by
  set R := rootsOf univ f
  have hac := (mem_allF.1 hf).2.2
  have hblock : ∀ B ∈ P.parts, markH a y z B7 B3 B (restrict B f) =
      markE y z B7 B3 B (B ∩ R) * (∏ i ∈ B ∩ (univ \ R), a i (f i)) *
        ∏ ρ ∈ B ∩ R, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v := by
    intro B hB
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
    unfold markH markE blockH
    rw [rootsOf_restrict, hwt, htree]
    split_ifs <;> ring
  rw [Finset.prod_congr rfl hblock, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_parts_inter, prod_parts_inter, wt, treeY]

/-- For a compatible partition, the marked double sum over blocks is a double sum over roots. -/
theorem sum_marked_eq_roots (y z : ι → ZMod 2) {f : ι → ι} (hf : f ∈ allF (univ : Finset ι))
    {P : Finpartition (univ : Finset ι)} (hP : Resp f P) :
    ∑ B7 ∈ P.parts, ∑ B3 ∈ P.parts.erase B7, ∏ B ∈ P.parts, markE y z B7 B3 B (B ∩ rootsOf univ f) =
      ∑ ρ7 ∈ rootsOf univ f, ∑ ρ3 ∈ (rootsOf univ f).erase ρ7,
        if P ∈ setA f ρ7 ρ3 then (y ρ7 + z ρ7) * ∏ ρ ∈ (rootsOf univ f).erase ρ7, z ρ else 0 := by
  classical
  set R := rootsOf univ f
  -- the value of a marked product at a pair of roots
  have hval : ∀ ρ7 ρ3, P ∈ setA f ρ7 ρ3 → ρ7 ∈ R → ρ3 ∈ R.erase ρ7 →
      ∏ B ∈ P.parts, markE y z (P.part ρ7) (P.part ρ3) B (B ∩ R) =
        (y ρ7 + z ρ7) * ∏ ρ ∈ R.erase ρ7, z ρ := by
    intro ρ7 ρ3 hA h7 h3
    obtain ⟨-, -, hP7, hP3, hP2⟩ := Finset.mem_filter.1 hA
    replace hP7 : P.part ρ7 ∩ R = {ρ7} := hP7
    replace hP3 : P.part ρ3 ∩ R = {ρ3} := hP3
    replace hP2 : ∀ ρ ∈ R, ρ ≠ ρ7 → ρ ≠ ρ3 → (P.part ρ ∩ R).card = 2 := hP2
    obtain ⟨h37, h3R⟩ := Finset.mem_erase.1 h3
    have hne : P.part ρ3 ≠ P.part ρ7 := by
      intro h
      have : ρ3 ∈ P.part ρ7 ∩ R := by rw [← h]; exact Finset.mem_inter.2 ⟨mem_part_univ P ρ3, h3R⟩
      rw [hP7, Finset.mem_singleton] at this; exact h37 this
    set S := (R.erase ρ7).erase ρ3
    have hS : ∏ ρ ∈ R.erase ρ7, z ρ = z ρ3 * ∏ ρ ∈ S, z ρ :=
      (Finset.mul_prod_erase _ _ h3).symm
    rw [hS, ← prod_parts_inter P S z]
    rw [← Finset.mul_prod_erase _ _ (part_mem_univ P ρ7),
      ← Finset.mul_prod_erase _ _ (part_mem_univ P ρ7),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, part_mem_univ P ρ3⟩),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, part_mem_univ P ρ3⟩)]
    have hS7 : P.part ρ7 ∩ S = ∅ := by
      ext i; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hi hiS
      have : i ∈ P.part ρ7 ∩ R := Finset.mem_inter.2 ⟨hi,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hiS)⟩
      rw [hP7, Finset.mem_singleton] at this
      exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hiS) this
    have hS3 : P.part ρ3 ∩ S = ∅ := by
      ext i; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hi hiS
      have : i ∈ P.part ρ3 ∩ R := Finset.mem_inter.2 ⟨hi,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hiS)⟩
      rw [hP3, Finset.mem_singleton] at this
      exact Finset.ne_of_mem_erase hiS this
    rw [hS7, hS3, Finset.prod_empty, one_mul, one_mul]
    unfold markE
    simp only [eq_self_iff_true, if_true, if_neg hne, hP7, hP3, Finset.card_singleton,
      Finset.sum_singleton, Finset.prod_singleton]
    congr 2
    refine Finset.prod_congr rfl fun B hB => ?_
    obtain ⟨hB3, hB'⟩ := Finset.mem_erase.1 hB
    obtain ⟨hB7, hBp⟩ := Finset.mem_erase.1 hB'
    rw [if_neg hB7, if_neg hB3]
    -- `B` contains a root other than `ρ₇, ρ₃`, so it contains exactly two roots
    obtain ⟨i, hi⟩ := Finpartition.nonempty_of_mem_parts P hBp
    have hBi : P.part i = B := P.part_eq_of_mem hBp hi
    set ρ := root f i
    have hρR : ρ ∈ R := root_mem_rootsOf hf i
    have hBρ : P.part ρ = B := by rw [part_root hP, hBi]
    have hρ7 : ρ ≠ ρ7 := fun h => hB7 (by rw [← hBρ, h])
    have hρ3 : ρ ≠ ρ3 := fun h => hB3 (by rw [← hBρ, h])
    have h2 := hP2 ρ hρR hρ7 hρ3
    rw [hBρ] at h2
    rw [if_pos h2]
    have : B ∩ S = B ∩ R := by
      ext j
      simp only [Finset.mem_inter, S, Finset.mem_erase]
      constructor
      · rintro ⟨hj, -, -, hjR⟩; exact ⟨hj, hjR⟩
      · rintro ⟨hj, hjR⟩
        refine ⟨hj, fun h => hB3 ?_, fun h => hB7 ?_, hjR⟩
        · rw [← P.part_eq_of_mem hBp hj, h]
        · rw [← P.part_eq_of_mem hBp hj, h]
    rw [this]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => ⟨P.part p.1, P.part p.2⟩) ?_ ?_ ?_ ?_
  · intro p hp hne
    obtain ⟨h7, h3⟩ := Finset.mem_sigma.1 hp
    have hA : P ∈ setA f p.1 p.2 := by by_contra h; exact hne (if_neg h)
    obtain ⟨-, -, hP7, -, -⟩ := Finset.mem_filter.1 hA
    obtain ⟨h37, h3R⟩ := Finset.mem_erase.1 h3
    refine Finset.mem_sigma.2 ⟨part_mem_univ P _, Finset.mem_erase.2 ⟨fun h => h37 ?_,
      part_mem_univ P _⟩⟩
    simp only at h
    have : p.2 ∈ P.part p.1 ∩ R := by rw [← h]; exact Finset.mem_inter.2 ⟨mem_part_univ P _, h3R⟩
    rw [hP7, Finset.mem_singleton] at this; exact this
  · intro p hp hne q hq hne' h
    have hA : P ∈ setA f p.1 p.2 := by by_contra h'; exact hne (if_neg h')
    have hA' : P ∈ setA f q.1 q.2 := by by_contra h'; exact hne' (if_neg h')
    obtain ⟨-, -, hP7, hP3, -⟩ := Finset.mem_filter.1 hA
    obtain ⟨h7q, h3q⟩ := Finset.mem_sigma.1 hq
    have h3qR := (Finset.mem_erase.1 h3q).2
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : q.1 = p.1 := by
      have : q.1 ∈ P.part p.1 ∩ R := by rw [h1]; exact Finset.mem_inter.2 ⟨mem_part_univ P _, h7q⟩
      rw [hP7, Finset.mem_singleton] at this; exact this
    have e2 : q.2 = p.2 := by
      have : q.2 ∈ P.part p.2 ∩ R := by rw [h2]; exact Finset.mem_inter.2 ⟨mem_part_univ P _, h3qR⟩
      rw [hP3, Finset.mem_singleton] at this; exact this
    exact Sigma.ext e1.symm (heq_of_eq e2.symm)
  · intro x hx hne
    obtain ⟨hB7, hB3⟩ := Finset.mem_sigma.1 hx
    obtain ⟨h37, hB3p⟩ := Finset.mem_erase.1 hB3
    have hfac := Finset.prod_ne_zero_iff.1 hne
    have hc7 : (x.1 ∩ R).card = 1 := by
      have := hfac x.1 hB7
      unfold markE at this
      rw [if_pos rfl] at this
      by_contra h; exact this (if_neg h)
    have hc3 : (x.2 ∩ R).card = 1 := by
      have := hfac x.2 hB3p
      unfold markE at this
      rw [if_neg h37, if_pos rfl] at this
      by_contra h; exact this (if_neg h)
    have hc1 : ∀ B ∈ P.parts, B ≠ x.1 → B ≠ x.2 → (B ∩ R).card = 2 := fun B hB h1 h2 => by
      have := hfac B hB
      unfold markE at this
      rw [if_neg h1, if_neg h2] at this
      by_contra h; exact this (if_neg h)
    obtain ⟨ρ7, hρ7⟩ := Finset.card_eq_one.1 hc7
    obtain ⟨ρ3, hρ3⟩ := Finset.card_eq_one.1 hc3
    have hm7 : ρ7 ∈ x.1 ∩ R := by rw [hρ7]; exact Finset.mem_singleton_self _
    have hm3 : ρ3 ∈ x.2 ∩ R := by rw [hρ3]; exact Finset.mem_singleton_self _
    have hp7 : P.part ρ7 = x.1 := P.part_eq_of_mem hB7 (Finset.mem_inter.1 hm7).1
    have hp3 : P.part ρ3 = x.2 := P.part_eq_of_mem hB3p (Finset.mem_inter.1 hm3).1
    have h73 : ρ3 ≠ ρ7 := fun h => h37 (by rw [← hp3, ← hp7, h])
    have hA : P ∈ setA f ρ7 ρ3 := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hP, by rw [hp7, hρ7], by rw [hp3, hρ3],
        fun ρ hρ hρ7' hρ3' => hc1 _ (part_mem_univ P ρ) ?_ ?_⟩
      · intro h
        have : ρ ∈ x.1 ∩ R := by rw [← h]; exact Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩
        rw [hρ7, Finset.mem_singleton] at this; exact hρ7' this
      · intro h
        have : ρ ∈ x.2 ∩ R := by rw [← h]; exact Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩
        rw [hρ3, Finset.mem_singleton] at this; exact hρ3' this
    have h7R := (Finset.mem_inter.1 hm7).2
    have h3R : ρ3 ∈ R.erase ρ7 := Finset.mem_erase.2 ⟨h73, (Finset.mem_inter.1 hm3).2⟩
    refine ⟨⟨ρ7, ρ3⟩, Finset.mem_sigma.2 ⟨h7R, h3R⟩, ?_, ?_⟩
    · simp only
      rw [if_pos hA, ← hval ρ7 ρ3 hA h7R h3R, hp7, hp3]
      exact hne
    · simp only [hp7, hp3]
  · intro p hp hne
    obtain ⟨h7, h3⟩ := Finset.mem_sigma.1 hp
    have hA : P ∈ setA f p.1 p.2 := by by_contra h; exact hne (if_neg h)
    simp only
    rw [if_pos hA, hval p.1 p.2 hA h7 h3]

/-- If every tree has `y(T) = 1` and `y(V) = 0`, the number of trees is even. -/
theorem even_card_roots {y : ι → ZMod 2} (hy0 : ∑ i, y i = 0) {f : ι → ι}
    (hf : f ∈ allF (univ : Finset ι)) (h : treeY y univ (rootsOf univ f) f ≠ 0) :
    Even (rootsOf univ f).card := by
  have hall : ∀ ρ ∈ rootsOf univ f, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v = 1 :=
    fun ρ hρ => (zmod2_cases _).resolve_left (Finset.prod_ne_zero_iff.1 h ρ hρ)
  have hsum : ∑ i, y i = ∑ ρ ∈ rootsOf univ f, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v :=
    (Finset.sum_fiberwise_of_maps_to (fun v _ => root_mem_rootsOf hf v) y).symm
  rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one, hy0] at hsum
  exact ZMod.natCast_eq_zero_iff_even.1 hsum.symm

/-- For a forest with an even number of trees, the compatible marked partitions contribute
`Σ_{k root} y_k z^{R∖k}`. -/
theorem sum_compat_marked (y z : ι → ZMod 2) {f : ι → ι} (hf : f ∈ allF (univ : Finset ι))
    (heven : Even (rootsOf univ f).card) :
    ∑ P : Finpartition (univ : Finset ι), (if Resp f P then ∑ B7 ∈ P.parts,
      ∑ B3 ∈ P.parts.erase B7, ∏ B ∈ P.parts, markE y z B7 B3 B (B ∩ rootsOf univ f) else 0) =
      ∑ k ∈ rootsOf univ f, y k * ∏ ρ ∈ (rootsOf univ f).erase k, z ρ := by
  classical
  set R := rootsOf univ f
  set c : ι → ZMod 2 := fun ρ7 => (y ρ7 + z ρ7) * ∏ ρ ∈ R.erase ρ7, z ρ
  have h1 : ∀ P : Finpartition (univ : Finset ι), (if Resp f P then ∑ B7 ∈ P.parts,
      ∑ B3 ∈ P.parts.erase B7, ∏ B ∈ P.parts, markE y z B7 B3 B (B ∩ R) else 0) =
      ∑ ρ7 ∈ R, ∑ ρ3 ∈ R.erase ρ7, if P ∈ setA f ρ7 ρ3 then c ρ7 else 0 := by
    intro P
    split_ifs with hP
    · exact sum_marked_eq_roots y z hf hP
    · symm
      exact Finset.sum_eq_zero fun ρ7 _ => Finset.sum_eq_zero fun ρ3 _ =>
        if_neg fun hA => hP (Finset.mem_filter.1 hA).2.1
  rw [Finset.sum_congr rfl fun P _ => h1 P, Finset.sum_comm]
  have h2 : ∀ ρ7 ∈ R, ∑ P : Finpartition (univ : Finset ι), ∑ ρ3 ∈ R.erase ρ7,
      (if P ∈ setA f ρ7 ρ3 then c ρ7 else 0) = c ρ7 := by
    intro ρ7 h7
    rw [Finset.sum_comm]
    have h3 : ∀ ρ3 ∈ R.erase ρ7, ∑ P : Finpartition (univ : Finset ι),
        (if P ∈ setA f ρ7 ρ3 then c ρ7 else 0) = c ρ7 := by
      intro ρ3 h3
      obtain ⟨h37, h3R⟩ := Finset.mem_erase.1 h3
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
        card_setA hf h7 h3R (Ne.symm h37), card_fpfi]
      have hc : ((R.erase ρ7).erase ρ3).card = R.card - 2 := by
        rw [Finset.card_erase_of_mem h3, Finset.card_erase_of_mem h7]; omega
      have hR2 : 2 ≤ R.card := by
        have := Finset.card_le_card (show {ρ7, ρ3} ⊆ R by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
        rwa [Finset.card_pair (Ne.symm h37)] at this
      rw [hc, if_pos ((Nat.even_sub hR2).2 (by simp [heven, even_two])), one_mul]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem h7]
    have hodd : Odd (R.card - 1) := by
      have : 1 ≤ R.card := Finset.card_pos.2 ⟨ρ7, h7⟩
      exact (Nat.odd_sub this).2 (by simp [heven])
    rw [ZMod.natCast_eq_one_iff_odd.2 hodd, one_mul]
  rw [Finset.sum_congr rfl h2]
  simp only [c, add_mul, Finset.sum_add_distrib]
  have h4 : ∑ ρ7 ∈ R, z ρ7 * ∏ ρ ∈ R.erase ρ7, z ρ = 0 := by
    rw [Finset.sum_congr rfl fun ρ7 h7 => Finset.mul_prod_erase R z h7, Finset.sum_const,
      nsmul_eq_mul, ZMod.natCast_eq_zero_iff_even.2 heven, zero_mul]
  rw [h4, add_zero]

/-- **The genus sum as a forest sum**: under reciprocity and `y(V) = 0`,
`T_5b = Σ_{f forest of ι} (Σ_{k root} y_k z^{R∖k}) wt(f) Π_{ρ root} y(T_ρ)`. -/
theorem genusSum5b_eq_forest {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (hy0 : ∑ i, y i = 0) (z : ι → ZMod 2) :
    genusSum5b a y z = ∑ g ∈ allF (univ : Finset ι),
      (∑ k ∈ rootsOf univ g, y k * ∏ ρ ∈ (rootsOf univ g).erase k, z ρ) *
        (wt a (univ \ rootsOf univ g) g * treeY y univ (rootsOf univ g) g) := by
  classical
  rw [genusSum5b_eq_marked]
  have step : ∀ (P : Finpartition (univ : Finset ι)) (B7 B3 : Finset ι),
      ∏ B ∈ P.parts, markW a y z B7 B3 B = ∑ f ∈ allF (univ : Finset ι),
        if Resp f P then (∏ B ∈ P.parts, markE y z B7 B3 B (B ∩ rootsOf univ f)) *
          (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) else 0 := by
    intro P B7 B3
    rw [Finset.prod_congr rfl fun B _ => markW_eq hrec z B7 B3 B, prod_sum_allF, Finset.sum_filter]
    refine Finset.sum_congr rfl fun f hf => ?_
    by_cases hP : Resp f P
    · rw [if_pos hP, if_pos (show ∀ i, f i ∈ P.part i from hP), prod_markH_restrict a y z P hf hP,
        mul_assoc]
    · rw [if_neg hP, if_neg (show ¬∀ i, f i ∈ P.part i from hP)]
  simp_rw [step]
  have swap : ∀ P : Finpartition (univ : Finset ι),
      (∑ B7 ∈ P.parts, ∑ B3 ∈ P.parts.erase B7, ∑ f ∈ allF (univ : Finset ι),
        if Resp f P then (∏ B ∈ P.parts, markE y z B7 B3 B (B ∩ rootsOf univ f)) *
          (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) else 0) =
      ∑ f ∈ allF (univ : Finset ι), (if Resp f P then ∑ B7 ∈ P.parts, ∑ B3 ∈ P.parts.erase B7,
        ∏ B ∈ P.parts, markE y z B7 B3 B (B ∩ rootsOf univ f) else 0) *
          (wt a (univ \ rootsOf univ f) f * treeY y univ (rootsOf univ f) f) := by
    intro P
    rw [Finset.sum_congr rfl fun B7 _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hP : Resp f P
    · simp only [if_pos hP, Finset.sum_mul]
    · simp only [if_neg hP, Finset.sum_const_zero, zero_mul]
  rw [Finset.sum_congr rfl fun P _ => swap P, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [← Finset.sum_mul]
  by_cases htree : treeY y univ (rootsOf univ f) f = 0
  · rw [htree, mul_zero, mul_zero, mul_zero]
  · rw [sum_compat_marked y z hf (even_card_roots hy0 hf htree)]

/-- **Theorem 3.6** (Smith's Theorem 2.2, row 5b; tyz-5b §3.3), for bits: under reciprocity and
`y(V) = 0`, `det M_5b = T_5b`. -/
theorem det_M5bG_eq_genusSum5b {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (hy0 : ∑ i, y i = 0) (z : ι → ZMod 2) : (M5bG a y z).det = genusSum5b a y z := by
  rw [det_M5bG_forest hrec, hy0, add_zero, one_mul, genusSum5b_eq_forest hrec hy0,
    ← sum_allF univ (fun F f => (∑ k ∈ F, y k * ∏ ρ ∈ F.erase k, z ρ) *
      (wt a (univ \ F) f * treeY y univ F f))]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [Finset.mul_sum]
  rfl

end ZInQ.RouteK.Rank5b.Sec3
