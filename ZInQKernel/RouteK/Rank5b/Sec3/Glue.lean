import ZInQKernel.RouteK.Rank5b.Sec3.M5bForest

/-!
# Forests and set partitions: gluing

* `allF U`: all forests on `U` (every root set); `mem_allF`: the maps that are the identity off `U`,
  map `U` into `U` and have no cycles;
* `sum_allF`: `Σ_{F ⊆ U} Σ_{f rooted at F} H(F, f) = Σ_{f ∈ allF U} H(roots f, f)`;
* `Finpartition.ofPartFun`: the set partition of `ι` given by a part function, and
  `eq_ofPartFun_part`: a set partition is determined by its part function;
* `prod_sum_allF` (**gluing**): for a set partition `P` of `ι`,
  `Π_{B∈P} Σ_{g ∈ allF B} h_B(g) = Σ_f Π_{B∈P} h_B(f|_B)` over the forests `f` of `ι` that map every
  block into itself.
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### All forests on a set -/

/-- The roots (fixed points) of `g` in `U`. -/
def rootsOf (U : Finset ι) (g : ι → ι) : Finset ι := U.filter fun i => g i = i

/-- All forests on `U`. -/
def allF (U : Finset ι) : Finset (ι → ι) := U.powerset.biUnion fun F => forests U F

theorem rootsOf_of_forests {U F : Finset ι} (hFU : F ⊆ U) {f : ι → ι} (hf : f ∈ forests U F) :
    rootsOf U f = F := by
  have hm := (mem_forests.1 hf).1
  ext i
  simp only [rootsOf, Finset.mem_filter]
  constructor
  · rintro ⟨hiU, hfi⟩
    by_contra hiF
    exact ne_of_mem hm (Finset.mem_sdiff.2 ⟨hiU, hiF⟩) hfi
  · intro hiF
    exact ⟨hFU hiF, (mem_mapsOn.1 hm).1 i fun h => (Finset.mem_sdiff.1 h).2 hiF⟩

theorem mem_allF {U : Finset ι} {g : ι → ι} :
    g ∈ allF U ↔ (∀ i, i ∉ U → g i = i) ∧ (∀ i ∈ U, g i ∈ U) ∧ IsAcyc g := by
  constructor
  · intro h
    obtain ⟨F, hF, hg⟩ := Finset.mem_biUnion.1 h
    obtain ⟨hm, hac⟩ := mem_forests.1 hg
    refine ⟨fun i hi => (mem_mapsOn.1 hm).1 i fun h => hi (Finset.mem_sdiff.1 h).1,
      fun i hi => ?_, hac⟩
    by_cases h' : i ∈ U \ F
    · exact ((mem_mapsOn.1 hm).2 i h').1
    · rw [(mem_mapsOn.1 hm).1 i h']; exact hi
  · rintro ⟨hid, hmap, hac⟩
    refine Finset.mem_biUnion.2 ⟨rootsOf U g, Finset.mem_powerset.2 (Finset.filter_subset _ _),
      mem_forests.2 ⟨mem_mapsOn.2 ⟨fun i hi => ?_, fun i hi => ?_⟩, hac⟩⟩
    · by_cases hiU : i ∈ U
      · by_contra hne
        exact hi (Finset.mem_sdiff.2 ⟨hiU, fun h => hne (Finset.mem_filter.1 h).2⟩)
      · exact hid i hiU
    · obtain ⟨hiU, hnr⟩ := Finset.mem_sdiff.1 hi
      exact ⟨hmap i hiU, fun h => hnr (Finset.mem_filter.2 ⟨hiU, h⟩)⟩

theorem mem_forests_rootsOf {U : Finset ι} {g : ι → ι} (hg : g ∈ allF U) :
    g ∈ forests U (rootsOf U g) := by
  obtain ⟨F, hF, hgF⟩ := Finset.mem_biUnion.1 hg
  rwa [rootsOf_of_forests (Finset.mem_powerset.1 hF) hgF]

/-- `Σ_{F ⊆ U} Σ_{f rooted at F} H(F, f) = Σ_{f ∈ allF U} H(roots f, f)`. -/
theorem sum_allF (U : Finset ι) (H : Finset ι → (ι → ι) → ZMod 2) :
    ∑ F ∈ U.powerset, ∑ f ∈ forests U F, H F f = ∑ g ∈ allF U, H (rootsOf U g) g := by
  rw [allF, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun F hF => Finset.sum_congr rfl fun f hf => ?_
    rw [rootsOf_of_forests (Finset.mem_powerset.1 hF) hf]
  · intro F hF F' hF' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro f h1 h2
    exact hne ((rootsOf_of_forests (Finset.mem_powerset.1 hF) h1).symm.trans
      (rootsOf_of_forests (Finset.mem_powerset.1 hF') h2))

/-! ### Set partitions from part functions -/

/-- The set partition of `ι` with part function `b`. -/
def ofPartFun (b : ι → Finset ι) (h1 : ∀ i, i ∈ b i) (h2 : ∀ i j, j ∈ b i → b j = b i) :
    Finpartition (univ : Finset ι) :=
  Finpartition.ofExistsUnique (univ.image b) (fun _ _ => Finset.subset_univ _)
    (fun a _ => ⟨b a, ⟨Finset.mem_image_of_mem b (Finset.mem_univ a), h1 a⟩,
      fun t ⟨ht, hat⟩ => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
        exact (h2 i a hat).symm⟩)
    (by
      intro h
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      have := h1 i
      rw [hi] at this
      exact Finset.notMem_empty i this)

theorem part_ofPartFun (b : ι → Finset ι) (h1 : ∀ i, i ∈ b i) (h2 : ∀ i j, j ∈ b i → b j = b i)
    (i : ι) : (ofPartFun b h1 h2).part i = b i :=
  Finpartition.part_eq_of_mem _ (Finset.mem_image_of_mem b (Finset.mem_univ i)) (h1 i)

theorem parts_eq_image_part (P : Finpartition (univ : Finset ι)) :
    P.parts = univ.image P.part := by
  ext B
  constructor
  · intro hB
    obtain ⟨i, hi⟩ := Finpartition.nonempty_of_mem_parts P hB
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, P.part_eq_of_mem hB hi⟩
  · intro hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
    exact P.part_mem.2 (Finset.mem_univ i)

theorem finpartition_ext_part {P Q : Finpartition (univ : Finset ι)}
    (h : ∀ i, P.part i = Q.part i) : P = Q := by
  apply Finpartition.ext
  rw [parts_eq_image_part, parts_eq_image_part]
  exact Finset.image_congr fun i _ => h i

theorem mem_part_univ (P : Finpartition (univ : Finset ι)) (i : ι) : i ∈ P.part i :=
  P.mem_part_self.2 (Finset.mem_univ i)

theorem part_mem_univ (P : Finpartition (univ : Finset ι)) (i : ι) : P.part i ∈ P.parts :=
  P.part_mem.2 (Finset.mem_univ i)

theorem part_eq_part_of_mem (P : Finpartition (univ : Finset ι)) {i j : ι} (h : j ∈ P.part i) :
    P.part j = P.part i :=
  P.part_eq_of_mem (part_mem_univ P i) h

/-! ### Gluing -/

/-- `f` restricted to `B` (the identity off `B`). -/
def restrict (B : Finset ι) (f : ι → ι) : ι → ι := fun i => if i ∈ B then f i else i

theorem iterate_agree {B : Finset ι} {f g : ι → ι} (hg : ∀ i ∈ B, g i ∈ B)
    (hfg : ∀ i ∈ B, f i = g i) (k : ℕ) : ∀ i ∈ B, f^[k] i = g^[k] i ∧ g^[k] i ∈ B := by
  induction k with
  | zero => exact fun i hi => ⟨rfl, hi⟩
  | succ k ih =>
    intro i hi
    obtain ⟨h1, h2⟩ := ih i hi
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, hfg _ h2]
    exact ⟨rfl, hg _ h2⟩

/-- A map that agrees on `B` with a map `g` preserving `B` has, on `B`, the same roots as `g`. -/
theorem root_agree {B : Finset ι} {f g : ι → ι} (hg : ∀ i ∈ B, g i ∈ B)
    (hfg : ∀ i ∈ B, f i = g i) {i : ι} (hi : i ∈ B) : root f i = root g i ∧ root g i ∈ B :=
  iterate_agree hg hfg _ i hi

theorem restrict_mem_allF {f : ι → ι} (hf : f ∈ allF (univ : Finset ι)) {B : Finset ι}
    (hB : ∀ i ∈ B, f i ∈ B) : restrict B f ∈ allF B := by
  obtain ⟨-, -, hac⟩ := mem_allF.1 hf
  have hrB : ∀ i ∈ B, restrict B f i ∈ B := fun i hi => by simp [restrict, hi, hB i hi]
  refine mem_allF.2 ⟨fun i hi => by simp [restrict, hi], hrB, fun i => ?_⟩
  by_cases hi : i ∈ B
  · obtain ⟨h1, h2⟩ := root_agree hrB (fun j _ => rfl) hi
    obtain ⟨h3, h4⟩ := root_agree (g := restrict B f) (f := f) hrB
      (fun j hj => by simp [restrict, hj]) hi
    rw [← h3]
    have : restrict B f (root f i) = f (root f i) := by simp [restrict, h3 ▸ h4]
    rw [this, hac i]
  · have hfix : restrict B f i = i := by simp [restrict, hi]
    rw [root_of_fixed hfix, hfix]

/-- **Gluing** forests along a set partition `P` of `ι`. -/
theorem prod_sum_allF (P : Finpartition (univ : Finset ι)) (h : Finset ι → (ι → ι) → ZMod 2) :
    ∏ B ∈ P.parts, ∑ g ∈ allF B, h B g =
      ∑ f ∈ (allF univ).filter (fun f => ∀ i, f i ∈ P.part i),
        ∏ B ∈ P.parts, h B (restrict B f) := by
  classical
  rw [Finset.prod_sum]
  refine Finset.sum_bij' (fun p _ j => p (P.part j) (part_mem_univ P j) j)
    (fun f _ B _ => restrict B f) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_pi] at hp
    have hpB : ∀ B (hB : B ∈ P.parts), (∀ i ∉ B, p B hB i = i) ∧ (∀ i ∈ B, p B hB i ∈ B) ∧
        IsAcyc (p B hB) := fun B hB => mem_allF.1 (hp B hB)
    have hglue : ∀ B (hB : B ∈ P.parts), ∀ i ∈ B,
        p (P.part i) (part_mem_univ P i) i = p B hB i := fun B hB i hi => by
      have : P.part i = B := P.part_eq_of_mem hB hi
      subst this
      rfl
    refine Finset.mem_filter.2 ⟨mem_allF.2 ⟨fun i hi => absurd (Finset.mem_univ i) hi,
      fun i _ => Finset.mem_univ _, fun i => ?_⟩, fun i => ?_⟩
    · set B := P.part i
      have hB := part_mem_univ P i
      obtain ⟨hid, hmap, hac⟩ := hpB B hB
      obtain ⟨h1, h2⟩ := root_agree hmap (hglue B hB) (mem_part_univ P i)
      rw [h1]
      dsimp only
      rw [hglue B hB _ h2, hac i]
    · exact (hpB _ _).2.1 i (mem_part_univ P i)
  · intro f hf
    rw [Finset.mem_pi]
    intro B hB
    obtain ⟨hf, hresp⟩ := Finset.mem_filter.1 hf
    exact restrict_mem_allF hf fun i hi => by
      rw [← P.part_eq_of_mem hB hi]; exact hresp i
  · intro p hp
    rw [Finset.mem_pi] at hp
    funext B hB x
    by_cases hx : x ∈ B
    · simp only [restrict, hx, if_true]
      have : P.part x = B := P.part_eq_of_mem hB hx
      subst this
      rfl
    · simp only [restrict, hx, if_false]
      exact ((mem_allF.1 (hp B hB)).1 x hx).symm
  · intro f _
    funext x
    simp [restrict, mem_part_univ P x]
  · intro p hp
    rw [← Finset.prod_attach P.parts]
    refine Finset.prod_congr rfl fun B _ => ?_
    congr 1
    rw [Finset.mem_pi] at hp
    funext x
    by_cases hx : x ∈ B.1
    · simp only [restrict, hx, if_true]
      have : P.part x = B.1 := P.part_eq_of_mem B.2 hx
      obtain ⟨B, hB⟩ := B
      simp only at this hx ⊢
      subst this
      rfl
    · simp only [restrict, hx, if_false]
      exact (mem_allF.1 (hp B.1 B.2)).1 x hx

end ZInQ.RouteK.Rank5b.Sec3
