import ZInQKernel.RouteK.Rank5b.Sec3.Perm

/-!
# The forest lemma (tyz-5b Lemma 2.1)

A map `f : ι → ι` is a *forest on `U` rooted at `F`* (`F ⊆ U`) if it is the identity off `U ∖ F`,
maps `U ∖ F` into `U` without fixed points, and has no cycles: every point reaches a fixed point
(`IsAcyc f`: the point `root f i = f^[#ι] i` is fixed). The trees are the fibres of `root f`; the weight
is `wt a R f = Π_{i∈R} a_{i f(i)}`, `R = U ∖ F`.

**Lemma 2.1** (`pmin_lapl_eq_forests`). For `F, W ⊆ U` with `|F| = |W|`,
`det L_U[U∖F, U∖W] = Σ wt(f)` over the forests `f` on `U` rooted at `F` in which every tree contains
exactly one element of `W` (`IsTransv f F W`).

Proof (tyz-5b §2.1): expanding the diagonal entries of the permanent gives
`Σ_f wt(f) · #compat(f)` over all maps `f` (`pmin_lapl_eq_sum_maps`), where `compat(f)` is the set
of bijections `σ : U∖F → U∖W` with `σ(i) ∈ {i, f(i)}`. If `f` has a cycle, toggling `σ` on it is a
fixed-point-free involution of `compat(f)` (`card_compat_even`). If `f` is a forest, `compat(f)` has
at most one element, `σ_W = f` on the paths from `W` and the identity elsewhere (`eq_sigmaW`),
and `σ_W ∈ compat(f)` iff every tree contains exactly one element of `W` (`sigmaW_mem_iff`).
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The maps on `U` with moving set `R`: the identity off `R`, and `f i ∈ U`, `f i ≠ i` on `R`. -/
def mapsOn (U R : Finset ι) : Finset (ι → ι) :=
  univ.filter fun f => (∀ i, i ∉ R → f i = i) ∧ ∀ i ∈ R, f i ∈ U ∧ f i ≠ i

/-- The weight `Π_{i∈R} a_{i f(i)}`. -/
def wt (a : ι → ι → ZMod 2) (R : Finset ι) (f : ι → ι) : ZMod 2 := ∏ i ∈ R, a i (f i)

/-- The bijections `R → C` compatible with `f`: `σ(i) ∈ {i, f(i)}`. -/
def compat (R C : Finset ι) (f : ι → ι) : Finset (ι → ι) :=
  (bijFun R C).filter fun σ => ∀ i ∈ R, σ i = i ∨ σ i = f i

/-- The root of `i`: `f^[#ι] i`. -/
def root (f : ι → ι) (i : ι) : ι := f^[Fintype.card ι] i

/-- `f` has no cycles: every root is a fixed point. -/
def IsAcyc (f : ι → ι) : Prop := ∀ i, f (root f i) = root f i

instance (f : ι → ι) : Decidable (IsAcyc f) := by unfold IsAcyc; infer_instance

/-- The forests on `U` rooted at `F`. -/
def forests (U F : Finset ι) : Finset (ι → ι) := (mapsOn U (U \ F)).filter IsAcyc

/-- Every tree (fibre of `root f` over `ρ ∈ F`) contains exactly one element of `W`. -/
def IsTransv (f : ι → ι) (F W : Finset ι) : Prop :=
  ∀ ρ ∈ F, (W.filter fun w => root f w = ρ).card = 1

instance (f : ι → ι) (F W : Finset ι) : Decidable (IsTransv f F W) := by
  unfold IsTransv; infer_instance

theorem mem_mapsOn {U R : Finset ι} {f : ι → ι} :
    f ∈ mapsOn U R ↔ (∀ i, i ∉ R → f i = i) ∧ ∀ i ∈ R, f i ∈ U ∧ f i ≠ i := by
  simp [mapsOn]

theorem mem_compat {R C : Finset ι} {f σ : ι → ι} :
    σ ∈ compat R C f ↔ σ ∈ bijFun R C ∧ ∀ i ∈ R, σ i = i ∨ σ i = f i := by
  simp [compat]

theorem mem_forests {U F : Finset ι} {f : ι → ι} :
    f ∈ forests U F ↔ f ∈ mapsOn U (U \ F) ∧ IsAcyc f := by
  simp [forests]

/-! ### Step 1: expanding the diagonal -/

/-- **Expansion of the diagonal entries**: `pmin L_U R C = Σ_f wt(f) · #compat(f)`. -/
theorem pmin_lapl_eq_sum_maps (a : ι → ι → ZMod 2) {U R C : Finset ι} (hCU : C ⊆ U) :
    pmin (lapl a U) R C = ∑ f ∈ mapsOn U R, wt a R f * ((compat R C f).card : ZMod 2) := by
  classical
  have hσ : ∀ σ ∈ bijFun R C, ∏ i ∈ R, lapl a U i (σ i) =
      ∑ f ∈ (mapsOn U R).filter (fun f => ∀ i ∈ R, σ i = i ∨ σ i = f i), wt a R f := by
    intro σ hσ
    obtain ⟨hid, hmap, -, -⟩ := mem_bijFun.1 hσ
    let t : ι → Finset ι := fun i =>
      if i ∈ R then (if σ i = i then U.erase i else {σ i}) else {i}
    let g : ι → ι → ZMod 2 := fun i j => if i ∈ R then a i j else 1
    have h1 : ∏ i ∈ R, lapl a U i (σ i) = ∏ i, ∑ j ∈ t i, g i j := by
      rw [← Finset.prod_filter_mul_prod_filter_not univ (fun i => i ∈ R)]
      have hrest : ∏ i ∈ univ.filter (fun i => i ∉ R), ∑ j ∈ t i, g i j = 1 :=
        Finset.prod_eq_one fun i hi => by
          have hi' : i ∉ R := (Finset.mem_filter.1 hi).2
          simp [t, g, hi']
      rw [hrest, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
      refine Finset.prod_congr rfl fun i hi => ?_
      by_cases hs : σ i = i
      · simp [t, g, hi, hs, lapl]
      · simp [t, g, hi, hs, lapl, Ne.symm hs]
    rw [h1, Finset.prod_univ_sum]
    have h2 : Fintype.piFinset t = (mapsOn U R).filter (fun f => ∀ i ∈ R, σ i = i ∨ σ i = f i) := by
      ext f
      simp only [Fintype.mem_piFinset, Finset.mem_filter, mem_mapsOn]
      constructor
      · intro hf
        refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_⟩
        · have := hf i; simp only [t, hi, ite_false, Finset.mem_singleton] at this; exact this
        · have := hf i
          by_cases hs : σ i = i
          · simp only [t, hi, hs, ite_true, Finset.mem_erase] at this
            exact ⟨this.2, this.1⟩
          · simp only [t, hi, hs, ite_true, ite_false, Finset.mem_singleton] at this
            rw [this]; exact ⟨hCU (hmap i hi), hs⟩
        · have := hf i
          by_cases hs : σ i = i
          · exact Or.inl hs
          · simp only [t, hi, hs, ite_true, ite_false, Finset.mem_singleton] at this
            exact Or.inr this.symm
      · rintro ⟨⟨hfid, hfU⟩, hc⟩ i
        by_cases hi : i ∈ R
        · by_cases hs : σ i = i
          · simp only [t, hi, hs, ite_true, Finset.mem_erase]
            exact ⟨(hfU i hi).2, (hfU i hi).1⟩
          · simp only [t, hi, hs, ite_true, ite_false, Finset.mem_singleton]
            rcases hc i hi with h | h
            · exact absurd h hs
            · exact h.symm
        · simp only [t, hi, ite_false, Finset.mem_singleton]; exact hfid i hi
    rw [h2]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun i => i ∈ R)]
    have hrest : ∏ i ∈ univ.filter (fun i => i ∉ R), g i (f i) = 1 :=
      Finset.prod_eq_one fun i hi => by simp [g, (Finset.mem_filter.1 hi).2]
    rw [hrest, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter, wt]
    exact Finset.prod_congr rfl fun i hi => by simp [g, hi]
  unfold pmin
  rw [Finset.sum_congr rfl hσ, Finset.sum_comm' (t' := mapsOn U R)
    (s' := fun f => compat R C f)]
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro σ f
    simp only [Finset.mem_filter, mem_compat]
    tauto

/-! ### Iterates and roots -/

section Iter

variable {U F : Finset ι} {f : ι → ι}

theorem iterate_mem (hf : f ∈ mapsOn U (U \ F)) {x : ι} (hx : x ∈ U) (k : ℕ) : f^[k] x ∈ U := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : f^[k] x ∈ U \ F
    · exact ((mem_mapsOn.1 hf).2 _ h).1
    · rw [(mem_mapsOn.1 hf).1 _ h]; exact ih

theorem mem_of_ne (hf : f ∈ mapsOn U (U \ F)) {x : ι} (hx : f x ≠ x) : x ∈ U \ F := by
  by_contra h; exact hx ((mem_mapsOn.1 hf).1 x h)

theorem ne_of_mem (hf : f ∈ mapsOn U (U \ F)) {x : ι} (hx : x ∈ U \ F) : f x ≠ x :=
  ((mem_mapsOn.1 hf).2 x hx).2

theorem iterate_fixed' {x : ι} (hx : f x = x) (k : ℕ) : f^[k] x = x :=
  Function.iterate_fixed hx k

theorem iterate_comm (m n : ℕ) (x : ι) : f^[m] (f^[n] x) = f^[n] (f^[m] x) := by
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]

/-- (AC1) In an acyclic map, a periodic point is fixed. -/
theorem fixed_of_periodic (hac : IsAcyc f) {x : ι} {m : ℕ} (hm : 0 < m) (hx : f^[m] x = x) :
    f x = x := by
  set N := Fintype.card ι
  have hper : f^[m * N] x = x := by
    have := (show Function.IsPeriodicPt f m x from hx).mul_const N
    exact this
  have hle : N ≤ m * N := Nat.le_mul_of_pos_left N hm
  have : x = root f x := by
    calc x = f^[m * N] x := hper.symm
      _ = f^[m * N - N] (f^[N] x) := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
      _ = root f x := iterate_fixed' (hac x) _
  rw [this]; exact hac x

/-- (AC2) A map with a cycle has a periodic point that is not fixed. -/
theorem exists_periodic_of_not_acyc (hac : ¬IsAcyc f) :
    ∃ x, f x ≠ x ∧ ∃ p, 0 < p ∧ f^[p] x = x := by
  unfold IsAcyc at hac
  push_neg at hac
  obtain ⟨i, hi⟩ := hac
  set N := Fintype.card ι
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (N + 1) => f^[(k : ℕ)] i) (by simp [N])
  wlog hlt : (a : ℕ) < b generalizing a b
  · exact this b a hab.symm heq.symm (lt_of_le_of_ne (not_lt.1 hlt)
      (fun h => hab (Fin.ext h.symm)))
  refine ⟨root f i, hi, (b : ℕ) - a, Nat.sub_pos_of_lt hlt, ?_⟩
  have hy : f^[(b : ℕ) - a] (f^[(a : ℕ)] i) = f^[(a : ℕ)] i := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact heq.symm
  have ha : (a : ℕ) ≤ N := Nat.lt_succ_iff.1 a.2
  have : root f i = f^[N - a] (f^[(a : ℕ)] i) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel ha]; rfl
  rw [this, iterate_comm, hy]

theorem root_apply (hac : IsAcyc f) (x : ι) : root f (f x) = root f x := by
  unfold root
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  exact hac x

theorem root_iterate (hac : IsAcyc f) (x : ι) (k : ℕ) : root f (f^[k] x) = root f x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', root_apply hac, ih]

theorem root_mem (hf : f ∈ mapsOn U (U \ F)) {x : ι} (hx : x ∈ U) : root f x ∈ U :=
  iterate_mem hf hx _

theorem root_mem_F (hf : f ∈ mapsOn U (U \ F)) (hac : IsAcyc f) {x : ι} (hx : x ∈ U) :
    root f x ∈ F := by
  have h1 := root_mem hf hx
  by_contra h
  exact ne_of_mem hf (Finset.mem_sdiff.2 ⟨h1, h⟩) (hac x)

theorem root_of_fixed {x : ι} (hx : f x = x) : root f x = x := iterate_fixed' hx _

end Iter

/-! ### Step 2: maps with a cycle contribute an even number -/

section Cycle

variable {U F C : Finset ι} {f : ι → ι}

/-- If `f` has a cycle, `#compat(f)` is even. -/
theorem card_compat_even (hf : f ∈ mapsOn U (U \ F)) (hac : ¬IsAcyc f) :
    ((compat (U \ F) C f).card : ZMod 2) = 0 := by
  classical
  obtain ⟨x, hxf, p, hp, hpx⟩ := exists_periodic_of_not_acyc hac
  set R := U \ F with hR
  let inZ : ι → Prop := fun j => ∃ k, f^[k] x = j
  have Z1 : ∀ j, inZ j → inZ (f j) := fun j ⟨k, hk⟩ =>
    ⟨k + 1, by rw [Function.iterate_succ_apply', hk]⟩
  have Z2 : ∀ j, inZ j → f^[p] j = j := fun j ⟨k, hk⟩ => by rw [← hk, iterate_comm, hpx]
  have Z3 : ∀ j, inZ j → f j ≠ j := by
    rintro j ⟨k, rfl⟩ hfix
    apply hxf
    have hle : k ≤ p * k := Nat.le_mul_of_pos_left k hp
    have h1 : f^[p * k] x = x := (show Function.IsPeriodicPt f p x from hpx).mul_const k
    have : x = f^[k] x := by
      calc x = f^[p * k] x := h1.symm
        _ = f^[p * k - k] (f^[k] x) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
        _ = f^[k] x := iterate_fixed' hfix _
    rw [← this] at hfix; exact hfix
  have Z4 : ∀ j, inZ j → j ∈ R := fun j hj => mem_of_ne hf (Z3 j hj)
  have Z5 : ∀ j, inZ j → ∃ j', inZ j' ∧ f j' = j := fun j hj =>
    ⟨f^[p - 1] j, by obtain ⟨k, hk⟩ := hj; exact ⟨p - 1 + k, by rw [Function.iterate_add_apply, hk]⟩,
      by rw [← Function.iterate_succ_apply' f, Nat.succ_eq_add_one, Nat.sub_add_cancel hp, Z2 j hj]⟩
  have Z6 : ∀ u v, inZ u → inZ v → f u = f v → u = v := fun u v hu hv h => by
    rw [← Z2 u hu, ← Z2 v hv, ← Nat.sub_add_cancel hp, Function.iterate_succ_apply,
      Function.iterate_succ_apply, h]
  have hxZ : inZ x := ⟨0, rfl⟩
  -- dichotomy for a compatible σ
  have dich : ∀ σ ∈ compat R C f, (σ x = x → ∀ j, inZ j → σ j = j) ∧
      (σ x = f x → ∀ j, inZ j → σ j = f j) := by
    intro σ hσ
    obtain ⟨hb, hc⟩ := mem_compat.1 hσ
    have hinj := (mem_bijFun.1 hb).2.2.1
    have step : ∀ j, inZ j → σ j = f j → σ (f j) = f (f j) := fun j hj hs => by
      rcases hc (f j) (Z4 _ (Z1 j hj)) with h | h
      · exact absurd (hinj j (Z4 j hj) (f j) (Z4 _ (Z1 j hj)) (hs.trans h.symm)).symm (Z3 j hj)
      · exact h
    have prop : ∀ j, inZ j → σ j = f j → ∀ t, σ (f^[t] j) = f (f^[t] j) := by
      intro j hj hs t
      induction t with
      | zero => exact hs
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact step _ (by obtain ⟨k, hk⟩ := hj; exact ⟨t + k, by rw [Function.iterate_add_apply, hk]⟩) ih
    refine ⟨fun hx0 j hj => ?_, fun hx1 j hj => ?_⟩
    · rcases hc j (Z4 j hj) with h | h
      · exact h
      · exfalso
        obtain ⟨k, rfl⟩ := hj
        have := prop _ ⟨k, rfl⟩ h (p * (k + 1) - k)
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel
          (by nlinarith : k ≤ p * (k + 1)),
          (show Function.IsPeriodicPt f p x from hpx).mul_const (k + 1)] at this
        exact hxf (hx0.symm.trans this).symm
    · obtain ⟨k, rfl⟩ := hj
      have := prop x hxZ hx1 k
      exact this
  let tog : (ι → ι) → (ι → ι) := fun σ i =>
    if inZ i then (if σ x = x then f i else i) else σ i
  have hsum : ∑ _σ ∈ compat R C f, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun σ _ => tog σ) (fun _ _ => CharTwo.add_self_eq_zero 1)
      ?_ ?_ ?_
    · intro σ hσ _ heq
      have := congrFun heq x
      simp only [tog, hxZ, ite_true] at this
      by_cases h0 : σ x = x
      · rw [if_pos h0] at this; exact hxf (this.trans h0)
      · rw [if_neg h0] at this; exact h0 this.symm
    · intro σ hσ
      obtain ⟨hb, hc⟩ := mem_compat.1 hσ
      obtain ⟨hid, hmap, hinj, hcard⟩ := mem_bijFun.1 hb
      obtain ⟨d0, d1⟩ := dich σ hσ
      refine mem_compat.2 ⟨mem_bijFun.2 ⟨fun i hi => ?_, fun i hi => ?_, fun i hi j hj hij => ?_,
        hcard⟩, fun i hi => ?_⟩
      · have : ¬inZ i := fun h => hi (Z4 i h)
        simp [tog, this, hid i hi]
      · by_cases hz : inZ i
        · by_cases h0 : σ x = x
          · simp only [tog, hz, h0, ite_true]
            rw [← d0 h0 (f i) (Z1 i hz)]; exact hmap _ (Z4 _ (Z1 i hz))
          · simp only [tog, hz, h0, ite_true, ite_false]
            have h1 : σ x = f x := (hc x (Z4 x hxZ)).resolve_left h0
            obtain ⟨j', hj', hfj'⟩ := Z5 i hz
            rw [← hfj', ← d1 h1 j' hj']; exact hmap _ (Z4 _ hj')
        · simp only [tog, hz, ite_false]; exact hmap i hi
      · by_cases h0 : σ x = x
        · -- tog σ = f on Z
          by_cases hzi : inZ i <;> by_cases hzj : inZ j <;>
            simp only [tog, hzi, hzj, h0, ite_true, ite_false] at hij
          · exact Z6 i j hzi hzj hij
          · exfalso; apply hzj
            have := hinj (f i) (Z4 _ (Z1 i hzi)) j hj (by rw [d0 h0 _ (Z1 i hzi)]; exact hij)
            rw [← this]; exact Z1 i hzi
          · exfalso; apply hzi
            have := hinj (f j) (Z4 _ (Z1 j hzj)) i hi (by rw [d0 h0 _ (Z1 j hzj)]; exact hij.symm)
            rw [← this]; exact Z1 j hzj
          · exact hinj i hi j hj hij
        · have h1 : σ x = f x := (hc x (Z4 x hxZ)).resolve_left h0
          by_cases hzi : inZ i <;> by_cases hzj : inZ j <;>
            simp only [tog, hzi, hzj, h0, ite_true, ite_false] at hij
          · exact hij
          · exfalso; apply hzj
            obtain ⟨i', hi', hfi'⟩ := Z5 i hzi
            have := hinj i' (Z4 _ hi') j hj (by rw [d1 h1 i' hi', hfi']; exact hij)
            rw [← this]; exact hi'
          · exfalso; apply hzi
            obtain ⟨j', hj', hfj'⟩ := Z5 j hzj
            have := hinj j' (Z4 _ hj') i hi (by rw [d1 h1 j' hj', hfj']; exact hij.symm)
            rw [← this]; exact hj'
          · exact hinj i hi j hj hij
      · by_cases hz : inZ i
        · by_cases h0 : σ x = x
          · simp [tog, hz, h0]
          · simp [tog, hz, h0]
        · simp only [tog, hz, ite_false]; exact hc i hi
    · intro σ hσ
      obtain ⟨hb, hc⟩ := mem_compat.1 hσ
      obtain ⟨d0, d1⟩ := dich σ hσ
      funext i
      by_cases hz : inZ i
      · by_cases h0 : σ x = x
        · have : ¬ (f x = x) := hxf
          simp only [tog, hz, hxZ, h0, ite_true, this, ite_false]
          exact (d0 h0 i hz).symm
        · have h1 : σ x = f x := (hc x (Z4 x hxZ)).resolve_left h0
          simp only [tog, hz, hxZ, h0, ite_true, ite_false]
          exact (d1 h1 i hz).symm
      · simp [tog, hz]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact hsum

end Cycle

/-! ### Step 3: forests -/

section Acyclic

variable {U F W : Finset ι} {f : ι → ι}

open Classical in
/-- `σ_W`: `f` on the points of `U ∖ F` reached from `W`, the identity elsewhere. -/
noncomputable def sigmaW (U F W : Finset ι) (f : ι → ι) : ι → ι := fun i =>
  if i ∈ U \ F ∧ ∃ w ∈ W, ∃ k, f^[k] w = i then f i else i

/-- (E1) For a forest, a compatible bijection is `σ_W`. -/
theorem eq_sigmaW (hf : f ∈ mapsOn U (U \ F)) (hac : IsAcyc f) {σ : ι → ι}
    (hσ : σ ∈ compat (U \ F) (U \ W) f) : σ = sigmaW U F W f := by
  classical
  obtain ⟨hb, hc⟩ := mem_compat.1 hσ
  obtain ⟨hid, hmap, hinj, hcard⟩ := mem_bijFun.1 hb
  set R := U \ F
  -- `cl ∩ R ⊆ E`
  have hcl : ∀ w ∈ W, ∀ k, f^[k] w ∈ R → σ (f^[k] w) = f (f^[k] w) := by
    intro w hw k
    induction k with
    | zero =>
      intro hR
      rcases hc w hR with h | h
      · exact absurd hw (Finset.mem_sdiff.1 (h ▸ hmap w hR)).2
      · exact h
    | succ k ih =>
      intro hR
      have hRk : f^[k] w ∈ R := by
        by_contra hk
        rw [Function.iterate_succ_apply', (mem_mapsOn.1 hf).1 _ hk] at hR
        exact hk hR
      have h1 := ih hRk
      rw [Function.iterate_succ_apply'] at hR ⊢
      rcases hc _ hR with h | h
      · exact absurd (hinj _ hRk _ hR (h1.trans h.symm)) (ne_of_mem hf hRk).symm
      · exact h
  -- `E ⊆ cl`
  have hE : ∀ i ∈ R, σ i = f i → ∃ w ∈ W, ∃ k, f^[k] w = i := by
    intro i hi hs
    by_contra hncl
    have chain : ∀ n, ∃ j, j ∈ R ∧ σ j = f j ∧ (¬∃ w ∈ W, ∃ k, f^[k] w = j) ∧ f^[n] j = i := by
      intro n
      induction n with
      | zero => exact ⟨i, hi, hs, hncl, rfl⟩
      | succ n ih =>
        obtain ⟨j, hjR, hjs, hjn, hjf⟩ := ih
        have hjW : j ∉ W := fun h => hjn ⟨j, h, 0, rfl⟩
        have hjC : j ∈ U \ W := Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hjR).1, hjW⟩
        obtain ⟨j', hj'R, hj'⟩ := bijFun_surj hb j hjC
        rcases hc j' hj'R with h | h
        · exfalso
          rw [h] at hj'
          rw [hj'] at h
          exact ne_of_mem hf hjR (hjs.symm.trans h)
        · refine ⟨j', hj'R, h, fun ⟨w, hw, k, hk⟩ => hjn ⟨w, hw, k + 1, ?_⟩, ?_⟩
          · rw [Function.iterate_succ_apply', hk, ← h, hj']
          · rw [Function.iterate_succ_apply, ← h, hj', hjf]
    obtain ⟨j, -, -, -, hjf⟩ := chain (Fintype.card ι)
    have : f i = i := by rw [← hjf]; exact hac j
    exact ne_of_mem hf hi this
  funext i
  unfold sigmaW
  by_cases hi : i ∈ R
  · by_cases hs : σ i = f i
    · rw [if_pos ⟨hi, hE i hi hs⟩, hs]
    · have hs' : σ i = i := (hc i hi).resolve_right hs
      rw [hs', if_neg]
      rintro ⟨-, w, hw, k, rfl⟩
      exact hs (hcl w hw k hi)
  · rw [hid i hi, if_neg fun h => hi h.1]

/-- Merging paths: if two different points of `W` have the same root, then either some point of
`U ∖ F` reached from `W` maps into `W`, or two different such points have the same image. -/
theorem merge (hf : f ∈ mapsOn U (U \ F)) {w w' : ι} (hww : w ≠ w')
    (hroot : root f w = root f w')
    (hA : ∀ i ∈ U \ F, (∃ v ∈ W, ∃ k, f^[k] v = i) → f i ∉ W)
    (hB : ∀ i ∈ U \ F, ∀ j ∈ U \ F, (∃ v ∈ W, ∃ k, f^[k] v = i) → (∃ v ∈ W, ∃ k, f^[k] v = j) →
      f i = f j → i = j) (hw : w ∈ W) (hw' : w' ∈ W) : False := by
  classical
  have hex : ∃ s, ∃ a b, a + b = s ∧ f^[a] w = f^[b] w' :=
    ⟨_, _, _, rfl, hroot⟩
  let s₀ := Nat.find hex
  obtain ⟨a, b, hab, heq⟩ := Nat.find_spec hex
  have hmin : ∀ a' b', f^[a'] w = f^[b'] w' → s₀ ≤ a' + b' := fun a' b' h =>
    Nat.find_min' hex ⟨a', b', rfl, h⟩
  have hab' : a + b = s₀ := hab
  rcases Nat.eq_zero_or_pos a with ha | ha <;> rcases Nat.eq_zero_or_pos b with hb | hb
  · subst ha; subst hb; exact hww heq
  · subst ha
    set u := f^[b - 1] w'
    have hu : f u = w := by
      rw [show w = f^[b] w' from heq]; show f (f^[b - 1] w') = f^[b] w'
      rw [← Function.iterate_succ_apply' f, Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    by_cases huR : u ∈ U \ F
    · exact hA u huR ⟨w', hw', b - 1, rfl⟩ (hu ▸ hw)
    · have : f u = u := (mem_mapsOn.1 hf).1 u huR
      have := hmin 0 (b - 1) (by rw [← hu, this]; rfl)
      omega
  · subst hb
    set u := f^[a - 1] w
    have hu : f u = w' := by
      rw [show w' = f^[a] w from heq.symm]; show f (f^[a - 1] w) = f^[a] w
      rw [← Function.iterate_succ_apply' f, Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
    by_cases huR : u ∈ U \ F
    · exact hA u huR ⟨w, hw, a - 1, rfl⟩ (hu ▸ hw')
    · have : f u = u := (mem_mapsOn.1 hf).1 u huR
      have := hmin (a - 1) 0 (by rw [← hu, this]; rfl)
      omega
  · set u := f^[a - 1] w
    set u' := f^[b - 1] w'
    have hu : f u = f^[a] w := by
      show f (f^[a - 1] w) = f^[a] w
      rw [← Function.iterate_succ_apply' f, Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
    have hu' : f u' = f^[b] w' := by
      show f (f^[b - 1] w') = f^[b] w'
      rw [← Function.iterate_succ_apply' f, Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    by_cases huR : u ∈ U \ F
    · by_cases hu'R : u' ∈ U \ F
      · have := hB u huR u' hu'R ⟨w, hw, a - 1, rfl⟩ ⟨w', hw', b - 1, rfl⟩ (by rw [hu, hu', heq])
        have := hmin (a - 1) (b - 1) this
        omega
      · have hfix : f u' = u' := (mem_mapsOn.1 hf).1 u' hu'R
        have := hmin a (b - 1) (by rw [heq, ← hu', hfix])
        omega
    · have hfix : f u = u := (mem_mapsOn.1 hf).1 u huR
      have := hmin (a - 1) b (by rw [← heq, ← hu, hfix])
      omega

/-- (E2) For a forest, `σ_W ∈ compat(f)` iff every tree contains exactly one element of `W`. -/
theorem sigmaW_mem_iff (hFU : F ⊆ U) (hWU : W ⊆ U) (hcard : F.card = W.card)
    (hf : f ∈ mapsOn U (U \ F)) (hac : IsAcyc f) :
    sigmaW U F W f ∈ compat (U \ F) (U \ W) f ↔ IsTransv f F W := by
  classical
  set R := U \ F
  set cl : ι → Prop := fun i => ∃ w ∈ W, ∃ k, f^[k] w = i
  have hcl_f : ∀ i, cl i → cl (f i) := fun i ⟨w, hw, k, hk⟩ =>
    ⟨w, hw, k + 1, by rw [Function.iterate_succ_apply', hk]⟩
  have hsig : ∀ i, sigmaW U F W f i = if i ∈ R ∧ cl i then f i else i := fun i => rfl
  have hcardRC : R.card = (U \ W).card := by
    rw [Finset.card_sdiff_of_subset hFU, Finset.card_sdiff_of_subset hWU, hcard]
  -- σ_W ∈ compat ↔ (A) ∧ (B)
  have key : sigmaW U F W f ∈ compat R (U \ W) f ↔
      (∀ i ∈ R, cl i → f i ∉ W) ∧ (∀ i ∈ R, ∀ j ∈ R, cl i → cl j → f i = f j → i = j) := by
    constructor
    · intro h
      obtain ⟨hb, -⟩ := mem_compat.1 h
      obtain ⟨-, hmap, hinj, -⟩ := mem_bijFun.1 hb
      refine ⟨fun i hi hci => ?_, fun i hi j hj hci hcj hij => ?_⟩
      · have := hmap i hi
        rw [hsig, if_pos ⟨hi, hci⟩] at this
        exact (Finset.mem_sdiff.1 this).2
      · apply hinj i hi j hj
        rw [hsig, hsig, if_pos ⟨hi, hci⟩, if_pos ⟨hj, hcj⟩, hij]
    · rintro ⟨hA, hB⟩
      refine mem_compat.2 ⟨mem_bijFun.2 ⟨fun i hi => ?_, fun i hi => ?_,
        fun i hi j hj hij => ?_, hcardRC⟩, fun i hi => ?_⟩
      · rw [hsig, if_neg fun h => hi h.1]
      · rw [hsig]
        by_cases hci : cl i
        · rw [if_pos ⟨hi, hci⟩]
          exact Finset.mem_sdiff.2 ⟨((mem_mapsOn.1 hf).2 i hi).1, hA i hi hci⟩
        · rw [if_neg fun h => hci h.2]
          exact Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hi).1, fun hw => hci ⟨i, hw, 0, rfl⟩⟩
      · rw [hsig, hsig] at hij
        by_cases hci : cl i <;> by_cases hcj : cl j
        · rw [if_pos ⟨hi, hci⟩, if_pos ⟨hj, hcj⟩] at hij; exact hB i hi j hj hci hcj hij
        · rw [if_pos ⟨hi, hci⟩, if_neg fun h => hcj h.2] at hij
          exact absurd (hij ▸ hcl_f i hci) hcj
        · rw [if_neg fun h => hci h.2, if_pos ⟨hj, hcj⟩] at hij
          exact absurd (hij ▸ hcl_f j hcj) hci
        · rw [if_neg fun h => hci h.2, if_neg fun h => hcj h.2] at hij; exact hij
      · rw [hsig]
        by_cases hci : cl i
        · rw [if_pos ⟨hi, hci⟩]; exact Or.inr rfl
        · rw [if_neg fun h => hci h.2]; exact Or.inl rfl
  rw [key]
  constructor
  · rintro ⟨hA, hB⟩
    -- `root` is injective on `W` and maps `W` into `F`
    have hinj : ∀ w ∈ W, ∀ w' ∈ W, root f w = root f w' → w = w' := by
      intro w hw w' hw' h
      by_contra hne
      exact merge hf hne h hA hB hw hw'
    have hmapsF : ∀ w ∈ W, root f w ∈ F := fun w hw => root_mem_F hf hac (hWU hw)
    have himg : W.image (root f) = F := by
      apply Finset.eq_of_subset_of_card_le
      · intro ρ hρ
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hρ
        exact hmapsF w hw
      · rw [Finset.card_image_of_injOn (fun w hw w' hw' h => hinj w hw w' hw' h), hcard]
    intro ρ hρ
    rw [← himg] at hρ
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hρ
    rw [Finset.card_eq_one]
    refine ⟨w, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hw, rfl⟩, ?_⟩⟩
    intro w' hw'
    obtain ⟨hw'W, hr⟩ := Finset.mem_filter.1 hw'
    exact hinj w' hw'W w hw hr
  · intro htr
    -- uniqueness in each tree
    have huniq : ∀ w ∈ W, ∀ w' ∈ W, root f w = root f w' → w = w' := by
      intro w hw w' hw' h
      have hρ := root_mem_F hf hac (hWU hw)
      have := htr _ hρ
      rw [Finset.card_eq_one] at this
      obtain ⟨v, hv⟩ := this
      have h1 : w ∈ W.filter (fun x => root f x = root f w) := Finset.mem_filter.2 ⟨hw, rfl⟩
      have h2 : w' ∈ W.filter (fun x => root f x = root f w) := Finset.mem_filter.2 ⟨hw', h.symm⟩
      rw [hv, Finset.mem_singleton] at h1 h2
      rw [h1, h2]
    refine ⟨fun i hi ⟨w, hw, k, hk⟩ hfi => ?_, fun i hi j hj ⟨w, hw, a, ha⟩ ⟨w', hw', b, hb⟩ hij => ?_⟩
    · have hr : root f (f i) = root f w := by rw [root_apply hac, ← hk, root_iterate hac]
      have := huniq _ hfi w hw hr
      rw [← hk, ← Function.iterate_succ_apply' f] at this
      have hfix := fixed_of_periodic hac (Nat.succ_pos k) this
      apply ne_of_mem hf hi
      rw [← hk, ← Function.iterate_succ_apply' f, Function.iterate_succ_apply, hfix]
    · have hr : root f w = root f w' := by
        rw [← root_iterate hac w a, ha, ← root_apply hac, hij, root_apply hac, ← hb,
          root_iterate hac]
      have hww := huniq w hw w' hw' hr
      subst hww
      subst ha; subst hb
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exfalso
        have hy : f^[b - a] (f^[a + 1] w) = f^[a + 1] w := by
          rw [← Function.iterate_add_apply]
          have : b - a + (a + 1) = b + 1 := by omega
          rw [this, Function.iterate_succ_apply', Function.iterate_succ_apply', hij]
        have hfix := fixed_of_periodic hac (Nat.sub_pos_of_lt hlt) hy
        apply ne_of_mem hf hj
        have : f^[b] w = f^[a + 1] w := by
          have : b = (b - a - 1) + (a + 1) := by omega
          rw [this, Function.iterate_add_apply, iterate_fixed' hfix]
        rw [this, hfix]
      · rw [heq]
      · exfalso
        have hy : f^[a - b] (f^[b + 1] w) = f^[b + 1] w := by
          rw [← Function.iterate_add_apply]
          have : a - b + (b + 1) = a + 1 := by omega
          rw [this, Function.iterate_succ_apply', Function.iterate_succ_apply', hij]
        have hfix := fixed_of_periodic hac (Nat.sub_pos_of_lt hgt) hy
        apply ne_of_mem hf hi
        have : f^[a] w = f^[b + 1] w := by
          have : a = (a - b - 1) + (b + 1) := by omega
          rw [this, Function.iterate_add_apply, iterate_fixed' hfix]
        rw [this, hfix]

/-- For a forest, `#compat(f) = [every tree contains exactly one element of W]`. -/
theorem card_compat_acyc (hFU : F ⊆ U) (hWU : W ⊆ U) (hcard : F.card = W.card)
    (hf : f ∈ mapsOn U (U \ F)) (hac : IsAcyc f) :
    (compat (U \ F) (U \ W) f).card = if IsTransv f F W then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨sigmaW U F W f, Finset.eq_singleton_iff_unique_mem.2
      ⟨(sigmaW_mem_iff hFU hWU hcard hf hac).2 h, fun σ hσ => eq_sigmaW hf hac hσ⟩⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro σ hσ
    have := eq_sigmaW hf hac hσ
    subst this
    exact h ((sigmaW_mem_iff hFU hWU hcard hf hac).1 hσ)

end Acyclic

/-- **Lemma 2.1 (forest lemma)**, the `𝔽₂` case of the all-minors matrix-tree theorem: for
`F, W ⊆ U` with `|F| = |W|`, `det L_U[U∖F, U∖W]` is the sum of `wt(f)` over the forests `f` on `U`
rooted at `F` in which every tree contains exactly one element of `W`. -/
theorem pmin_lapl_eq_forests (a : ι → ι → ZMod 2) {U F W : Finset ι} (hFU : F ⊆ U) (hWU : W ⊆ U)
    (hcard : F.card = W.card) :
    pmin (lapl a U) (U \ F) (U \ W) =
      ∑ f ∈ forests U F, if IsTransv f F W then wt a (U \ F) f else 0 := by
  rw [pmin_lapl_eq_sum_maps a Finset.sdiff_subset, forests, Finset.sum_filter,
    ← Finset.sum_filter_add_sum_filter_not (mapsOn U (U \ F)) IsAcyc]
  have hcyc : ∑ f ∈ (mapsOn U (U \ F)).filter (fun f => ¬IsAcyc f),
      wt a (U \ F) f * ((compat (U \ F) (U \ W) f).card : ZMod 2) = 0 :=
    Finset.sum_eq_zero fun f hf => by
      obtain ⟨hf, hac⟩ := Finset.mem_filter.1 hf
      rw [card_compat_even hf hac, mul_zero]
  rw [hcyc, add_zero, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f hf => ?_
  split_ifs with hac htr htr
  · rw [card_compat_acyc hFU hWU hcard hf hac, if_pos htr, Nat.cast_one, mul_one]
  · rw [card_compat_acyc hFU hWU hcard hf hac, if_neg htr, Nat.cast_zero, mul_zero]
  · rfl

end ZInQ.RouteK.Rank5b.Sec3
