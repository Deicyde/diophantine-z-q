import ZInQKernel.RouteK.Rank5b.Sec3.Glue

/-!
# Counting set partitions compatible with a forest

* `card_fpfi`: the number of fixed-point-free involutions of a finite set `X` (= the number of
  partitions of `X` into pairs) is odd iff `|X|` is even (conjugation by a transposition; the fixed
  points are the involutions pairing the two swapped points);
* `card_A_eq`: for a forest `f` of `ι` with root set `R` and two roots `ρ₇ ≠ ρ₃`, the set partitions of
  `ι` that map every block into itself under `f`, in which `ρ₇` and `ρ₃` are alone in their blocks
  among the roots and every other block contains exactly two roots, correspond to the
  fixed-point-free involutions of `R ∖ {ρ₇, ρ₃}`.
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fixed-point-free involutions of `X` (the identity off `X`). -/
def fpfi (X : Finset ι) : Finset (ι → ι) :=
  univ.filter fun s => (∀ i, i ∉ X → s i = i) ∧ ∀ i ∈ X, s i ∈ X ∧ s i ≠ i ∧ s (s i) = i

theorem mem_fpfi {X : Finset ι} {s : ι → ι} :
    s ∈ fpfi X ↔ (∀ i, i ∉ X → s i = i) ∧ ∀ i ∈ X, s i ∈ X ∧ s i ≠ i ∧ s (s i) = i := by
  simp [fpfi]

theorem fpfi_invol {X : Finset ι} {s : ι → ι} (hs : s ∈ fpfi X) (i : ι) : s (s i) = i := by
  obtain ⟨hid, hX⟩ := mem_fpfi.1 hs
  by_cases hi : i ∈ X
  · exact (hX i hi).2.2
  · rw [hid i hi, hid i hi]

theorem card_fpfi_pair {X : Finset ι} {x y : ι} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    (((fpfi X).filter fun s => s x = y).card) = (fpfi ((X.erase x).erase y)).card := by
  classical
  have hyx : y ∈ X.erase x := Finset.mem_erase.2 ⟨Ne.symm hxy, hy⟩
  refine Finset.card_bij' (fun s _ => Function.update (Function.update s x x) y y)
    (fun s _ => Function.update (Function.update s x y) y x) ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hs, hsx⟩ := Finset.mem_filter.1 hs
    obtain ⟨hid, hX⟩ := mem_fpfi.1 hs
    have hsy : s y = x := by rw [← hsx]; exact fpfi_invol hs x
    refine mem_fpfi.2 ⟨fun i hi => ?_, fun i hi => ?_⟩
    · by_cases hiy : i = y
      · subst hiy; simp
      · rw [Function.update_of_ne hiy]
        by_cases hix : i = x
        · subst hix; simp
        · rw [Function.update_of_ne hix]
          exact hid i fun h => hi (Finset.mem_erase.2 ⟨hiy, Finset.mem_erase.2 ⟨hix, h⟩⟩)
    · obtain ⟨hiy, hi'⟩ := Finset.mem_erase.1 hi
      obtain ⟨hix, hiX⟩ := Finset.mem_erase.1 hi'
      obtain ⟨h1, h2, h3⟩ := hX i hiX
      have hsix : s i ≠ x := fun h => hiy (by rw [← h3, h, hsx])
      have hsiy : s i ≠ y := fun h => hix (by rw [← h3, h, hsy])
      simp only [Function.update_of_ne hiy, Function.update_of_ne hix, Function.update_of_ne hsix,
        Function.update_of_ne hsiy]
      exact ⟨Finset.mem_erase.2 ⟨hsiy, Finset.mem_erase.2 ⟨hsix, h1⟩⟩, h2, h3⟩
  · intro s hs
    obtain ⟨hid, hX⟩ := mem_fpfi.1 hs
    have hsx : s x = x := hid x (by simp)
    have hsy : s y = y := hid y (by simp)
    refine Finset.mem_filter.2 ⟨mem_fpfi.2 ⟨fun i hi => ?_, fun i hi => ?_⟩, by
      rw [Function.update_of_ne hxy, Function.update_self]⟩
    · have hix : i ≠ x := fun h => hi (h ▸ hx)
      have hiy : i ≠ y := fun h => hi (h ▸ hy)
      rw [Function.update_of_ne hiy, Function.update_of_ne hix]
      exact hid i fun h => hi (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    · by_cases hiy : i = y
      · subst hiy
        simp [Function.update_of_ne hxy, hxy, hx]
      · by_cases hix : i = x
        · subst hix
          simp [Function.update_of_ne hxy, hxy, hy, Ne.symm hxy]
        · have hi' : i ∈ (X.erase x).erase y := Finset.mem_erase.2 ⟨hiy, Finset.mem_erase.2 ⟨hix, hi⟩⟩
          obtain ⟨h1, h2, h3⟩ := hX i hi'
          have hsix : s i ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h1)
          have hsiy : s i ≠ y := Finset.ne_of_mem_erase h1
          simp only [Function.update_of_ne hiy, Function.update_of_ne hix,
            Function.update_of_ne hsix, Function.update_of_ne hsiy]
          exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1), h2, h3⟩
  · intro s hs
    obtain ⟨hs, hsx⟩ := Finset.mem_filter.1 hs
    have hsy : s y = x := by rw [← hsx]; exact fpfi_invol hs x
    funext i
    by_cases hiy : i = y
    · subst hiy; simp [hsy]
    · rw [Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst hix; simp [hsx, Ne.symm hxy]
      · simp [Function.update_of_ne hix, hix, hiy]
  · intro s hs
    obtain ⟨hid, -⟩ := mem_fpfi.1 hs
    have hsx : s x = x := hid x (by simp)
    have hsy : s y = y := hid y (by simp)
    funext i
    by_cases hiy : i = y
    · subst hiy; simp [hsy]
    · rw [Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst hix; simp [hsx, Ne.symm hxy]
      · simp [Function.update_of_ne hix, hix, hiy]

/-- **Pairings are odd in number iff the set has even size.** -/
theorem card_fpfi (X : Finset ι) :
    ((fpfi X).card : ZMod 2) = if Even X.card then 1 else 0 := by
  classical
  induction h : X.card using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [Finset.card_eq_zero] at h
      subst h
      have : fpfi (∅ : Finset ι) = {id} := by
        ext s
        simp only [mem_fpfi, Finset.notMem_empty, not_false_eq_true, forall_const,
          IsEmpty.forall_iff, implies_true, and_true, Finset.mem_singleton]
        exact ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩
      rw [this]; simp
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h
      have : fpfi ({x} : Finset ι) = ∅ := by
        ext s
        simp only [mem_fpfi, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        intro _ h
        obtain ⟨h1, h2, -⟩ := h x rfl
        exact h2 h1
      rw [this]; simp
  · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (show 1 < X.card by omega)
    -- conjugation by the transposition `(x y)`
    let τ := Equiv.swap x y
    let c : (ι → ι) → (ι → ι) := fun s i => τ (s (τ i))
    have hτX : ∀ i, τ i ∈ X ↔ i ∈ X := fun i => by
      rcases eq_or_ne i x with rfl | hix
      · simp [τ, hx, hy]
      rcases eq_or_ne i y with rfl | hiy
      · simp [τ, hx, hy]
      rw [show τ i = i from Equiv.swap_apply_of_ne_of_ne hix hiy]
    have hcmem : ∀ s ∈ fpfi X, c s ∈ fpfi X := fun s hs => by
      obtain ⟨hid, hX⟩ := mem_fpfi.1 hs
      refine mem_fpfi.2 ⟨fun i hi => ?_, fun i hi => ?_⟩
      · simp only [c]
        rw [hid _ fun h => hi ((hτX i).1 h), Equiv.swap_apply_self]
      · have hτi : τ i ∈ X := (hτX i).2 hi
        obtain ⟨h1, h2, h3⟩ := hX _ hτi
        refine ⟨(hτX _).2 h1, fun h => h2 ?_, ?_⟩
        · simp only [c] at h
          exact τ.injective (by rw [h, Equiv.swap_apply_self])
        · show τ (s (τ (τ (s (τ i))))) = i
          rw [show τ (τ (s (τ i))) = s (τ i) from Equiv.swap_apply_self _ _ _, h3]
          exact Equiv.swap_apply_self _ _ _
    have hcc : ∀ s, c (c s) = s := fun s => by
      funext i; simp [c, τ]
    have hfix : ∀ s ∈ fpfi X, c s = s ↔ s x = y := by
      intro s hs
      have hinv := fpfi_invol hs
      constructor
      · intro h
        have := congrFun h x
        simp only [c, τ, Equiv.swap_apply_left] at this
        by_contra hne
        have hsx : s x ≠ x := ((mem_fpfi.1 hs).2 x hx).2.1
        have h1 : s y = Equiv.swap x y (s x) := by
          rw [← this, Equiv.swap_apply_self]
        rw [Equiv.swap_apply_of_ne_of_ne hsx hne] at h1
        exact hxy (by rw [← hinv x, ← h1, hinv y])
      · intro h
        have hsy : s y = x := by rw [← h]; exact hinv x
        funext i
        simp only [c]
        rcases eq_or_ne i x with rfl | hix
        · simp [τ, hsy, h]
        rcases eq_or_ne i y with rfl | hiy
        · simp [τ, h, hsy]
        rw [show τ i = i from Equiv.swap_apply_of_ne_of_ne hix hiy]
        have h1 : s i ≠ x := fun h' => hiy (by rw [← hinv i, h', h])
        have h2 : s i ≠ y := fun h' => hix (by rw [← hinv i, h', hsy])
        exact Equiv.swap_apply_of_ne_of_ne h1 h2
    -- the non-fixed points pair up
    have hsplit : ((fpfi X).card : ZMod 2) = (((fpfi X).filter fun s => s x = y).card : ZMod 2) := by
      rw [← Finset.card_filter_add_card_filter_not (fun s => s x = y), Nat.cast_add]
      have : (((fpfi X).filter fun s => ¬ s x = y).card : ZMod 2) = 0 := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_involution (fun s _ => c s) (fun _ _ => by
          simp only [Nat.cast_one]; exact CharTwo.add_self_eq_zero 1) ?_ ?_ ?_
        · intro s hs _ h
          obtain ⟨hs, hne⟩ := Finset.mem_filter.1 hs
          exact hne ((hfix s hs).1 h)
        · intro s hs
          obtain ⟨hs, hne⟩ := Finset.mem_filter.1 hs
          refine Finset.mem_filter.2 ⟨hcmem s hs, fun h => hne ?_⟩
          have := (hfix (c s) (hcmem s hs)).2 h
          rw [hcc] at this
          rw [← (hfix s hs).1 this.symm]
        · intro s _; exact hcc s
      rw [this, add_zero]
    rw [hsplit, card_fpfi_pair hx hy hxy]
    have hcard : ((X.erase x).erase y).card = n - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxy, hy⟩),
        Finset.card_erase_of_mem hx, h]
      omega
    rw [ih (n - 2) (by omega) _ hcard]
    have : Even (n - 2) ↔ Even n := by
      constructor
      · intro he; have := he.add (even_two); rwa [Nat.sub_add_cancel hn] at this
      · intro he; exact (Nat.even_sub hn).2 (by simp [he, even_two])
    simp only [this]

/-! ### Set partitions compatible with a forest -/

section Compat

variable {f : ι → ι}

/-- `P` is compatible with `f`: `f` maps every block into itself. -/
def Resp (f : ι → ι) (P : Finpartition (univ : Finset ι)) : Prop := ∀ i, f i ∈ P.part i

instance (f : ι → ι) (P : Finpartition (univ : Finset ι)) : Decidable (Resp f P) := by
  unfold Resp; infer_instance

theorem part_iterate {P : Finpartition (univ : Finset ι)} (hP : Resp f P) (i : ι) (k : ℕ) :
    P.part (f^[k] i) = P.part i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', part_eq_part_of_mem P (hP _), ih]

theorem part_root {P : Finpartition (univ : Finset ι)} (hP : Resp f P) (i : ι) :
    P.part (root f i) = P.part i := part_iterate hP i _

theorem mem_part_iff_root {P : Finpartition (univ : Finset ι)} (hP : Resp f P) {i j : ι} :
    j ∈ P.part i ↔ root f j ∈ P.part i := by
  rw [P.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _),
    P.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _), part_root hP]

theorem root_mem_rootsOf (hf : f ∈ allF (univ : Finset ι)) (i : ι) :
    root f i ∈ rootsOf univ f :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_allF.1 hf).2.2 i⟩

theorem root_eq_self {ρ : ι} (hρ : ρ ∈ rootsOf univ f) : root f ρ = ρ :=
  root_of_fixed (Finset.mem_filter.1 hρ).2

/-- The set partitions compatible with `f` in which `ρ₇` and `ρ₃` are the only roots of their
blocks and every other block contains exactly two roots. -/
def setA (f : ι → ι) (ρ7 ρ3 : ι) : Finset (Finpartition (univ : Finset ι)) :=
  univ.filter fun P => Resp f P ∧ P.part ρ7 ∩ rootsOf univ f = {ρ7} ∧
    P.part ρ3 ∩ rootsOf univ f = {ρ3} ∧
    ∀ ρ ∈ rootsOf univ f, ρ ≠ ρ7 → ρ ≠ ρ3 → (P.part ρ ∩ rootsOf univ f).card = 2

/-- The part function of the partition attached to a pairing `s` of the roots. -/
def bS (f s : ι → ι) (i : ι) : Finset ι :=
  univ.filter fun j => root f j = root f i ∨ root f j = s (root f i)

theorem card_setA (hf : f ∈ allF (univ : Finset ι)) {ρ7 ρ3 : ι} (h7 : ρ7 ∈ rootsOf univ f)
    (h3 : ρ3 ∈ rootsOf univ f) (h73 : ρ7 ≠ ρ3) :
    (setA f ρ7 ρ3).card = (fpfi (((rootsOf univ f).erase ρ7).erase ρ3)).card := by
  classical
  set R := rootsOf univ f with hR
  set X := (R.erase ρ7).erase ρ3 with hX
  have hmemX : ∀ ρ, ρ ∈ X ↔ ρ ∈ R ∧ ρ ≠ ρ7 ∧ ρ ≠ ρ3 := fun ρ => by
    simp only [hX, Finset.mem_erase]; tauto
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
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => ?_, ?_, ?_, fun ρ hρ hρ7 hρ3 => ?_⟩
    · rw [hpart]; simp [bS, root_apply (mem_allF.1 hf).2.2]
    · rw [hpart, hsing ρ7 h7 (by simp [hmemX])]
    · rw [hpart, hsing ρ3 h3 (by simp [hmemX])]
    · have hρX : ρ ∈ X := (hmemX ρ).2 ⟨hρ, hρ7, hρ3⟩
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
    obtain ⟨-, hresp, hP7, hP3, hP2⟩ := Finset.mem_filter.1 hP
    -- the partner of a root
    have hex : ∀ ρ ∈ X, ∃ σ, (P.part ρ ∩ R).erase ρ = {σ} := fun ρ hρX => by
      obtain ⟨hρ, hρ7, hρ3⟩ := (hmemX ρ).1 hρX
      have h2 := hP2 ρ hρ hρ7 hρ3
      apply Finset.card_eq_one.1
      rw [Finset.card_erase_of_mem (Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩), h2]
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
      obtain ⟨hρ, hρ7, hρ3⟩ := (hmemX ρ).1 h
      refine (hmemX _).2 ⟨hsR, fun h7' => ?_, fun h3' => ?_⟩
      · have : ρ ∈ P.part ρ7 ∩ R := by
          rw [← h7', part_eq_part_of_mem P hsP]; exact Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩
        rw [hP7, Finset.mem_singleton] at this; exact hρ7 this
      · have : ρ ∈ P.part ρ3 ∩ R := by
          rw [← h3', part_eq_part_of_mem P hsP]; exact Finset.mem_inter.2 ⟨mem_part_univ P ρ, hρ⟩
        rw [hP3, Finset.mem_singleton] at this; exact hρ3 this
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
    -- both parts are the preimages of the same roots
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
      have hρ73 : ρ = ρ7 ∨ ρ = ρ3 := by
        by_contra hne; push_neg at hne; exact hρX ((hmemX ρ).2 ⟨hρ, hne.1, hne.2⟩)
      rw [hsρ]
      rcases hρ73 with h | h
      · rw [h, hP7]; simp
      · rw [h, hP3]; simp

end Compat

end ZInQ.RouteK.Rank5b.Sec3
