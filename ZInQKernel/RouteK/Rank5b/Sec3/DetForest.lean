import ZInQKernel.RouteK.Rank5b.Sec3.DetAlg

/-!
# Forest expansion of `det M₁` and `det M_5b` (tyz-5b Propositions 3.3 and 3.4, forest form)

Generic setting: bits `a`, `y`, `z` on a finite type `ι`, `L = lapl a univ`.

* `Pmat a c d = [[D_d, Lᵀ], [L, D_c]]`; `det_Pmat`: `det P(c, d) = Σ_F c^F Σ_{f forest rooted at F}
  wt(f) Π_{ρ∈F} d(T_ρ)` (principal-minor expansion `pmin_add_diagonal`, the block structure
  `pmin_fromBlocks_anti`, `pmin_transpose`, the forest lemma and the transversal sum `sum_transv`);
  this replaces Lemmas 3.1 and 3.2 of tyz-5b.
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Principal-minor expansion and the block structure, for permanent minors -/

section Blocks

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `pmin (Q + diag e) univ univ = Σ_S e^S pmin Q Sᶜ Sᶜ`. -/
theorem pmin_add_diagonal (Q : Matrix n n (ZMod 2)) (e : n → ZMod 2) :
    pmin (Q + diagonal e) univ univ =
      ∑ S ∈ (univ : Finset n).powerset, (∏ x ∈ S, e x) * pmin Q (univ \ S) (univ \ S) := by
  classical
  unfold pmin
  have hexp : ∀ σ : n → n, ∏ x ∈ univ, (Q + diagonal e) x (σ x) =
      ∑ S ∈ (univ : Finset n).powerset,
        if ∀ x ∈ S, σ x = x then (∏ x ∈ S, e x) * ∏ x ∈ univ \ S, Q x (σ x) else 0 := by
    intro σ
    have : ∀ x, (Q + diagonal e) x (σ x) = diagonal e x (σ x) + Q x (σ x) := fun x => by
      rw [Matrix.add_apply, add_comm]
    simp_rw [this]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs with h
    · congr 1
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [h x hx, diagonal_apply_eq]
    · push_neg at h
      obtain ⟨x, hx, hne⟩ := h
      rw [Finset.prod_eq_zero hx (by rw [diagonal_apply_ne _ (Ne.symm hne)]), zero_mul]
  rw [Finset.sum_congr rfl (fun σ _ => hexp σ), Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Finset.sum_filter, Finset.mul_sum]
  have hset : (bijFun (univ : Finset n) univ).filter (fun σ => ∀ x ∈ S, σ x = x) =
      bijFun (univ \ S) (univ \ S) := by
    ext σ
    simp only [Finset.mem_filter, mem_bijFun, Finset.mem_univ, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, forall_const, true_and, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hinj, -⟩, hfix⟩
      refine ⟨fun i hi => hfix i (by tauto), fun i hi hσi => hi ?_, fun i _ j _ h => hinj i j h,
        trivial⟩
      have := hinj (σ i) i (by rw [hfix _ hσi])
      rw [← this]; exact hσi
    · rintro ⟨hid, hmap, hinj, -⟩
      refine ⟨⟨fun i j h => ?_, trivial⟩, fun x hx => hid x (by tauto)⟩
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
      · rw [hid i (by tauto), hid j (by tauto)] at h; exact h
      · rw [hid i (by tauto)] at h; exact absurd (h ▸ hi) (hmap j hj)
      · rw [hid j (by tauto)] at h; exact absurd (h.symm ▸ hj) (hmap i hi)
      · exact hinj i hi j hj h
  rw [hset]

/-- A normalized bijection `R → C` has a normalized inverse `C → R`. -/
noncomputable def invOn (R : Finset ι) (σ : ι → ι) : ι → ι := fun c =>
  if h : ∃ a ∈ R, σ a = c then Classical.choose h else c

theorem invOn_spec {R C : Finset ι} {σ : ι → ι} (hσ : σ ∈ bijFun R C) {c : ι} (hc : c ∈ C) :
    invOn R σ c ∈ R ∧ σ (invOn R σ c) = c := by
  have h : ∃ a ∈ R, σ a = c := bijFun_surj hσ c hc
  unfold invOn
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem invOn_apply {R C : Finset ι} {σ : ι → ι} (hσ : σ ∈ bijFun R C) {a : ι} (ha : a ∈ R) :
    invOn R σ (σ a) = a := by
  have hm := (mem_bijFun.1 hσ).2.1 a ha
  obtain ⟨h1, h2⟩ := invOn_spec hσ hm
  exact (mem_bijFun.1 hσ).2.2.1 _ h1 _ ha h2

theorem invOn_not_mem {R C : Finset ι} {σ : ι → ι} (hσ : σ ∈ bijFun R C) {c : ι} (hc : c ∉ C) :
    invOn R σ c = c := by
  unfold invOn
  rw [dif_neg]
  rintro ⟨a, ha, rfl⟩
  exact hc ((mem_bijFun.1 hσ).2.1 a ha)

theorem invOn_mem {R C : Finset ι} {σ : ι → ι} (hσ : σ ∈ bijFun R C) :
    invOn R σ ∈ bijFun C R := by
  obtain ⟨_, _, _, hcard⟩ := mem_bijFun.1 hσ
  refine mem_bijFun.2 ⟨fun c hc => invOn_not_mem hσ hc, fun c hc => (invOn_spec hσ hc).1,
    fun c hc c' hc' h => ?_, hcard.symm⟩
  rw [← (invOn_spec hσ hc).2, ← (invOn_spec hσ hc').2, h]

theorem invOn_invOn {R C : Finset ι} {σ : ι → ι} (hσ : σ ∈ bijFun R C) :
    invOn C (invOn R σ) = σ := by
  have hinv := invOn_mem hσ
  funext x
  by_cases hx : x ∈ R
  · have h1 := invOn_apply hσ hx
    have h2 : σ x ∈ C := (mem_bijFun.1 hσ).2.1 x hx
    rw [← h1, invOn_apply hinv h2, h1]
  · rw [(mem_bijFun.1 hσ).1 x hx, invOn_not_mem hinv hx]

/-- `det Mᵀ[A, C] = det M[C, A]`. -/
theorem pmin_transpose (M : Matrix ι ι (ZMod 2)) (A C : Finset ι) :
    pmin Mᵀ A C = pmin M C A := by
  unfold pmin
  refine Finset.sum_bij' (fun σ _ => invOn A σ) (fun τ _ => invOn C τ)
    (fun σ hσ => invOn_mem hσ) (fun τ hτ => invOn_mem hτ)
    (fun σ hσ => invOn_invOn hσ) (fun τ hτ => invOn_invOn hτ) ?_
  intro σ hσ
  refine Finset.prod_bij' (fun a _ => σ a) (fun c _ => invOn A σ c)
    (fun a ha => (mem_bijFun.1 hσ).2.1 a ha) (fun c hc => (invOn_spec hσ hc).1)
    (fun a ha => invOn_apply hσ ha) (fun c hc => (invOn_spec hσ hc).2) ?_
  intro a ha
  rw [transpose_apply, invOn_apply hσ ha]

/-- The bijection of `A ⊕ C` made of `ν : A → C` and `τ : C → A`. -/
def glue (A C : Finset ι) (ν τ : ι → ι) : ι ⊕ ι → ι ⊕ ι :=
  Sum.elim (fun a => if a ∈ A then Sum.inr (ν a) else Sum.inl a)
    (fun c => if c ∈ C then Sum.inl (τ c) else Sum.inr c)

/-- The permanent minor of `[[0, M], [N, 0]]` on `A ⊕ C` is `det M[A, C] · det N[C, A]`. -/
theorem pmin_fromBlocks_anti (M N : Matrix ι ι (ZMod 2)) (A C : Finset ι) :
    pmin (fromBlocks 0 M N 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) (A.disjSum C) (A.disjSum C) =
      pmin M A C * pmin N C A := by
  classical
  unfold pmin
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => glue A C p.1 p.2) ?_ ?_ ?_ ?_
  · rintro ⟨ν, τ⟩ hp -
    obtain ⟨hν, hτ⟩ := Finset.mem_product.1 hp
    obtain ⟨hνid, hνmap, hνinj, hcard⟩ := mem_bijFun.1 hν
    obtain ⟨hτid, hτmap, hτinj, -⟩ := mem_bijFun.1 hτ
    refine mem_bijFun.2 ⟨fun x hx => ?_, fun x hx => ?_, fun x hx x' hx' h => ?_, rfl⟩
    · rcases x with a | c
      · have : a ∉ A := fun h => hx (Finset.inl_mem_disjSum.2 h)
        simp [glue, this]
      · have : c ∉ C := fun h => hx (Finset.inr_mem_disjSum.2 h)
        simp [glue, this]
    · rcases x with a | c
      · have ha : a ∈ A := Finset.inl_mem_disjSum.1 hx
        simp [glue, ha, hνmap a ha]
      · have hc : c ∈ C := Finset.inr_mem_disjSum.1 hx
        simp [glue, hc, hτmap c hc]
    · rcases x with a | c <;> rcases x' with a' | c'
      · have ha := Finset.inl_mem_disjSum.1 hx
        have ha' := Finset.inl_mem_disjSum.1 hx'
        simp only [glue, Sum.elim_inl, ha, ha', if_true, Sum.inr.injEq] at h
        rw [hνinj a ha a' ha' h]
      · have ha := Finset.inl_mem_disjSum.1 hx
        have hc' := Finset.inr_mem_disjSum.1 hx'
        simp [glue, ha, hc'] at h
      · have hc := Finset.inr_mem_disjSum.1 hx
        have ha' := Finset.inl_mem_disjSum.1 hx'
        simp [glue, hc, ha'] at h
      · have hc := Finset.inr_mem_disjSum.1 hx
        have hc' := Finset.inr_mem_disjSum.1 hx'
        simp only [glue, Sum.elim_inr, hc, hc', if_true, Sum.inl.injEq] at h
        rw [hτinj c hc c' hc' h]
  · rintro ⟨ν, τ⟩ hp - ⟨ν', τ'⟩ hp' - h
    obtain ⟨hν, hτ⟩ := Finset.mem_product.1 hp
    obtain ⟨hν', hτ'⟩ := Finset.mem_product.1 hp'
    simp only at hν hτ hν' hτ' h
    simp only [Prod.mk.injEq]
    constructor
    · funext a
      by_cases ha : a ∈ A
      · have := congrFun h (Sum.inl a)
        simpa [glue, ha] using this
      · rw [(mem_bijFun.1 hν).1 a ha, (mem_bijFun.1 hν').1 a ha]
    · funext c
      by_cases hc : c ∈ C
      · have := congrFun h (Sum.inr c)
        simpa [glue, hc] using this
      · rw [(mem_bijFun.1 hτ).1 c hc, (mem_bijFun.1 hτ').1 c hc]
  · intro σ hσ hne
    obtain ⟨hid, hmap, hinj, -⟩ := mem_bijFun.1 hσ
    rw [Finset.prod_disjSum] at hne
    have hA : ∀ a ∈ A, ∃ k ∈ C, σ (Sum.inl a) = Sum.inr k := by
      intro a ha
      have h1 : (fromBlocks 0 M N 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) (Sum.inl a) (σ (Sum.inl a)) ≠ 0 :=
        Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hne) a ha
      have h2 := hmap (Sum.inl a) (Finset.inl_mem_disjSum.2 ha)
      rcases h : σ (Sum.inl a) with j | k
      · rw [h] at h1; simp at h1
      · rw [h] at h2; exact ⟨k, Finset.inr_mem_disjSum.1 h2, rfl⟩
    have hC : ∀ c ∈ C, ∃ j ∈ A, σ (Sum.inr c) = Sum.inl j := by
      intro c hc
      have h1 : (fromBlocks 0 M N 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) (Sum.inr c) (σ (Sum.inr c)) ≠ 0 :=
        Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne) c hc
      have h2 := hmap (Sum.inr c) (Finset.inr_mem_disjSum.2 hc)
      rcases h : σ (Sum.inr c) with j | k
      · rw [h] at h2; exact ⟨j, Finset.inl_mem_disjSum.1 h2, rfl⟩
      · rw [h] at h1; simp at h1
    let ν : ι → ι := fun a => if a ∈ A then Sum.elim (fun _ => a) id (σ (Sum.inl a)) else a
    let τ : ι → ι := fun c => if c ∈ C then Sum.elim id (fun _ => c) (σ (Sum.inr c)) else c
    have hνa : ∀ a ∈ A, σ (Sum.inl a) = Sum.inr (ν a) := fun a ha => by
      obtain ⟨k, -, hk⟩ := hA a ha
      simp [ν, ha, hk]
    have hτc : ∀ c ∈ C, σ (Sum.inr c) = Sum.inl (τ c) := fun c hc => by
      obtain ⟨j, -, hj⟩ := hC c hc
      simp [τ, hc, hj]
    have hνmap : ∀ a ∈ A, ν a ∈ C := fun a ha => by
      have := hmap (Sum.inl a) (Finset.inl_mem_disjSum.2 ha)
      rw [hνa a ha] at this; exact Finset.inr_mem_disjSum.1 this
    have hτmap : ∀ c ∈ C, τ c ∈ A := fun c hc => by
      have := hmap (Sum.inr c) (Finset.inr_mem_disjSum.2 hc)
      rw [hτc c hc] at this; exact Finset.inl_mem_disjSum.1 this
    have hνinj : ∀ a ∈ A, ∀ a' ∈ A, ν a = ν a' → a = a' := fun a ha a' ha' h => by
      have := hinj _ (Finset.inl_mem_disjSum.2 ha) _ (Finset.inl_mem_disjSum.2 ha')
        (by rw [hνa a ha, hνa a' ha', h])
      exact Sum.inl_injective this
    have hτinj : ∀ c ∈ C, ∀ c' ∈ C, τ c = τ c' → c = c' := fun c hc c' hc' h => by
      have := hinj _ (Finset.inr_mem_disjSum.2 hc) _ (Finset.inr_mem_disjSum.2 hc')
        (by rw [hτc c hc, hτc c' hc', h])
      exact Sum.inr_injective this
    have hcard : A.card = C.card := le_antisymm
      (Finset.card_le_card_of_injOn ν hνmap fun a ha a' ha' h => hνinj a ha a' ha' h)
      (Finset.card_le_card_of_injOn τ hτmap fun c hc c' hc' h => hτinj c hc c' hc' h)
    refine ⟨(ν, τ), Finset.mem_product.2 ⟨mem_bijFun.2 ⟨fun a ha => by simp [ν, ha], hνmap,
      hνinj, hcard⟩, mem_bijFun.2 ⟨fun c hc => by simp [τ, hc], hτmap, hτinj, hcard.symm⟩⟩,
      ?_, ?_⟩
    · dsimp only
      intro h0
      rcases mul_eq_zero.1 h0 with h0 | h0
      · obtain ⟨a, ha, h⟩ := Finset.prod_eq_zero_iff.1 h0
        apply Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hne) a ha
        rw [hνa a ha]; simpa using h
      · obtain ⟨c, hc, h⟩ := Finset.prod_eq_zero_iff.1 h0
        apply Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne) c hc
        rw [hτc c hc]; simpa using h
    · funext x
      rcases x with a | c
      · by_cases ha : a ∈ A
        · simp only [glue, Sum.elim_inl, ha, if_true]; exact (hνa a ha).symm
        · simp only [glue, Sum.elim_inl, ha, if_false]
          exact (hid _ fun h => ha (Finset.inl_mem_disjSum.1 h)).symm
      · by_cases hc : c ∈ C
        · simp only [glue, Sum.elim_inr, hc, if_true]; exact (hτc c hc).symm
        · simp only [glue, Sum.elim_inr, hc, if_false]
          exact (hid _ fun h => hc (Finset.inr_mem_disjSum.1 h)).symm
  · rintro ⟨ν, τ⟩ hp -
    rw [Finset.prod_disjSum]
    congr 1
    · refine Finset.prod_congr rfl fun a ha => ?_
      simp [glue, ha]
    · refine Finset.prod_congr rfl fun c hc => ?_
      simp [glue, hc]

end Blocks

/-! ### Transversals -/

theorem card_eq_of_isTransv {U F W : Finset ι} {f : ι → ι} (hf : f ∈ forests U F) (hWU : W ⊆ U)
    (htr : IsTransv f F W) : F.card = W.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := root f) (t := F)
    (fun w hw => root_mem_of_forests hf (hWU hw))]
  rw [Finset.sum_congr rfl fun ρ hρ => htr ρ hρ]
  simp

/-- **Transversal sum**: `Σ_W d^W` over the sets with exactly one element in every tree is
`Π_{ρ∈F} d(T_ρ)`. -/
theorem sum_transv {U F : Finset ι} {f : ι → ι} (hf : f ∈ forests U F) (d : ι → ZMod 2) :
    ∑ W ∈ U.powerset, (if IsTransv f F W then ∏ w ∈ W, d w else 0) =
      ∏ ρ ∈ F, ∑ v ∈ U.filter (fun v => root f v = ρ), d v := by
  classical
  rw [Finset.prod_sum, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun p _ => F.attach.image (fun x => p x.1 x.2)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_pi] at hp
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 fun w hw => ?_, fun ρ hρ => ?_⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hw
      exact (Finset.mem_filter.1 (hp x.1 x.2)).1
    · rw [Finset.card_eq_one]
      refine ⟨p ρ hρ, ?_⟩
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_attach, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨x, rfl⟩, hx⟩
        have := (Finset.mem_filter.1 (hp x.1 x.2)).2
        rw [this] at hx
        obtain ⟨x, hx'⟩ := x
        subst hx
        rfl
      · rintro rfl
        exact ⟨⟨⟨ρ, hρ⟩, rfl⟩, (Finset.mem_filter.1 (hp ρ hρ)).2⟩
  · intro p hp q hq h
    rw [Finset.mem_pi] at hp hq
    funext ρ hρ
    have hmem : p ρ hρ ∈ F.attach.image (fun x => q x.1 x.2) := by
      rw [← h]; exact Finset.mem_image.2 ⟨⟨ρ, hρ⟩, Finset.mem_attach _ _, rfl⟩
    obtain ⟨⟨ρ', hρ'⟩, -, heq⟩ := Finset.mem_image.1 hmem
    have h1 := (Finset.mem_filter.1 (hp ρ hρ)).2
    have h2 := (Finset.mem_filter.1 (hq ρ' hρ')).2
    simp only at heq
    rw [← heq, h2] at h1
    subst h1
    exact heq.symm
  · intro W hW
    obtain ⟨hWU, htr⟩ := Finset.mem_filter.1 hW
    rw [Finset.mem_powerset] at hWU
    have hex : ∀ ρ ∈ F, ∃ a, W.filter (fun w => root f w = ρ) = {a} := fun ρ hρ =>
      Finset.card_eq_one.1 (htr ρ hρ)
    let p : ∀ ρ ∈ F, ι := fun ρ hρ => Classical.choose (hex ρ hρ)
    have hp : ∀ ρ hρ, W.filter (fun w => root f w = ρ) = {p ρ hρ} := fun ρ hρ =>
      Classical.choose_spec (hex ρ hρ)
    have hpmem : ∀ ρ hρ, p ρ hρ ∈ W ∧ root f (p ρ hρ) = ρ := fun ρ hρ => by
      have : p ρ hρ ∈ W.filter (fun w => root f w = ρ) := by
        rw [hp ρ hρ]; exact Finset.mem_singleton_self _
      exact Finset.mem_filter.1 this
    refine ⟨p, Finset.mem_pi.2 fun ρ hρ => Finset.mem_filter.2 ⟨hWU (hpmem ρ hρ).1,
      (hpmem ρ hρ).2⟩, ?_⟩
    ext w
    simp only [Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨x, rfl⟩; exact (hpmem x.1 x.2).1
    · intro hw
      have hρ := root_mem_of_forests hf (hWU hw)
      refine ⟨⟨root f w, hρ⟩, ?_⟩
      have : w ∈ W.filter (fun v => root f v = root f w) := Finset.mem_filter.2 ⟨hw, rfl⟩
      rw [hp (root f w) hρ, Finset.mem_singleton] at this
      exact this.symm
  · intro p hp
    rw [Finset.mem_pi] at hp
    rw [Finset.prod_image]
    intro x _ x' _ h
    have h1 := (Finset.mem_filter.1 (hp x.1 x.2)).2
    have h2 := (Finset.mem_filter.1 (hp x'.1 x'.2)).2
    simp only at h
    rw [h, h2] at h1
    exact Subtype.ext h1.symm

/-! ### `det P(c, d)` -/

/-- `P(c, d) = [[D_d, Lᵀ], [L, D_c]]`, `L = lapl a univ`. -/
def Pmat (a : ι → ι → ZMod 2) (c d : ι → ZMod 2) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks (diagonal d) (lapl a univ)ᵀ (lapl a univ) (diagonal c)

theorem sum_powerset_sum (h : Finset (ι ⊕ ι) → ZMod 2) :
    ∑ S ∈ (univ : Finset (ι ⊕ ι)).powerset, h S =
      ∑ W ∈ (univ : Finset ι).powerset, ∑ F ∈ (univ : Finset ι).powerset, h (W.disjSum F) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun S => (S.toLeft, S.toRight)) (fun p => p.1.disjSum p.2)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun S _ => Finset.toLeft_disjSum_toRight)
    (fun p _ => by simp) (fun S _ => by simp [Finset.toLeft_disjSum_toRight])

theorem pmin_eq_zero_of_card_ne (M : Matrix ι ι (ZMod 2)) {R C : Finset ι} (h : R.card ≠ C.card) :
    pmin M R C = 0 := by
  unfold pmin
  rw [Finset.sum_eq_zero]
  intro σ hσ
  exact absurd (mem_bijFun.1 hσ).2.2.2 h

/-- **`det P(c, d)` as a forest sum**: `Σ_F c^F Σ_{f rooted at F} wt(f) Π_{ρ∈F} d(T_ρ)`. -/
theorem det_Pmat (a : ι → ι → ZMod 2) (c d : ι → ZMod 2) :
    (Pmat a c d).det = ∑ F ∈ (univ : Finset ι).powerset, (∏ ρ ∈ F, c ρ) *
      ∑ f ∈ forests univ F, wt a (univ \ F) f *
        ∏ ρ ∈ F, ∑ v ∈ univ.filter (fun v => root f v = ρ), d v := by
  classical
  have hP : Pmat a c d = fromBlocks 0 (lapl a univ)ᵀ (lapl a univ) 0 + diagonal (Sum.elim d c) := by
    rw [Pmat, ← fromBlocks_diagonal, fromBlocks_add]
    simp
  rw [det_eq_pmin_univ, hP, pmin_add_diagonal, sum_powerset_sum]
  have hcompl : ∀ W F : Finset ι, (univ : Finset (ι ⊕ ι)) \ W.disjSum F =
      (univ \ W).disjSum (univ \ F) := fun W F => by
    ext x; rcases x with i | i <;> simp
  simp_rw [hcompl, pmin_fromBlocks_anti, pmin_transpose, zmod2_mul_self, Finset.prod_disjSum,
    Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F hF => ?_
  have hterm : ∀ W ∈ (univ : Finset ι).powerset,
      (∏ x ∈ W, d x) * (∏ x ∈ F, c x) * pmin (lapl a univ) (univ \ F) (univ \ W) =
      (∏ x ∈ F, c x) * ∑ f ∈ forests univ F,
        wt a (univ \ F) f * (if IsTransv f F W then ∏ w ∈ W, d w else 0) := by
    intro W _
    by_cases hc : F.card = W.card
    · rw [pmin_lapl_eq_forests a (subset_univ F) (subset_univ W) hc]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      split_ifs <;> ring
    · rw [pmin_eq_zero_of_card_ne (lapl a univ) (by
        rw [Finset.card_sdiff_of_subset (subset_univ F), Finset.card_sdiff_of_subset (subset_univ W)]
        have := Finset.card_le_univ F
        have := Finset.card_le_univ W
        rw [Finset.card_univ]
        omega), mul_zero]
      symm
      rw [mul_eq_zero]; right
      refine Finset.sum_eq_zero fun f hf => ?_
      rw [if_neg fun htr => hc (card_eq_of_isTransv hf (subset_univ W) htr), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [← Finset.mul_sum, sum_transv hf]

end ZInQ.RouteK.Rank5b.Sec3
