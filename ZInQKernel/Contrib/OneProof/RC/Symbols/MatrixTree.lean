import ZInQKernel.Contrib.OneProof.RC.Symbols.Core

/-!
# Lane RC2: the all-minors matrix-tree theorem modulo 2 (tex 10641–10650)

The degree-zero and degree-one coefficients of the network operator are rooted-forest minors of
the grounded auxiliary Laplacian (the manuscript cites Cauchy–Binet; printed source: S. Chaiken,
"A combinatorial proof of the all minors matrix tree theorem", SIAM J. Algebraic Discrete Methods
3 (1982) 319–329). This file proves both statements (kind: PROVED) by a different classical route:
* the permutation expansion of a directed grounded Laplacian over `ZMod 2` counts acyclic parent
  functions (`det_expand`);
* acyclic parent functions are in bijection with rooted spanning forests (`forest_bij`);
* degree one uses the bordered determinant (`det_bordered`) and one extra auxiliary vertex.
-/


namespace ZInQ.Manuscript.RC.Symbols
namespace MTInternal
open Finset Matrix

/-- Extension by the identity of a function on the subtype of `A`. -/
def ext (A : Finset ℕ) (f : A → ℕ) : ℕ → ℕ := fun x => if h : x ∈ A then f ⟨x, h⟩ else x

/-- Parent functions with choice sets `C`, identity outside `A`. -/
noncomputable def PF (A : Finset ℕ) (C : ℕ → Finset ℕ) : Finset (ℕ → ℕ) := by
  classical exact (Fintype.piFinset (fun i : A => C i)).image (ext A)

/-- Acyclic: iteration from each vertex of `A` leaves `A`. -/
def Acyc (A : Finset ℕ) (p : ℕ → ℕ) : Prop := ∀ x ∈ A, ∃ n, p^[n] x ∉ A

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mem_PF {A : Finset ℕ} {C : ℕ → Finset ℕ} {p : ℕ → ℕ} :
    p ∈ PF A C ↔ (∀ x ∈ A, p x ∈ C x) ∧ (∀ x ∉ A, p x = x) := by
  classical
  unfold PF
  constructor
  · intro hp
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
    rw [Fintype.mem_piFinset] at hf
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [ext, dif_pos hx]; exact hf ⟨x, hx⟩
    · simp only [ext, dif_neg hx]
  · rintro ⟨h1, h2⟩
    refine Finset.mem_image.mpr ⟨fun i => p i, Fintype.mem_piFinset.mpr fun i => h1 i i.2, ?_⟩
    funext x
    by_cases hx : x ∈ A
    · simp only [ext, dif_pos hx]
    · simp only [ext, dif_neg hx, h2 x hx]

/-! ### Helper lemmas -/

theorem ext_val (A : Finset ℕ) (f : A → ℕ) (i : A) : ext A f i = f i := by
  simp [ext]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem ext_inj (A : Finset ℕ) : Function.Injective (ext A) := by
  intro f g h
  funext i
  have := congrFun h i
  rwa [ext_val, ext_val] at this

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem iterate_mem {p : ℕ → ℕ} {D : Finset ℕ} (h : ∀ x ∈ D, p x ∈ D) {x : ℕ} (hx : x ∈ D) :
    ∀ n, p^[n] x ∈ D
  | 0 => hx
  | n + 1 => by rw [Function.iterate_succ_apply']; exact h _ (iterate_mem h hx n)

/-- Subsets of `A` closed under `p` on which `p` is injective. -/
noncomputable def Dset (A : Finset ℕ) (p : ℕ → ℕ) : Finset (Finset ℕ) := by
  classical exact A.powerset.filter (fun D => (∀ x ∈ D, p x ∈ D) ∧ Set.InjOn p D)

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mem_Dset {A : Finset ℕ} {p : ℕ → ℕ} {D : Finset ℕ} :
    D ∈ Dset A p ↔ D ⊆ A ∧ (∀ x ∈ D, p x ∈ D) ∧ Set.InjOn p D := by
  classical
  unfold Dset
  rw [mem_filter, mem_powerset]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem Dset_acyc {A : Finset ℕ} {p : ℕ → ℕ} (h : Acyc A p) : Dset A p = {∅} := by
  ext D
  rw [mem_Dset, mem_singleton]
  constructor
  · rintro ⟨hA, hcl, -⟩
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨n, hn⟩ := h x (hA hx)
    exact hn (hA (iterate_mem hcl hx n))
  · rintro rfl
    simp

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem exists_cycle {A : Finset ℕ} {p : ℕ → ℕ} (h : ¬ Acyc A p) :
    ∃ Z : Finset ℕ, Z.Nonempty ∧ Z ⊆ A ∧ (∀ x ∈ Z, p x ∈ Z) ∧ Set.InjOn p Z ∧
      (∀ y ∈ Z, ∃ x ∈ Z, p x = y) ∧
      (∀ D : Finset ℕ, (∀ x ∈ D, p x ∈ D) → ∀ y ∈ D, y ∈ Z → Z ⊆ D) := by
  unfold Acyc at h
  push Not at h
  obtain ⟨x₀, -, hall⟩ := h
  obtain ⟨i, -, j, -, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (A.card + 1)) (t := A) (f := fun n => p^[n] x₀) (by simp)
    (fun n _ => hall n)
  obtain ⟨a, b, hab, habeq⟩ : ∃ a b, a < b ∧ p^[a] x₀ = p^[b] x₀ := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  obtain ⟨z, hz⟩ : ∃ z, z = p^[a] x₀ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = b - a := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hper : Function.IsPeriodicPt p m z := by
    show p^[m] z = z
    rw [hz, ← Function.iterate_add_apply, show m + a = b by omega, ← habeq]
  have hper' : p^[m] z = z := hper
  have hzA : ∀ k, p^[k] z ∈ A := fun k => by
    rw [hz, ← Function.iterate_add_apply]; exact hall _
  have memZ : ∀ k, p^[k] z ∈ (range m).image (fun k => p^[k] z) := fun k =>
    mem_image.mpr ⟨k % m, mem_range.mpr (Nat.mod_lt _ hm0), hper.iterate_mod_apply k⟩
  have hcl : ∀ x ∈ (range m).image (fun k => p^[k] z), p x ∈ (range m).image (fun k => p^[k] z) := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := mem_image.mp hx
    rw [← Function.iterate_succ_apply' p k z]
    exact memZ _
  have hsurj : ∀ y ∈ (range m).image (fun k => p^[k] z),
      ∃ x ∈ (range m).image (fun k => p^[k] z), p x = y := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := mem_image.mp hy
    refine ⟨p^[k + m - 1] z, memZ _, ?_⟩
    rw [← Function.iterate_succ_apply' p (k + m - 1) z, show (k + m - 1).succ = k + m by omega,
      Function.iterate_add_apply, hper']
  refine ⟨(range m).image (fun k => p^[k] z), ⟨z, memZ 0⟩, ?_, hcl, ?_, hsurj, ?_⟩
  · intro x hx
    obtain ⟨k, -, rfl⟩ := mem_image.mp hx
    exact hzA k
  · have hmaps : Set.MapsTo p ((range m).image (fun k => p^[k] z) : Set ℕ)
        ((range m).image (fun k => p^[k] z) : Set ℕ) := fun x hx => hcl x hx
    have hso : Set.SurjOn p ((range m).image (fun k => p^[k] z) : Set ℕ)
        ((range m).image (fun k => p^[k] z) : Set ℕ) := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj y hy
      exact ⟨x, hx, hxy⟩
    exact ((Set.Finite.surjOn_iff_bijOn_of_mapsTo (Finset.finite_toSet _) hmaps).mp hso).injOn
  · intro D hDcl y hyD hyZ
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hyZ
    rw [mem_range] at hk
    intro w hw
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hw
    have := iterate_mem hDcl hyD (l + m - k)
    rwa [← Function.iterate_add_apply, show l + m - k + k = l + m by omega,
      Function.iterate_add_apply, hper'] at this

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem Dset_parity (A : Finset ℕ) (p : ℕ → ℕ) [Decidable (Acyc A p)] :
    ((Dset A p).card : ZMod 2) = if Acyc A p then 1 else 0 := by
  split_ifs with h
  · rw [Dset_acyc h]; simp
  · obtain ⟨Z, hZne, hZA, hZcl, hZinj, hZsurj, hdich⟩ := exists_cycle h
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_involution (fun D _ => if Z ⊆ D then D \ Z else D ∪ Z) ?_ ?_ ?_ ?_
    · intro D _
      simp only [Nat.cast_one]
      decide
    · intro D _ _
      by_cases hsub : Z ⊆ D
      · simp only [hsub, if_true]
        obtain ⟨z, hz⟩ := hZne
        intro heq
        have h2 : z ∈ D \ Z := by rw [heq]; exact hsub hz
        exact (mem_sdiff.mp h2).2 hz
      · simp only [hsub, if_false]
        intro heq
        apply hsub
        rw [← heq]
        exact subset_union_right
    · intro D hD
      obtain ⟨hDA, hDcl, hDinj⟩ := mem_Dset.mp hD
      by_cases hsub : Z ⊆ D
      · simp only [hsub, if_true]
        refine mem_Dset.mpr ⟨sdiff_subset.trans hDA, ?_, hDinj.mono (coe_subset.mpr sdiff_subset)⟩
        intro x hx
        rw [mem_sdiff] at hx ⊢
        refine ⟨hDcl x hx.1, fun hpx => ?_⟩
        obtain ⟨y, hy, hyx⟩ := hZsurj _ hpx
        have := hDinj (mem_coe.mpr (hsub hy)) (mem_coe.mpr hx.1) hyx
        exact hx.2 (this ▸ hy)
      · simp only [hsub, if_false]
        have hdisj : ∀ y ∈ D, y ∉ Z := fun y hyD hyZ => hsub (hdich D hDcl y hyD hyZ)
        refine mem_Dset.mpr ⟨union_subset hDA hZA, ?_, ?_⟩
        · intro x hx
          rcases mem_union.mp hx with hx | hx
          · exact mem_union_left _ (hDcl x hx)
          · exact mem_union_right _ (hZcl x hx)
        · intro x hx y hy hxy
          simp only [coe_union, Set.mem_union, mem_coe] at hx hy
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · exact hDinj hx hy hxy
          · exact absurd (hxy ▸ hZcl y hy) (hdisj _ (hDcl x hx))
          · exact absurd (hxy ▸ hZcl x hx) (hdisj _ (hDcl y hy))
          · exact hZinj hx hy hxy
    · intro D hD
      obtain ⟨hDA, hDcl, hDinj⟩ := mem_Dset.mp hD
      by_cases hsub : Z ⊆ D
      · have hn : ¬ Z ⊆ D \ Z := by
          obtain ⟨z, hz⟩ := hZne
          intro h'
          exact (mem_sdiff.mp (h' hz)).2 hz
        simp only [hsub, if_true, hn, if_false]
        exact sdiff_union_of_subset hsub
      · have hdisj : ∀ y ∈ D, y ∉ Z := fun y hyD hyZ => hsub (hdich D hDcl y hyD hyZ)
        have hn : Z ⊆ D ∪ Z := subset_union_right
        simp only [hsub, if_false, hn, if_true]
        exact union_sdiff_cancel_right (Finset.disjoint_left.mpr hdisj)

/-- Permutations of `A` that move each point either nowhere or to its parent. -/
noncomputable def compat (A : Finset ℕ) (f : A → ℕ) : Finset (Equiv.Perm A) := by
  classical exact univ.filter (fun σ => ∀ i, σ i = i ∨ ((σ i : ℕ) = f i))

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mem_compat {A : Finset ℕ} {f : A → ℕ} {σ : Equiv.Perm A} :
    σ ∈ compat A f ↔ ∀ i, σ i = i ∨ ((σ i : ℕ) = f i) := by
  classical
  unfold compat
  simp

/-- The map that follows `p` on `D` and fixes everything else. -/
def mkFun (A : Finset ℕ) (p : ℕ → ℕ) (D : Finset ℕ) : A → A :=
  fun a => if h : (a : ℕ) ∈ D ∧ p a ∈ A then ⟨p a, h.2⟩ else a

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mkFun_of_mem {A : Finset ℕ} {p : ℕ → ℕ} {D : Finset ℕ} (hD : D ⊆ A)
    (hcl : ∀ x ∈ D, p x ∈ D) {a : A} (ha : (a : ℕ) ∈ D) : (mkFun A p D a : ℕ) = p a := by
  unfold mkFun
  rw [dif_pos ⟨ha, hD (hcl _ ha)⟩]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mkFun_of_not_mem {A : Finset ℕ} {p : ℕ → ℕ} {D : Finset ℕ} {a : A}
    (ha : (a : ℕ) ∉ D) : mkFun A p D a = a := by
  unfold mkFun
  rw [dif_neg (fun h => ha h.1)]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mkFun_inj {A : Finset ℕ} {p : ℕ → ℕ} {D : Finset ℕ} (hD : D ⊆ A)
    (hcl : ∀ x ∈ D, p x ∈ D) (hinj : Set.InjOn p D) : Function.Injective (mkFun A p D) := by
  intro a b hab
  have hv := congrArg Subtype.val hab
  by_cases ha : (a : ℕ) ∈ D <;> by_cases hb : (b : ℕ) ∈ D
  · rw [mkFun_of_mem hD hcl ha, mkFun_of_mem hD hcl hb] at hv
    exact Subtype.ext (hinj ha hb hv)
  · rw [mkFun_of_mem hD hcl ha, mkFun_of_not_mem hb] at hv
    exact absurd (hv ▸ hcl _ ha) hb
  · rw [mkFun_of_not_mem ha, mkFun_of_mem hD hcl hb] at hv
    exact absurd (hv.symm ▸ hcl _ hb) ha
  · rwa [mkFun_of_not_mem ha, mkFun_of_not_mem hb] at hab

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem support_mem_Dset (A : Finset ℕ) (f : A → ℕ) (σ : Equiv.Perm A) (hσ : σ ∈ compat A f) :
    σ.support.map (Function.Embedding.subtype _) ∈ Dset A (ext A f) := by
  classical
  rw [mem_compat] at hσ
  refine mem_Dset.mpr ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, -, rfl⟩ := mem_map.mp hx
    exact a.2
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    rw [Equiv.Perm.mem_support] at ha
    have h1 : ((σ a : A) : ℕ) = f a := (hσ a).resolve_left ha
    simp only [Function.Embedding.coe_subtype, ext_val, ← h1]
    exact mem_map_of_mem (Function.Embedding.subtype _) (Equiv.Perm.apply_mem_support.mpr (Equiv.Perm.mem_support.mpr ha))
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_map.mp (mem_coe.mp hx)
    obtain ⟨b, hb, rfl⟩ := mem_map.mp (mem_coe.mp hy)
    rw [Equiv.Perm.mem_support] at ha hb
    simp only [Function.Embedding.coe_subtype, ext_val] at hxy
    rw [← (hσ a).resolve_left ha, ← (hσ b).resolve_left hb] at hxy
    simp only [Function.Embedding.coe_subtype]
    exact congrArg Subtype.val (σ.injective (Subtype.ext hxy))

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem card_compat (A : Finset ℕ) (f : A → ℕ) (hf : ∀ i, f i ≠ i) :
    (compat A f).card = (Dset A (ext A f)).card := by
  classical
  refine Finset.card_bij' (fun σ _ => σ.support.map (Function.Embedding.subtype _))
    (fun D hD => Equiv.ofBijective (mkFun A (ext A f) D)
      (Finite.injective_iff_bijective.mp (mkFun_inj (mem_Dset.mp hD).1 (mem_Dset.mp hD).2.1
        (mem_Dset.mp hD).2.2))) (fun σ hσ => support_mem_Dset A f σ hσ) ?_ ?_ ?_
  · intro D hD
    obtain ⟨hDA, hDcl, -⟩ := mem_Dset.mp hD
    rw [mem_compat]
    intro a
    by_cases ha : (a : ℕ) ∈ D
    · right
      rw [Equiv.ofBijective_apply, mkFun_of_mem hDA hDcl ha, ext_val]
    · left
      rw [Equiv.ofBijective_apply, mkFun_of_not_mem ha]
  · intro σ hσ
    obtain ⟨hDA, hDcl, -⟩ := mem_Dset.mp (support_mem_Dset A f σ hσ)
    rw [mem_compat] at hσ
    refine Equiv.ext fun a => Subtype.ext ?_
    rw [Equiv.ofBijective_apply]
    by_cases ha : σ a = a
    · have hn : (a : ℕ) ∉ σ.support.map (Function.Embedding.subtype _) := by
        rw [show (a : ℕ) = Function.Embedding.subtype _ a from rfl, mem_map',
          Equiv.Perm.mem_support, not_not]
        exact ha
      rw [mkFun_of_not_mem hn, ha]
    · have hm : (a : ℕ) ∈ σ.support.map (Function.Embedding.subtype _) :=
        mem_map_of_mem (Function.Embedding.subtype _) (Equiv.Perm.mem_support.mpr ha)
      rw [mkFun_of_mem hDA hDcl hm, ext_val]
      exact ((hσ a).resolve_left ha).symm
  · intro D hD
    obtain ⟨hDA, hDcl, -⟩ := mem_Dset.mp hD
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Equiv.Perm.mem_support, Equiv.ofBijective_apply] at ha
      by_contra hx
      exact ha (mkFun_of_not_mem hx)
    · intro hx
      refine ⟨⟨x, hDA hx⟩, ?_, rfl⟩
      rw [Equiv.Perm.mem_support, Equiv.ofBijective_apply]
      intro h
      have := congrArg Subtype.val h
      rw [mkFun_of_mem (a := ⟨x, hDA hx⟩) hDA hDcl hx, ext_val] at this
      exact hf _ this

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem compat_parity (A : Finset ℕ) (f : A → ℕ) (hf : ∀ i, f i ≠ i)
    [Decidable (Acyc A (ext A f))] :
    ((compat A f).card : ZMod 2) = if Acyc A (ext A f) then 1 else 0 := by
  rw [card_compat A f hf]
  exact Dset_parity _ _

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem zmod2_units_smul (u : ℤˣ) (x : ZMod 2) : u • x = x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [Units.neg_smul, one_smul]; exact ZMod.neg_eq_self_mod_two x

open Classical in
/-- Permutation expansion of a directed grounded Laplacian over `ZMod 2`: the determinant counts
acyclic parent functions (directed matrix-tree theorem mod 2; used for tex 10641–10650).
Kind: PROVED. -/
theorem det_expand (A : Finset ℕ) (C : ℕ → Finset ℕ) (w : ℕ → ℕ → ZMod 2)
    (hC : ∀ i ∈ A, i ∉ C i) (hC' : ∀ i ∈ A, ∀ j ∈ A, j ≠ i → j ∈ C i)
    (M : Matrix A A (ZMod 2))
    (hM : ∀ i j : A, M i j = if i = j then ∑ y ∈ C i, w i y else w i j) :
    M.det = ∑ p ∈ PF A C, if Acyc A p then ∏ i ∈ A, w i (p i) else 0 := by
  have h1 : M.det = ∑ σ : Equiv.Perm A, ∏ i, M i (σ i) := by
    rw [← det_transpose, det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [zmod2_units_smul]; rfl
  let B : Equiv.Perm A → A → Finset ℕ := fun σ i => if σ i = i then C i else {((σ i : A) : ℕ)}
  have h2 : ∀ σ : Equiv.Perm A,
      ∏ i, M i (σ i) = ∑ x ∈ Fintype.piFinset (B σ), ∏ i : A, w i (x i) := by
    intro σ
    calc ∏ i, M i (σ i) = ∏ i, ∑ j ∈ B σ i, w i j := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hM]
          by_cases h : σ i = i
          · simp [B, h]
          · rw [if_neg (Ne.symm h)]
            simp [B, h]
      _ = _ := Finset.prod_univ_sum _ _
  have hsub : ∀ σ x, x ∈ Fintype.piFinset (B σ) → x ∈ Fintype.piFinset (fun i : A => C i) := by
    intro σ x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    intro i
    have := hx i
    by_cases h : σ i = i
    · simpa [B, h] using this
    · simp only [B, if_neg h, mem_singleton] at this
      rw [this]
      exact hC' i i.2 (σ i) (σ i).2 (fun e => h (Subtype.ext e))
  have hfilt : ∀ x ∈ Fintype.piFinset (fun i : A => C i),
      univ.filter (fun σ => x ∈ Fintype.piFinset (B σ)) = compat A x := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    ext σ
    rw [mem_filter, mem_compat]
    simp only [mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : σ i = i
      · exact Or.inl hi
      · right
        have := h i
        simp only [B, if_neg hi, mem_singleton] at this
        exact this.symm
    · intro h i
      by_cases hi : σ i = i
      · simp only [B, hi]
        exact hx i
      · have := (h i).resolve_left hi
        simp [B, hi, this]
  have h3 : ∑ σ : Equiv.Perm A, ∑ x ∈ Fintype.piFinset (B σ), ∏ i : A, w i (x i)
      = ∑ x ∈ Fintype.piFinset (fun i : A => C i),
          ((compat A x).card : ZMod 2) * ∏ i : A, w i (x i) := by
    rw [Finset.sum_comm' (t' := Fintype.piFinset (fun i : A => C i))
      (s' := fun x => univ.filter (fun σ => x ∈ Fintype.piFinset (B σ)))]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.sum_const, nsmul_eq_mul, hfilt x hx]
    · intro σ x
      simp only [mem_univ, true_and, mem_filter]
      exact ⟨fun h => ⟨h, hsub σ x h⟩, fun h => h.1⟩
  rw [h1, Finset.sum_congr rfl fun σ _ => h2 σ, h3]
  unfold PF
  rw [Finset.sum_image (fun f _ g _ h => ext_inj A h)]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxC : ∀ i, x i ≠ i := by
    intro i h
    rw [Fintype.mem_piFinset] at hx
    have := hx i
    rw [h] at this
    exact hC i i.2 this
  rw [compat_parity A x hxC]
  split_ifs
  · rw [one_mul, ← Finset.prod_coe_sort A]
    exact Finset.prod_congr rfl fun i _ => by rw [ext_val]
  · rw [zero_mul]


/-- Edge set of a parent function. -/
def edges (A : Finset ℕ) (p : ℕ → ℕ) : Finset (Sym2 ℕ) := A.image (fun x => s(x, p x))

/-- Rooted forests on `V` with root set `R` (complement `A`), one root per component. -/
def RF (V R A : Finset ℕ) (S : Finset (Sym2 ℕ)) : Prop :=
  IsForest V S ∧ (∀ x ∈ A, ∃ r ∈ R, conn S x r) ∧ (∀ r ∈ R, ∀ r' ∈ R, conn S r r' → r = r')

/-! ### Iteration of a parent function -/

section Iter
variable {A : Finset ℕ} {p : ℕ → ℕ}

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem iter_fix (hfix : ∀ x ∉ A, p x = x) {z : ℕ} (hz : z ∉ A) (m : ℕ) : p^[m] z = z := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hfix z hz]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem iter_stay (hfix : ∀ x ∉ A, p x = x) {x n : ℕ} (hn : p^[n] x ∉ A) (m : ℕ)
    (hm : n ≤ m) : p^[m] x = p^[n] x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, Function.iterate_add_apply, iter_fix hfix hn]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem cycle_false (hpa : Acyc A p) {y n : ℕ} (hn : 0 < n) (hy : p^[n] y = y)
    (hin : ∀ k < n, p^[k] y ∈ A) : False := by
  have hper : Function.IsPeriodicPt p n y := hy
  obtain ⟨m, hm⟩ := hpa y (by simpa using hin 0 hn)
  apply hm
  rw [← hper.iterate_mod_apply]
  exact hin _ (Nat.mod_lt _ hn)

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem two_cycle (hpa : Acyc A p) {x : ℕ} (hx : x ∈ A) (hpx : p x ∈ A) (h : p (p x) = x) :
    False :=
  cycle_false hpa (n := 2) (y := x) (by norm_num) h
    (fun k hk => by interval_cases k <;> simpa)

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem root_out (hpa : Acyc A p) (hfix : ∀ x ∉ A, p x = x) (x : ℕ) : p^[A.card] x ∉ A := by
  classical
  intro hcon
  have hex : ∃ n, p^[n] x ∉ A := by
    by_cases hx : x ∈ A
    · exact hpa x hx
    · exact ⟨0, hx⟩
  have hn : p^[Nat.find hex] x ∉ A := Nat.find_spec hex
  have hlt : ∀ k < Nat.find hex, p^[k] x ∈ A := fun k hk => by
    have := Nat.find_min hex hk; simpa using this
  have hcard : A.card < Nat.find hex := by
    by_contra hle
    push Not at hle
    exact hn (iter_stay hfix hn A.card hle ▸ hcon)
  have key : ∀ i j, i < j → j ≤ A.card → p^[i] x = p^[j] x → False := by
    intro i j hij hj he
    refine cycle_false hpa (y := p^[i] x) (n := j - i) (by omega) ?_ ?_
    · rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, ← he]
    · intro k hk
      rw [← Function.iterate_add_apply]
      exact hlt _ (by omega)
  obtain ⟨i, hi, j, hj, hij, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (A.card + 1)) (t := A) (f := fun k => p^[k] x) (by simp)
    (fun k hk => hlt k (by simp at hk; omega))
  simp only [Finset.mem_range] at hi hj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h (by omega) he
  · exact key j i h (by omega) he.symm

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem root_comp (hpa : Acyc A p) (hfix : ∀ x ∉ A, p x = x) (x : ℕ) :
    p^[A.card] (p x) = p^[A.card] x := by
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply',
    hfix _ (root_out hpa hfix x)]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem conn_step (hfix : ∀ x ∉ A, p x = x) (x : ℕ) : conn (edges A p) x (p x) := by
  by_cases hx : x ∈ A
  · exact Relation.EqvGen.rel _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · rw [hfix x hx]; exact Relation.EqvGen.refl _

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem conn_iter (hfix : ∀ x ∉ A, p x = x) (x : ℕ) (k : ℕ) :
    conn (edges A p) x (p^[k] x) := by
  induction k with
  | zero => exact Relation.EqvGen.refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Relation.EqvGen.trans _ _ _ ih (conn_step hfix _)

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem root_of_conn (hpa : Acyc A p) (hfix : ∀ x ∉ A, p x = x) {x y : ℕ}
    (h : conn (edges A p) x y) : p^[A.card] x = p^[A.card] y := by
  unfold conn at h
  induction h with
  | rel a b hab =>
    obtain ⟨z, _, he⟩ := Finset.mem_image.mp hab
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (root_comp hpa hfix z).symm
    · exact root_comp hpa hfix z
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem edges_card (hpa : Acyc A p) {V : Finset ℕ} (hp : p ∈ PF A (fun x => V.erase x)) :
    (edges A p).card = A.card := by
  obtain ⟨_, hfix⟩ := mem_PF.mp hp
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  simp only at he
  rw [Finset.mem_coe] at hx hy
  rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    subst h1
    exact two_cycle hpa hy hx h2

end Iter

/-! ### Representatives -/

theorem rep_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (hv : v ∈ V) :
    rep V S v ∈ V ∧ conn S (rep V S v) v := by
  classical
  unfold rep
  split_ifs with h
  · have := Finset.min'_mem _ h
    rw [Finset.mem_filter] at this
    exact this
  · exact absurd ⟨v, Finset.mem_filter.mpr ⟨hv, Relation.EqvGen.refl _⟩⟩ h

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem rep_le {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (hv : v ∈ V) (hw : w ∈ V)
    (h : conn S w v) : rep V S v ≤ w := by
  classical
  unfold rep
  split_ifs with hne
  · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hw, h⟩)
  · exact absurd ⟨v, Finset.mem_filter.mpr ⟨hv, Relation.EqvGen.refl _⟩⟩ hne

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem rep_eq {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u v : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (h : conn S u v) : rep V S u = rep V S v :=
  le_antisymm
    (rep_le hu (rep_mem hv).1
      (Relation.EqvGen.trans _ _ _ (rep_mem hv).2 (Relation.EqvGen.symm _ _ h)))
    (rep_le hv (rep_mem hu).1 (Relation.EqvGen.trans _ _ _ (rep_mem hu).2 h))

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem ncomp_eq {V R : Finset ℕ} {S : Finset (Sym2 ℕ)} (hRV : R ⊆ V)
    (hcov : ∀ v ∈ V, ∃ r ∈ R, conn S v r)
    (huniq : ∀ r ∈ R, ∀ r' ∈ R, conn S r r' → r = r') : ncomp V S = R.card := by
  unfold ncomp
  have himg : V.image (rep V S) = R.image (rep V S) := by
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨r, hr, hvr⟩ := hcov v hv
      exact ⟨r, hr, (rep_eq hv (hRV hr) hvr).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hRV hr, rfl⟩
  rw [himg]
  apply Finset.card_image_of_injOn
  intro r hr r' hr' he
  rw [Finset.mem_coe] at hr hr'
  apply huniq r hr r' hr'
  have h1 := (rep_mem (S := S) (hRV hr)).2
  have h2 := (rep_mem (S := S) (hRV hr')).2
  rw [he] at h1
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) h2

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mem_pairs {V : Finset ℕ} {a b : ℕ} (h : s(a, b) ∈ pairs V) :
    a ∈ V ∧ b ∈ V ∧ a ≠ b := by
  unfold pairs at h
  obtain ⟨⟨u, v⟩, hm, he⟩ := Finset.mem_image.mp h
  simp only [Finset.mem_filter, Finset.mem_product] at hm he
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hm.1.1, hm.1.2, hm.2⟩
  · exact ⟨hm.1.2, hm.1.1, fun h => hm.2 h.symm⟩

/-! ### Layers from the roots -/

/-- Vertices within distance `k` of `R` along `S`. -/
def lay (R : Finset ℕ) (S : Finset (Sym2 ℕ)) : ℕ → Set ℕ
  | 0 => {x | x ∈ R}
  | k + 1 => lay R S k ∪ {x | ∃ y ∈ lay R S k, s(x, y) ∈ S}

/-- Depth: the first layer containing a vertex. -/
noncomputable def dep (R : Finset ℕ) (S : Finset (Sym2 ℕ)) (x : ℕ) : ℕ :=
  sInf {k | x ∈ lay R S k}

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem lay_succ {R : Finset ℕ} {S : Finset (Sym2 ℕ)} {k x : ℕ} :
    x ∈ lay R S (k + 1) ↔ x ∈ lay R S k ∨ ∃ y ∈ lay R S k, s(x, y) ∈ S := Iff.rfl

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem lay_conn {R : Finset ℕ} {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : conn S a b) :
    (∃ k, a ∈ lay R S k) ↔ (∃ k, b ∈ lay R S k) := by
  unfold conn at h
  induction h with
  | rel a b hab =>
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, lay_succ.mpr (Or.inr ⟨a, hk, by rw [Sym2.eq_swap]; exact hab⟩)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, lay_succ.mpr (Or.inr ⟨b, hk, hab⟩)⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem dep_mem {R : Finset ℕ} {S : Finset (Sym2 ℕ)} {x : ℕ} (h : ∃ k, x ∈ lay R S k) :
    x ∈ lay R S (dep R S x) := Nat.sInf_mem h

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem dep_le {R : Finset ℕ} {S : Finset (Sym2 ℕ)} {x k : ℕ} (h : x ∈ lay R S k) :
    dep R S x ≤ k := Nat.sInf_le h

/-! ### The three statements -/

/-- Acyclic parent functions are exactly the rooted forests with one root per component
(used for tex 10641–10650). Kind: PROVED. -/
theorem forest_bij (V R A : Finset ℕ) (hRA : Disjoint R A) (hV : V = R ∪ A)
    (S : Finset (Sym2 ℕ)) :
    RF V R A S ↔ ∃ p ∈ PF A (fun x => V.erase x), Acyc A p ∧ edges A p = S := by
  classical
  have hRV : R ⊆ V := by rw [hV]; exact Finset.subset_union_left
  have hAV : A ⊆ V := by rw [hV]; exact Finset.subset_union_right
  have hVc : V.card = R.card + A.card := by rw [hV, Finset.card_union_of_disjoint hRA]
  constructor
  · rintro ⟨⟨hSV, hcard⟩, hcov, huniq⟩
    have hcovV : ∀ v ∈ V, ∃ r ∈ R, conn S v r := by
      intro v hv
      rw [hV, Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact ⟨v, hv, Relation.EqvGen.refl _⟩
      · exact hcov v hv
    have hSc : S.card = A.card := by
      rw [ncomp_eq hRV hcovV huniq] at hcard
      omega
    have hpar : ∀ x ∈ A, ∃ y, s(x, y) ∈ S ∧ dep R S y < dep R S x := by
      intro x hx
      have hex : ∃ k, x ∈ lay R S k := by
        obtain ⟨r, hr, hxr⟩ := hcov x hx
        exact (lay_conn hxr).mpr ⟨0, hr⟩
      have hmem := dep_mem hex
      obtain ⟨m, hm⟩ : ∃ m, dep R S x = m + 1 := by
        refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
        rw [h0] at hmem
        exact Finset.disjoint_left.mp hRA hmem hx
      rw [hm] at hmem
      rcases lay_succ.mp hmem with hmem | ⟨y, hy, hxy⟩
      · have := dep_le hmem
        omega
      · exact ⟨y, hxy, by have := dep_le hy; omega⟩
    choose! par hparS hparlt using hpar
    let p : ℕ → ℕ := fun x => if x ∈ A then par x else x
    have hpA : ∀ x ∈ A, p x = par x := fun x hx => if_pos hx
    have hpn : ∀ x ∉ A, p x = x := fun x hx => if_neg hx
    have hpPF : p ∈ PF A (fun x => V.erase x) := by
      rw [mem_PF]
      refine ⟨fun x hx => ?_, hpn⟩
      have := mem_pairs (hSV (hparS x hx))
      rw [hpA x hx]
      exact Finset.mem_erase.mpr ⟨this.2.2.symm, this.2.1⟩
    have hpacyc : Acyc A p := by
      intro x _
      by_contra hall
      push Not at hall
      have key : ∀ n, dep R S (p^[n] x) + n ≤ dep R S x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Function.iterate_succ_apply', hpA _ (hall n)]
          have := hparlt _ (hall n)
          omega
      have := key (dep R S x + 1)
      omega
    refine ⟨p, hpPF, hpacyc, ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
      rw [hpA x hx]
      exact hparS x hx
    · rw [edges_card hpacyc hpPF, hSc]
  · rintro ⟨p, hp, hpa, rfl⟩
    obtain ⟨hpV, hfix⟩ := mem_PF.mp hp
    have hrootR : ∀ r ∈ R, p^[A.card] r = r := fun r hr =>
      iter_fix hfix (Finset.disjoint_left.mp hRA hr) _
    have hmapV : ∀ x ∈ V, p x ∈ V := fun x hx => by
      by_cases hxA : x ∈ A
      · exact Finset.mem_of_mem_erase (hpV x hxA)
      · rw [hfix x hxA]; exact hx
    have hiterV : ∀ x ∈ V, ∀ k, p^[k] x ∈ V := by
      intro x hx k
      induction k with
      | zero => exact hx
      | succ k ih => rw [Function.iterate_succ_apply']; exact hmapV _ ih
    have hroot : ∀ x ∈ V, p^[A.card] x ∈ R := fun x hx => by
      have h1 := hiterV x hx A.card
      rw [hV, Finset.mem_union] at h1
      exact h1.resolve_right (root_out hpa hfix x)
    have huniq : ∀ r ∈ R, ∀ r' ∈ R, conn (edges A p) r r' → r = r' := by
      intro r hr r' hr' h
      have := root_of_conn hpa hfix h
      rwa [hrootR r hr, hrootR r' hr'] at this
    have hcovV : ∀ v ∈ V, ∃ r ∈ R, conn (edges A p) v r := fun v hv =>
      ⟨_, hroot v hv, conn_iter hfix v A.card⟩
    refine ⟨⟨?_, ?_⟩, fun x hx => hcovV x (hAV hx), huniq⟩
    · intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
      have h1 := hpV x hx
      refine Finset.mem_image.mpr ⟨(x, p x), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hAV hx, Finset.mem_of_mem_erase h1⟩, (Finset.ne_of_mem_erase h1).symm⟩
    · rw [edges_card hpa hp, ncomp_eq hRV hcovV huniq, hVc]
      omega

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem edges_inj (V A : Finset ℕ) (p q : ℕ → ℕ) (hp : p ∈ PF A (fun x => V.erase x))
    (hq : q ∈ PF A (fun x => V.erase x)) (hpa : Acyc A p) (hqa : Acyc A q)
    (h : edges A p = edges A q) : p = q := by
  obtain ⟨_, hpfix⟩ := mem_PF.mp hp
  obtain ⟨_, hqfix⟩ := mem_PF.mp hq
  by_contra hne
  have hex : ∃ x ∈ A, p x ≠ q x := by
    by_contra hall
    push Not at hall
    refine hne (funext fun x => ?_)
    by_cases hx : x ∈ A
    · exact hall x hx
    · rw [hpfix x hx, hqfix x hx]
  obtain ⟨x0, hx0, hne0⟩ := hex
  have step : ∀ x, x ∈ A ∧ p x ≠ q x → p x ∈ A ∧ p (p x) ≠ q (p x) := by
    rintro x ⟨hx, hxne⟩
    have hmem : s(x, p x) ∈ edges A q := by
      rw [← h]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hmem
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      exact absurd h2.symm hxne
    · subst h1
      exact ⟨hy, fun hpp => two_cycle hpa hx hy (hpp.trans h2)⟩
  have hall : ∀ n, p^[n] x0 ∈ A ∧ p (p^[n] x0) ≠ q (p^[n] x0) := by
    intro n
    induction n with
    | zero => exact ⟨hx0, hne0⟩
    | succ n ih => rw [Function.iterate_succ_apply']; exact step _ ih
  obtain ⟨n, hn⟩ := hpa x0 hx0
  exact hn (hall n).1

/-- `conn` along a forest of a parent function is equality of roots. -/
theorem conn_edges_iff (V R A : Finset ℕ) (hRA : Disjoint R A) (hV : V = R ∪ A) (p : ℕ → ℕ)
    (hp : p ∈ PF A (fun x => V.erase x)) (hpa : Acyc A p) (x y : ℕ) (hx : x ∈ V) (hy : y ∈ V) :
    conn (edges A p) x y ↔ p^[A.card] x = p^[A.card] y := by
  have hfix := (mem_PF.mp hp).2
  constructor
  · exact root_of_conn hpa hfix
  · intro h
    have h1 := conn_iter hfix x A.card
    have h2 := conn_iter hfix y A.card
    rw [h] at h1
    exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)


/-- Over `ZMod 2`, every permutation sign is `1`. -/
theorem sign_zmod2 {m : Type*} [Fintype m] [DecidableEq m] (σ : Equiv.Perm m) :
    ((Equiv.Perm.sign σ : ℤ) : ZMod 2) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simp
  · decide

/-- Bordered determinant over `ZMod 2` (used for tex 10641–10650). Kind: PROVED. -/
theorem det_bordered {n : Type*} [Fintype n] [DecidableEq n] (L : Matrix n n (ZMod 2))
    (u v : n → ZMod 2) (d : ZMod 2) :
    (Matrix.fromBlocks L (Matrix.replicateCol Unit v) (Matrix.replicateRow Unit u)
      (fun _ _ => d)).det = d * L.det + u ⬝ᵥ (L.adjugate *ᵥ v) := by
  change (Matrix.fromBlocks L (Matrix.replicateCol Unit v) (Matrix.replicateRow Unit u)
    (Matrix.of fun _ _ => d)).det = _
  set N := Matrix.fromBlocks L (Matrix.replicateCol Unit v) (Matrix.replicateRow Unit u)
    (Matrix.of fun _ _ => d) with hN
  rw [det_eq_sum_mul_adjugate_row N (Sum.inr ()), Fintype.sum_sum_type]
  simp only [Fintype.univ_unit, sum_singleton, adjugate_apply]
  have hstar : (N.updateRow (Sum.inr ()) (Pi.single (Sum.inr ()) 1)).det = L.det := by
    have : N.updateRow (Sum.inr ()) (Pi.single (Sum.inr ()) 1) =
        Matrix.fromBlocks L (Matrix.replicateCol Unit v) 0 1 := by
      ext (i | i) (j | j) <;> simp [hN, updateRow_apply]
    rw [this, det_fromBlocks_zero₂₁]
    simp
  have hj : ∀ j : n, (N.updateRow (Sum.inr ()) (Pi.single (Sum.inl j) 1)).det =
      cramer L v j := by
    intro j
    set σ : Equiv.Perm (n ⊕ Unit) := Equiv.swap (Sum.inl j) (Sum.inr ())
    have h1 := det_permute' σ (N.updateRow (Sum.inr ()) (Pi.single (Sum.inl j) 1))
    rw [sign_zmod2, one_mul] at h1
    rw [← h1, cramer_apply]
    have : (N.updateRow (Sum.inr ()) (Pi.single (Sum.inl j) 1)).submatrix id σ =
        Matrix.fromBlocks (L.updateCol j v) (Matrix.replicateCol Unit (fun i => L i j)) 0 1 := by
      ext (i | i) (k | k)
      · by_cases hk : k = j
        · subst hk; simp [σ, hN, updateRow_apply]
        · simp [σ, hN, updateRow_apply, hk, Equiv.swap_apply_of_ne_of_ne]
      · simp [σ, hN, updateRow_apply]
      · by_cases hk : k = j
        · subst hk; simp [σ, hN, updateRow_apply]
        · simp [σ, hN, updateRow_apply, hk, Equiv.swap_apply_of_ne_of_ne]
      · simp [σ, hN, updateRow_apply]
    rw [this, det_fromBlocks_zero₂₁]
    simp
  rw [hstar]
  simp only [hj, cramer_eq_adjugate_mulVec, dotProduct]
  simp [hN, add_comm]


/-! ## Assembly lemmas -/

open Classical in
/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem prod_zmod2 (s : Finset ℕ) (f : ℕ → ZMod 2) :
    ∏ i ∈ s, f i = if ∀ i ∈ s, f i = 1 then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one h
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    apply Finset.prod_eq_zero hi
    have : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
    exact this _ hne

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem conn_refl' (S : Finset (Sym2 ℕ)) (a : ℕ) : conn S a a := Relation.EqvGen.refl a
/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem conn_symm' {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : conn S a b) : conn S b a :=
  Relation.EqvGen.symm _ _ h
/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem conn_trans' {S : Finset (Sym2 ℕ)} {a b c : ℕ} (h1 : conn S a b) (h2 : conn S b c) :
    conn S a c := Relation.EqvGen.trans _ _ _ h1 h2

open Classical in
/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem rep_spec' (V : Finset ℕ) (S : Finset (Sym2 ℕ)) {a : ℕ} (ha : a ∈ V) :
    rep V S a ∈ V ∧ conn S (rep V S a) a ∧ ∀ u ∈ V, conn S u a → rep V S a ≤ u := by
  have hne : (V.filter (fun u => conn S u a)).Nonempty :=
    ⟨a, Finset.mem_filter.2 ⟨ha, conn_refl' S a⟩⟩
  have h1 : rep V S a = (V.filter (fun u => conn S u a)).min' hne := by
    rw [rep, dif_pos hne]
  have hm := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hm
  refine ⟨h1 ▸ hm.1, h1 ▸ hm.2, fun u hu huc => ?_⟩
  rw [h1]; exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hu, huc⟩)

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem rep_eq_of_conn' (V : Finset ℕ) (S : Finset (Sym2 ℕ)) {a b : ℕ} (ha : a ∈ V)
    (hb : b ∈ V) (h : conn S a b) : rep V S a = rep V S b := by
  obtain ⟨ma, ca, la⟩ := rep_spec' V S ha
  obtain ⟨mb, cb, lb⟩ := rep_spec' V S hb
  exact le_antisymm (la _ mb (conn_trans' cb (conn_symm' h))) (lb _ ma (conn_trans' ca h))

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem starForest_eq_empty_iff' (T : Finset ℕ) (S : Finset (Sym2 ℕ)) :
    starForest T S = ∅ ↔ ∀ r ∈ T, ∀ r' ∈ T, conn S r r' → r = r' := by
  unfold starForest
  rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  constructor
  · intro h r hr r' hr' hc
    have h1 := h hr
    have h2 := h hr'
    push Not at h1 h2
    have := rep_eq_of_conn' T S hr hr' hc
    rw [h1, h2] at this; exact this
  · intro h r hr
    push Not
    obtain ⟨hm, hc, -⟩ := rep_spec' T S hr
    exact h _ hm _ hr hc

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem starForest_eq_pair_iff' (T : Finset ℕ) (S : Finset (Sym2 ℕ)) {a c : ℕ} (ha : a ∈ T)
    (hc : c ∈ T) (hac : a ≠ c) :
    starForest T S = {s(a, c)} ↔
      conn S a c ∧ ∀ r ∈ T.erase a, ∀ r' ∈ T.erase a, conn S r r' → r = r' := by
  classical
  have key : ∀ b ∈ T, rep T S b ≠ b → s(rep T S b, b) ∈ starForest T S := by
    intro b hb hne
    unfold starForest
    exact Finset.mem_image.2 ⟨b, Finset.mem_filter.2 ⟨hb, hne⟩, rfl⟩
  constructor
  · intro h
    have hstar : ∀ b ∈ T, rep T S b ≠ b → s(rep T S b, b) = s(a, c) := by
      intro b hb hne
      have := key b hb hne
      rw [h, Finset.mem_singleton] at this; exact this
    refine ⟨?_, ?_⟩
    · have hmem : s(a, c) ∈ starForest T S := by rw [h]; exact Finset.mem_singleton_self _
      unfold starForest at hmem
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 hmem
      have hbT := (Finset.mem_filter.1 hb).1
      have hcb := (rep_spec' T S hbT).2.1
      rcases Sym2.eq_iff.1 hbe with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hcb; exact hcb
      · rw [h1, h2] at hcb; exact conn_symm' hcb
    · intro r hr r' hr' hrr
      have hrT := Finset.mem_of_mem_erase hr
      have hr'T := Finset.mem_of_mem_erase hr'
      have hra := Finset.ne_of_mem_erase hr
      have hr'a := Finset.ne_of_mem_erase hr'
      by_contra hne
      have heq := rep_eq_of_conn' T S hrT hr'T hrr
      -- one of r, r' differs from the common representative
      have aux : ∀ b ∈ T, b ≠ a → rep T S b ≠ b → rep T S b = a ∧ b = c := by
        intro b hb hba hrb
        rcases Sym2.eq_iff.1 (hstar b hb hrb) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exact absurd h2 hba
      by_cases hm : rep T S r = r
      · have hm' : rep T S r' ≠ r' := by rw [← heq, hm]; exact hne
        obtain ⟨h1, h2⟩ := aux r' hr'T hr'a hm'
        rw [← heq, hm] at h1; exact hra h1
      · obtain ⟨h1, h2⟩ := aux r hrT hra hm
        have hm' : rep T S r' ≠ r' := by rw [← heq, h1]; exact fun h => hr'a h.symm
        obtain ⟨h3, h4⟩ := aux r' hr'T hr'a hm'
        exact hne (h2.trans h4.symm)
  · rintro ⟨hac', H⟩
    ext e
    rw [Finset.mem_singleton]
    constructor
    · intro he
      unfold starForest at he
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨hbT, hne⟩ := Finset.mem_filter.1 hb
      obtain ⟨hm, hcm, -⟩ := rep_spec' T S hbT
      by_cases hba : b = a
      · subst hba
        have hma : rep T S b ≠ b := hne
        have : rep T S b = c :=
          H _ (Finset.mem_erase.2 ⟨hma, hm⟩) _ (Finset.mem_erase.2 ⟨fun h => hac h.symm, hc⟩)
            (conn_trans' hcm hac')
        rw [this]; exact Sym2.eq_swap
      · by_cases hma : rep T S b = a
        · have : b = c :=
            H _ (Finset.mem_erase.2 ⟨hba, hbT⟩) _ (Finset.mem_erase.2 ⟨fun h => hac h.symm, hc⟩)
              (conn_trans' (conn_symm' (hma ▸ hcm)) hac')
          rw [hma, this]
        · exact absurd (H _ (Finset.mem_erase.2 ⟨hma, hm⟩) _ (Finset.mem_erase.2 ⟨hba, hbT⟩) hcm)
            hne
    · rintro rfl
      obtain ⟨hm, hcm, -⟩ := rep_spec' T S hc
      have hrac := rep_eq_of_conn' T S ha hc hac'
      by_cases hma : rep T S c = a
      · have := key c hc (by rw [hma]; exact hac)
        rw [hma] at this; exact this
      · have hmc : rep T S c = c :=
          H _ (Finset.mem_erase.2 ⟨hma, hm⟩) _ (Finset.mem_erase.2 ⟨fun h => hac h.symm, hc⟩) hcm
        have := key a ha (by rw [hrac, hmc]; exact fun h => hac h.symm)
        rw [hrac, hmc] at this
        rw [Sym2.eq_swap]; exact this

variable {L : Type*} [AddCommGroup L]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mem_netEdges' {Γ : Config L} {T X : Finset ℕ} {e : Sym2 ℕ} :
    e ∈ netEdges Γ T X ↔ ∃ x ∈ X, ∃ y ∈ T ∪ X, x ≠ y ∧ Γ.z x y = 1 ∧ s(x, y) = e := by
  unfold netEdges
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨hx, hy⟩, hxy, hz⟩, rfl⟩; exact ⟨x, hx, y, hy, hxy, hz, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, hz, rfl⟩; exact ⟨x, y, ⟨⟨hx, hy⟩, hxy, hz⟩, rfl⟩

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem netEdge_aux (Γ : Config L) (T X : Finset ℕ)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x) {x y : ℕ} (hx : x ∈ X)
    (hy : y ∈ T ∪ X) (hxy : x ≠ y) : s(x, y) ∈ netEdges Γ T X ↔ Γ.z x y = 1 := by
  rw [mem_netEdges']
  constructor
  · rintro ⟨x', hx', y', hy', hne, hz, he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hz
    · rw [hsymm x' hx' y' hy' hne] at hz; exact hz
  · intro hz; exact ⟨x, hx, y, hy, hxy, hz, rfl⟩

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem netEdge_term (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X) {a y : ℕ}
    (ha : a ∈ T) : s(a, y) ∈ netEdges Γ T X ↔ y ∈ X ∧ Γ.z y a = 1 := by
  have haX : a ∉ X := Finset.disjoint_left.1 hTX ha
  rw [mem_netEdges']
  constructor
  · rintro ⟨x', hx', y', hy', hne, hz, he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hx' haX
    · exact ⟨hx', hz⟩
  · rintro ⟨hy, hz⟩
    exact ⟨y, hy, a, Finset.mem_union_left _ ha, fun h => haX (h ▸ hy), hz, Sym2.eq_swap⟩

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem edge_mem_edges {A : Finset ℕ} {p : ℕ → ℕ} {x : ℕ} (hx : x ∈ A) :
    s(x, p x) ∈ edges A p := Finset.mem_image.2 ⟨x, hx, rfl⟩

open Classical in
/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem mt0_core (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x) :
    (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = ∅)).card : ZMod 2) =
      (lap Γ T X).det := by
  have hdet := det_expand X (fun x => (T ∪ X).erase x) Γ.z
    (fun i _ => Finset.notMem_erase i _)
    (fun i _ j hj hji => Finset.mem_erase.2 ⟨hji, Finset.mem_union_right _ hj⟩)
    (lap Γ T X) (fun i j => rfl)
  rw [hdet]
  have hterm : ∀ p : ℕ → ℕ, (if Acyc X p then ∏ i ∈ X, Γ.z i (p i) else 0) =
      if (Acyc X p ∧ ∀ i ∈ X, Γ.z i (p i) = 1) then (1 : ZMod 2) else 0 := by
    intro p; rw [prod_zmod2]
    by_cases h1 : Acyc X p <;> by_cases h2 : ∀ i ∈ X, Γ.z i (p i) = 1 <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_boole]
  congr 1
  symm
  have hsub : ∀ p ∈ PF X (fun x => (T ∪ X).erase x), (∀ i ∈ X, Γ.z i (p i) = 1) →
      edges X p ⊆ netEdges Γ T X := by
    intro p hp hones
    rw [edges, Finset.image_subset_iff]
    intro x hx
    have hpx := Finset.mem_erase.1 ((mem_PF.1 hp).1 x hx)
    exact (netEdge_aux Γ T X hsymm hx hpx.2 (Ne.symm hpx.1)).2 (hones x hx)
  apply Finset.card_bij (fun p _ => edges X p)
  · intro p hp
    obtain ⟨hpPF, hacyc, hones⟩ := Finset.mem_filter.1 hp
    obtain ⟨hF, hroot, hsep⟩ :=
      (forest_bij (T ∪ X) T X hTX rfl (edges X p)).2 ⟨p, hpPF, hacyc, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hsub p hpPF hones),
      ⟨hF, hroot⟩, (starForest_eq_empty_iff' T _).2 hsep⟩
  · intro p hp q hq h
    obtain ⟨hpPF, hpa, -⟩ := Finset.mem_filter.1 hp
    obtain ⟨hqPF, hqa, -⟩ := Finset.mem_filter.1 hq
    exact edges_inj (T ∪ X) X p q hpPF hqPF hpa hqa h
  · intro S hS
    obtain ⟨hSsub, ⟨hF, hroot⟩, hstar⟩ := Finset.mem_filter.1 hS
    obtain ⟨p, hpPF, hpa, rfl⟩ := (forest_bij (T ∪ X) T X hTX rfl S).1
      ⟨hF, hroot, (starForest_eq_empty_iff' T S).1 hstar⟩
    refine ⟨p, Finset.mem_filter.2 ⟨hpPF, hpa, fun i hi => ?_⟩, rfl⟩
    have hpx := Finset.mem_erase.1 ((mem_PF.1 hpPF).1 i hi)
    exact (netEdge_aux Γ T X hsymm hi hpx.2 (Ne.symm hpx.1)).1
      (Finset.mem_powerset.1 hSsub (edge_mem_edges hi))

/-! ## Iteration lemmas -/

theorem iter_off {A : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ x ∉ A, g x = x) {x : ℕ} (hx : x ∉ A)
    (n : ℕ) : g^[n] x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hg x hx]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem iter_stable {A : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ x ∉ A, g x = x) {x : ℕ} {n : ℕ}
    (hn : g^[n] x ∉ A) {m : ℕ} (hm : n ≤ m) : g^[m] x = g^[n] x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, Function.iterate_add_apply, iter_off hg hn]

/-- A periodic orbit stays in any set containing one period. -/
theorem iter_periodic {p : ℕ → ℕ} {y t : ℕ} (ht : 0 < t) (hper : p^[t] y = y) (B : Set ℕ)
    (hB : ∀ m < t, p^[m] y ∈ B) : ∀ m, p^[m] y ∈ B := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < t
    · exact hB m hm
    · have : m = (m - t) + t := by omega
      rw [this, Function.iterate_add_apply, hper]
      exact ih _ (by omega)

/-- Pigeonhole: an acyclic parent function leaves `A` within `A.card` steps. -/
theorem iter_card_notMem {A : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ x ∉ A, g x = x) (hac : Acyc A g)
    (x : ℕ) : g^[A.card] x ∉ A := by
  classical
  by_cases hx : x ∈ A
  swap
  · rw [iter_off hg hx]; exact hx
  intro hin
  have hall : ∀ k ≤ A.card, g^[k] x ∈ A := by
    intro k hk
    by_contra hk'
    rw [← iter_stable hg hk' hk] at hk'
    exact hk' hin
  obtain ⟨k, hk, l, hl, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (A.card + 1)) (t := A) (f := fun k => g^[k] x)
    (by simp) (fun k hk => hall k (by simpa [Nat.lt_succ_iff] using hk))
  rw [Finset.mem_range] at hk hl
  -- wlog k < l
  have key : ∀ k l, k < l → l ≤ A.card → g^[k] x = g^[l] x → False := by
    intro k l hkl hl heq
    have hper : g^[l - k] (g^[k] x) = g^[k] x := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hkl.le, heq]
    have hstay := iter_periodic (by omega) hper (A : Set ℕ) (fun m hm => by
      rw [← Function.iterate_add_apply]; exact hall _ (by omega))
    obtain ⟨n, hn⟩ := hac (g^[k] x) (hall k (by omega))
    exact hn (hstay n)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key k l h (by omega) heq
  · exact key l k h (by omega) heq.symm

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem iter_update_eq {g : ℕ → ℕ} {b j x : ℕ} {n : ℕ} (h : ∀ m < n, g^[m] x ≠ b) :
    (Function.update g b j)^[n] x = g^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun m hm => h m (by omega)), Function.update_of_ne (h n (by omega))]

/-- Adding one vertex `b` pointing to `j`: acyclicity. -/
theorem acyc_update_iff {A : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ x ∉ A, g x = x) {b j : ℕ}
    (hb : b ∉ A) (hj : j ∈ A) :
    Acyc (insert b A) (Function.update g b j) ↔ Acyc A g ∧ g^[A.card] j ≠ b := by
  classical
  set p := Function.update g b j
  have hpb : p b = j := Function.update_self b j g
  constructor
  · intro hp
    have hAg : Acyc A g := by
      intro x hx
      by_contra hcon
      push Not at hcon
      have hne : ∀ m, g^[m] x ≠ b := fun m h => hb (h ▸ hcon m)
      obtain ⟨n, hn⟩ := hp x (Finset.mem_insert_of_mem hx)
      rw [iter_update_eq (fun m _ => hne m)] at hn
      exact hn (Finset.mem_insert_of_mem (hcon n))
    refine ⟨hAg, fun hjb => ?_⟩
    -- least k with g^[k] j = b
    have hex : ∃ k, g^[k] j = b := ⟨_, hjb⟩
    let k := Nat.find hex
    have hk : g^[k] j = b := Nat.find_spec hex
    have hlt : ∀ m < k, g^[m] j ≠ b := fun m hm => Nat.find_min hex hm
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hk; exact absurd (hk ▸ hj) hb
      · exact h
    have hinA : ∀ m < k, g^[m] j ∈ A := by
      intro m hm
      by_contra hmA
      have := iter_stable hg hmA (le_of_lt hm)
      rw [hk] at this
      exact hlt m hm this.symm
    have hpk : p^[k] j = b := by rw [iter_update_eq hlt, hk]
    have hper : p^[k + 1] j = j := by
      rw [Function.iterate_succ_apply', hpk]; exact hpb
    have hstay := iter_periodic (Nat.succ_pos k) hper (insert b A : Finset ℕ) (fun m hm => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
      · rw [iter_update_eq (fun m' hm' => hlt m' (by omega))]
        exact Finset.mem_insert_of_mem (hinA m h)
      · rw [h, hpk]; exact Finset.mem_insert_self b A)
    obtain ⟨n, hn⟩ := hp j (Finset.mem_insert_of_mem hj)
    exact hn (hstay n)
  · rintro ⟨hAg, hjb⟩
    have hjne : ∀ m, g^[m] j ≠ b := by
      intro m hm
      have hmA : g^[m] j ∉ A := hm ▸ hb
      rcases le_total m A.card with h | h
      · exact hjb (by rw [iter_stable hg hmA h, hm])
      · rw [iter_stable hg (iter_card_notMem hg hAg j) h] at hm; exact hjb hm
    have hpj : ∀ m, p^[m] j = g^[m] j := fun m => iter_update_eq (fun m' _ => hjne m')
    have hjout : p^[A.card] j ∉ insert b A := by
      rw [hpj, Finset.mem_insert, not_or]
      exact ⟨hjb, iter_card_notMem hg hAg j⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxA
    · refine ⟨A.card + 1, ?_⟩
      rw [Function.iterate_succ_apply, hpb]; exact hjout
    · by_cases hxb : ∃ m, g^[m] x = b
      · let m := Nat.find hxb
        have hm : g^[m] x = b := Nat.find_spec hxb
        have hlt : ∀ m' < m, g^[m'] x ≠ b := fun m' hm' => Nat.find_min hxb hm'
        refine ⟨A.card + 1 + m, ?_⟩
        rw [Function.iterate_add_apply, iter_update_eq hlt, hm, Function.iterate_succ_apply, hpb]
        exact hjout
      · push Not at hxb
        refine ⟨A.card, ?_⟩
        rw [iter_update_eq (fun m' _ => hxb m'), Finset.mem_insert, not_or]
        exact ⟨hxb _, iter_card_notMem hg hAg x⟩

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem root_update {A : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ x ∉ A, g x = x) {b j : ℕ}
    (hb : b ∉ A) (hAg : Acyc A g) (hjb : g^[A.card] j ≠ b) :
    (Function.update g b j)^[(insert b A).card] b = g^[A.card] j := by
  have hjne : ∀ m, g^[m] j ≠ b := by
    intro m hm
    have hmA : g^[m] j ∉ A := hm ▸ hb
    rcases le_total m A.card with h | h
    · exact hjb (by rw [iter_stable hg hmA h, hm])
    · rw [iter_stable hg (iter_card_notMem hg hAg j) h] at hm; exact hjb hm
  rw [Finset.card_insert_of_notMem hb, Function.iterate_succ_apply, Function.update_self,
    iter_update_eq (fun m' _ => hjne m')]

/-! ## Parent functions with one more vertex -/

theorem PF_congr {A : Finset ℕ} {C D : ℕ → Finset ℕ} (h : ∀ x ∈ A, C x = D x) :
    PF A C = PF A D := by
  ext p; rw [mem_PF, mem_PF]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun x hx => h x hx ▸ h1 x hx, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun x hx => (h x hx).symm ▸ h1 x hx, h2⟩

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem PF_insert_sum {M : Type*} [AddCommMonoid M] {A : Finset ℕ} {b : ℕ} (hb : b ∉ A)
    (C : ℕ → Finset ℕ) (F : (ℕ → ℕ) → M) :
    ∑ p ∈ PF (insert b A) C, F p = ∑ j ∈ C b, ∑ g ∈ PF A C, F (Function.update g b j) := by
  have hprod := Finset.sum_product' (s := C b) (t := PF A C)
    (f := fun j g => F (Function.update g b j))
  rw [← hprod]
  symm
  apply Finset.sum_nbij' (fun q => Function.update q.2 b q.1)
    (fun p => (p b, Function.update p b b))
  · intro q hq
    obtain ⟨hj, hg⟩ := Finset.mem_product.1 hq
    obtain ⟨hg1, hg2⟩ := mem_PF.1 hg
    rw [mem_PF]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | hxA
      · rw [Function.update_self]; exact hj
      · have hxb : x ≠ b := fun h => hb (h ▸ hxA)
        rw [Function.update_of_ne hxb]; exact hg1 x hxA
    · have hxb : x ≠ b := fun h => hx (h ▸ Finset.mem_insert_self _ _)
      rw [Function.update_of_ne hxb]; exact hg2 x (fun h => hx (Finset.mem_insert_of_mem h))
  · intro p hp
    obtain ⟨hp1, hp2⟩ := mem_PF.1 hp
    rw [Finset.mem_product, mem_PF]
    refine ⟨hp1 b (Finset.mem_insert_self _ _), fun x hx => ?_, fun x hx => ?_⟩
    · have hxb : x ≠ b := fun h => hb (h ▸ hx)
      dsimp only
      rw [Function.update_of_ne hxb]; exact hp1 x (Finset.mem_insert_of_mem hx)
    · dsimp only
      by_cases hxb : x = b
      · subst hxb; rw [Function.update_self]
      · rw [Function.update_of_ne hxb]
        exact hp2 x (fun h => (Finset.mem_insert.1 h).elim hxb hx)
  · intro q hq
    obtain ⟨hj, hg⟩ := Finset.mem_product.1 hq
    have hgb : q.2 b = b := (mem_PF.1 hg).2 b hb
    have : Function.update q.2 b b = q.2 := by
      have h' := Function.update_eq_self b q.2
      rw [hgb] at h'; exact h'
    simp only [Function.update_self, Function.update_idem, this]
  · intro p hp
    simp only [Function.update_idem, Function.update_eq_self]
  · intro q hq; rfl

/-- `insert c X` as `X ⊕ Unit`. -/
def insEquiv (X : Finset ℕ) (c : ℕ) (hc : c ∉ X) : (insert c X : Finset ℕ) ≃ (X ⊕ Unit) where
  toFun i := if h : (i : ℕ) = c then Sum.inr () else
    Sum.inl ⟨i, (Finset.mem_insert.1 i.2).resolve_left h⟩
  invFun s := match s with
    | Sum.inl x => ⟨x, Finset.mem_insert_of_mem x.2⟩
    | Sum.inr _ => ⟨c, Finset.mem_insert_self c X⟩
  left_inv i := by
    by_cases h : (i : ℕ) = c
    · simp only [dif_pos h]; exact Subtype.ext h.symm
    · simp only [dif_neg h]
  right_inv s := by
    rcases s with x | u
    · have : (x : ℕ) ≠ c := fun h => hc (h ▸ x.2)
      simp only [dif_neg this]
    · simp

/-! ## Degree one: the forest side -/

theorem rf_pair_iff (T X : Finset ℕ) (S : Finset (Sym2 ℕ)) {a c : ℕ} (ha : a ∈ T) (hc : c ∈ T)
    (hac : a ≠ c) :
    (IsRootedForest T X S ∧ starForest T S = {s(a, c)}) ↔
      (RF (T ∪ X) (T.erase a) (insert a X) S ∧ conn S a c) := by
  rw [starForest_eq_pair_iff' T S ha hc hac]
  have hcE : c ∈ T.erase a := Finset.mem_erase.2 ⟨fun h => hac h.symm, hc⟩
  constructor
  · rintro ⟨⟨hF, hroot⟩, hac', H⟩
    refine ⟨⟨hF, fun x hx => ?_, H⟩, hac'⟩
    rcases Finset.mem_insert.1 hx with hxa | hxX
    · exact ⟨c, hcE, hxa ▸ hac'⟩
    · obtain ⟨r, hr, hxr⟩ := hroot x hxX
      by_cases hra : r = a
      · exact ⟨c, hcE, conn_trans' hxr (hra ▸ hac')⟩
      · exact ⟨r, Finset.mem_erase.2 ⟨hra, hr⟩, hxr⟩
  · rintro ⟨⟨hF, hroot, H⟩, hac'⟩
    refine ⟨⟨hF, fun x hx => ?_⟩, hac', H⟩
    obtain ⟨r, hr, hxr⟩ := hroot x (Finset.mem_insert_of_mem hx)
    exact ⟨r, Finset.mem_of_mem_erase hr, hxr⟩

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem edges_update_subset_iff {X : Finset ℕ} {g : ℕ → ℕ} {a j : ℕ} (haX : a ∉ X)
    (N : Finset (Sym2 ℕ)) :
    edges (insert a X) (Function.update g a j) ⊆ N ↔
      s(a, j) ∈ N ∧ ∀ x ∈ X, s(x, g x) ∈ N := by
  rw [edges, Finset.image_subset_iff, Finset.forall_mem_insert, Function.update_self]
  apply and_congr Iff.rfl
  apply forall₂_congr
  intro x hx
  rw [Function.update_of_ne (fun h : x = a => haX (h ▸ hx))]

/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem Q_update_iff (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x) {a c : ℕ} (ha : a ∈ T)
    (hac : a ≠ c) {g : ℕ → ℕ} (hg : g ∈ PF X (fun x => (T ∪ X).erase x)) {j : ℕ} (hj : j ∈ X) :
    (Acyc (insert a X) (Function.update g a j) ∧
        edges (insert a X) (Function.update g a j) ⊆ netEdges Γ T X ∧
        (Function.update g a j)^[(insert a X).card] a = c) ↔
      (Γ.z j a = 1 ∧ (∀ i ∈ X, Γ.z i (g i) = 1) ∧ Acyc X g ∧ g^[X.card] j = c) := by
  have haX : a ∉ X := Finset.disjoint_left.1 hTX ha
  obtain ⟨hg1, hg2⟩ := mem_PF.1 hg
  have hones : (∀ x ∈ X, s(x, g x) ∈ netEdges Γ T X) ↔ ∀ i ∈ X, Γ.z i (g i) = 1 := by
    apply forall₂_congr
    intro x hx
    have hpx := Finset.mem_erase.1 (hg1 x hx)
    exact netEdge_aux Γ T X hsymm hx hpx.2 (Ne.symm hpx.1)
  rw [edges_update_subset_iff haX, netEdge_term Γ T X hTX ha, hones,
    acyc_update_iff hg2 haX hj]
  constructor
  · rintro ⟨⟨hAg, hja⟩, ⟨⟨-, hz⟩, ho⟩, hr⟩
    rw [root_update hg2 haX hAg hja] at hr
    exact ⟨hz, ho, hAg, hr⟩
  · rintro ⟨hz, ho, hAg, hr⟩
    have hja : g^[X.card] j ≠ a := by rw [hr]; exact Ne.symm hac
    exact ⟨⟨hAg, hja⟩, ⟨⟨hj, hz⟩, ho⟩, by rw [root_update hg2 haX hAg hja]; exact hr⟩

open Classical in
/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem lhs_count (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x)
    {a c : ℕ} (ha : a ∈ T) (hc : c ∈ T) (hac : a ≠ c) :
    (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = {s(a, c)})).card : ZMod 2) =
    ∑ j ∈ X, ∑ g ∈ PF X (fun x => (T ∪ X).erase x),
      if (Γ.z j a = 1 ∧ (∀ i ∈ X, Γ.z i (g i) = 1) ∧ Acyc X g ∧ g^[X.card] j = c)
      then (1 : ZMod 2) else 0 := by
  have haX : a ∉ X := Finset.disjoint_left.1 hTX ha
  have hcX : c ∉ X := Finset.disjoint_left.1 hTX hc
  have hV : T ∪ X = T.erase a ∪ insert a X := by
    ext y
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · by_cases hya : y = a
        · exact Or.inr (Or.inl hya)
        · exact Or.inl ⟨hya, h⟩
      · exact Or.inr (Or.inr h)
    · rintro (⟨_, h⟩ | h | h)
      · exact Or.inl h
      · exact Or.inl (h ▸ ha)
      · exact Or.inr h
  have hRA : Disjoint (T.erase a) (insert a X) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    rcases Finset.mem_insert.1 hy' with hya | hyX
    · exact Finset.ne_of_mem_erase hy hya
    · exact Finset.disjoint_left.1 hTX (Finset.mem_of_mem_erase hy) hyX
  have hcA : c ∉ insert a X := by
    rw [Finset.mem_insert, not_or]; exact ⟨fun h => hac h.symm, hcX⟩
  have haV : a ∈ T ∪ X := Finset.mem_union_left _ ha
  have hcV : c ∈ T ∪ X := Finset.mem_union_left _ hc
  let Q : (ℕ → ℕ) → Prop := fun p => Acyc (insert a X) p ∧
    edges (insert a X) p ⊆ netEdges Γ T X ∧ p^[(insert a X).card] a = c
  have hcard : ((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = {s(a, c)})).card =
      ((PF (insert a X) (fun x => (T ∪ X).erase x)).filter Q).card := by
    symm
    apply Finset.card_bij (fun p _ => edges (insert a X) p)
    · intro p hp
      obtain ⟨hpPF, hpa, hsub, hroot⟩ := Finset.mem_filter.1 hp
      have hRF := (forest_bij (T ∪ X) (T.erase a) (insert a X) hRA hV _).2 ⟨p, hpPF, hpa, rfl⟩
      have hconn : conn (edges (insert a X) p) a c := by
        rw [conn_edges_iff (T ∪ X) (T.erase a) (insert a X) hRA hV p hpPF hpa a c haV hcV,
          hroot, iter_off (mem_PF.1 hpPF).2 hcA]
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub,
        (rf_pair_iff T X _ ha hc hac).2 ⟨hRF, hconn⟩⟩
    · intro p hp q hq h
      obtain ⟨hpPF, hpa, -⟩ := Finset.mem_filter.1 hp
      obtain ⟨hqPF, hqa, -⟩ := Finset.mem_filter.1 hq
      exact edges_inj (T ∪ X) (insert a X) p q hpPF hqPF hpa hqa h
    · intro S hS
      obtain ⟨hSsub, hS2⟩ := Finset.mem_filter.1 hS
      obtain ⟨hRF, hconn⟩ := (rf_pair_iff T X S ha hc hac).1 hS2
      obtain ⟨p, hpPF, hpa, rfl⟩ := (forest_bij (T ∪ X) (T.erase a) (insert a X) hRA hV S).1 hRF
      refine ⟨p, Finset.mem_filter.2 ⟨hpPF, hpa, Finset.mem_powerset.1 hSsub, ?_⟩, rfl⟩
      rw [conn_edges_iff (T ∪ X) (T.erase a) (insert a X) hRA hV p hpPF hpa a c haV hcV,
        iter_off (mem_PF.1 hpPF).2 hcA] at hconn
      exact hconn
  rw [hcard, Finset.natCast_card_filter, PF_insert_sum haX]
  have hXsub : X ⊆ (T ∪ X).erase a := fun y hy =>
    Finset.mem_erase.2 ⟨fun h => haX (h ▸ hy), Finset.mem_union_right _ hy⟩
  rw [← Finset.sum_subset hXsub]
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro g hg
    exact if_congr (Q_update_iff Γ T X hTX hsymm ha hac hg hj) rfl rfl
  · intro j _ hjX
    apply Finset.sum_eq_zero
    intro g _
    rw [if_neg]
    rintro ⟨-, hsub, -⟩
    rw [edges_update_subset_iff haX, netEdge_term Γ T X hTX ha] at hsub
    exact hjX hsub.1.1

/-! ## Degree one: the determinant side -/

open Classical in
/-- Auxiliary lemma for the matrix-tree theorem mod 2 (tex 10641–10650). Kind: PROVED. -/
theorem rhs_count (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    {a c : ℕ} (hc : c ∈ T) :
    attach Γ X a ⬝ᵥ ((lap Γ T X).adjugate *ᵥ attach Γ X c) =
    ∑ j ∈ X, ∑ g ∈ PF X (fun x => (T ∪ X).erase x),
      if (Γ.z j a = 1 ∧ (∀ i ∈ X, Γ.z i (g i) = 1) ∧ Acyc X g ∧ g^[X.card] j = c)
      then (1 : ZMod 2) else 0 := by
  have hcX : c ∉ X := Finset.disjoint_left.1 hTX hc
  set d : ZMod 2 := ∑ j ∈ X, Γ.z j a with hd
  have hB := det_bordered (lap Γ T X) (attach Γ X a) (attach Γ X c) d
  let C' : ℕ → Finset ℕ := fun i => if i = c then X else (T ∪ X).erase i
  let w' : ℕ → ℕ → ZMod 2 := fun i y => if i = c then Γ.z y a else Γ.z i y
  let M' : Matrix (insert c X : Finset ℕ) (insert c X : Finset ℕ) (ZMod 2) :=
    fun i j => if i = j then ∑ y ∈ C' i, w' i y else w' i j
  have hM'eq : M' = (Matrix.fromBlocks (lap Γ T X) (Matrix.replicateCol Unit (attach Γ X c))
      (Matrix.replicateRow Unit (attach Γ X a)) (fun _ _ => d)).submatrix
        (insEquiv X c hcX) (insEquiv X c hcX) := by
    ext i j
    simp only [Matrix.submatrix_apply, insEquiv, Equiv.coe_fn_mk]
    by_cases hi : (i : ℕ) = c <;> by_cases hj : (j : ℕ) = c
    · rw [dif_pos hi, dif_pos hj]
      have hij : i = j := Subtype.ext (hi.trans hj.symm)
      show (if i = j then ∑ y ∈ C' i, w' i y else w' i j) = d
      rw [if_pos hij]
      simp only [C', w', hi, if_true, hd]
    · rw [dif_pos hi, dif_neg hj]
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      show (if i = j then ∑ y ∈ C' i, w' i y else w' i j) = Γ.z j a
      rw [if_neg hij]
      simp only [w', hi, if_true]
    · rw [dif_neg hi, dif_pos hj]
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      show (if i = j then ∑ y ∈ C' i, w' i y else w' i j) = Γ.z i c
      rw [if_neg hij]
      simp only [w', hi, if_false, hj]
    · rw [dif_neg hi, dif_neg hj]
      show (if i = j then ∑ y ∈ C' i, w' i y else w' i j) =
        (if (⟨i, _⟩ : X) = ⟨j, _⟩ then ∑ u ∈ (T ∪ X).erase i, Γ.z i u else Γ.z i j)
      simp only [C', w', hi, if_false, Subtype.ext_iff]
  have hdetM' : M'.det = (Matrix.fromBlocks (lap Γ T X) (Matrix.replicateCol Unit (attach Γ X c))
      (Matrix.replicateRow Unit (attach Γ X a)) (fun _ _ => d)).det := by
    rw [hM'eq, Matrix.det_submatrix_equiv_self]
  have hC1 : ∀ i ∈ insert c X, i ∉ C' i := by
    intro i _
    by_cases h : i = c
    · simp only [C', h, if_true]; exact hcX
    · simp only [C', h, if_false]; exact Finset.notMem_erase i _
  have hC2 : ∀ i ∈ insert c X, ∀ j ∈ insert c X, j ≠ i → j ∈ C' i := by
    intro i _ j hj hji
    by_cases h : i = c
    · simp only [C', h, if_true]
      rcases Finset.mem_insert.1 hj with hjc | hjX
      · exact absurd (hjc.trans h.symm) hji
      · exact hjX
    · simp only [C', h, if_false]
      refine Finset.mem_erase.2 ⟨hji, ?_⟩
      rcases Finset.mem_insert.1 hj with hjc | hjX
      · exact hjc ▸ Finset.mem_union_left _ hc
      · exact Finset.mem_union_right _ hjX
  have hexp' := det_expand (insert c X) C' w' hC1 hC2 M' (fun i j => rfl)
  have hexp := det_expand X (fun x => (T ∪ X).erase x) Γ.z (fun i _ => Finset.notMem_erase i _)
    (fun i _ j hj hji => Finset.mem_erase.2 ⟨hji, Finset.mem_union_right _ hj⟩) (lap Γ T X)
    (fun i j => rfl)
  rw [PF_insert_sum hcX] at hexp'
  have hCc : C' c = X := by simp [C']
  have hPF : PF X C' = PF X (fun x => (T ∪ X).erase x) :=
    PF_congr (fun x hx => by
      have hxc : x ≠ c := fun h => hcX (h ▸ hx)
      simp [C', hxc])
  rw [hCc, hPF] at hexp'
  have hterm : ∀ j ∈ X, ∀ g ∈ PF X (fun x => (T ∪ X).erase x),
      (if Acyc (insert c X) (Function.update g c j) then
        ∏ i ∈ insert c X, w' i (Function.update g c j i) else 0) =
      if (Acyc X g ∧ g^[X.card] j ≠ c) then Γ.z j a * ∏ i ∈ X, Γ.z i (g i) else 0 := by
    intro j hj g hg
    have hg2 := (mem_PF.1 hg).2
    rw [acyc_update_iff hg2 hcX hj]
    by_cases h : Acyc X g ∧ g^[X.card] j ≠ c
    · rw [if_pos h, if_pos h, Finset.prod_insert hcX]
      congr 1
      · simp [w']
      · apply Finset.prod_congr rfl
        intro i hi
        have hic : i ≠ c := fun h' => hcX (h' ▸ hi)
        simp [w', hic, Function.update_of_ne hic]
    · rw [if_neg h, if_neg h]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hRHS : attach Γ X a ⬝ᵥ ((lap Γ T X).adjugate *ᵥ attach Γ X c) =
      M'.det + d * (lap Γ T X).det := by
    rw [hdetM', hB]; linear_combination (-(d * (lap Γ T X).det)) * h2
  rw [hRHS, hexp', hexp, hd, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_congr rfl (hterm j hj), Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [prod_zmod2]
  have hz : Γ.z j a = 0 ∨ Γ.z j a = 1 := by
    generalize Γ.z j a = t; revert t; decide
  by_cases hA : Acyc X g <;> by_cases hr : g^[X.card] j = c <;>
    by_cases ho : ∀ i ∈ X, Γ.z i (g i) = 1 <;> rcases hz with hz | hz <;>
    simp [hA, hr, ho, hz]
  all_goals (split_ifs <;> decide)

end MTInternal

open Finset Matrix
variable {L : Type*} [AddCommGroup L]

open Classical in
/-- **All-minors matrix-tree theorem mod 2, degree zero** (tex 10641–10650; printed source
Chaiken 1982). The number mod 2 of rooted forests of the network whose terminal partition is
discrete equals the determinant of the grounded auxiliary Laplacian. Kind: PROVED. -/
theorem mt0 (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x) :
    (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = ∅)).card : ZMod 2) =
      (lap Γ T X).det :=
  MTInternal.mt0_core Γ T X hTX hsymm

open Classical in
/-- **All-minors matrix-tree theorem mod 2, degree one** (tex 10641–10650; printed source
Chaiken 1982). The number mod 2 of rooted forests of the network whose terminal partition is
`{a, c}` plus singletons equals `c_aᵀ adj(Q) c_c` for the grounded auxiliary Laplacian `Q` and the
attachment columns `c_a`, `c_c`. Kind: PROVED. -/
theorem mt1 (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x)
    {a c : ℕ} (ha : a ∈ T) (hc : c ∈ T) (hac : a ≠ c) :
    (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = {s(a, c)})).card : ZMod 2) =
      attach Γ X a ⬝ᵥ ((lap Γ T X).adjugate *ᵥ attach Γ X c) := by
  rw [MTInternal.lhs_count Γ T X hTX hsymm ha hc hac, MTInternal.rhs_count Γ T X hTX hc]

end ZInQ.Manuscript.RC.Symbols
