import ZInQKernel.Contrib.OneProof.RC.Symbols.Core

/-!
# Lane RC2: forest products, minimum seeds, contraction certificates, zero-total packets

Manuscript: Definition `ex:sec7-typed-graph` (tex 2015–2066, contraction), Lemma
`ex:sec7-coefficient-rules` (2102–2136), Definition `ex:sec7-seed-partition` and Lemma
`ex:sec7-seed-certificate` (2176–2207), App G zero-total packets and cycle products (10587–10633).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {A : Config L → ZMod 2}

namespace ForestAux

/-! ### Generalities on configurations -/

/-- Extensionality for configurations. -/
theorem config_ext {Γ Δ : Config L} (hV : Γ.V = Δ.V) (ht : Γ.t = Δ.t) (hz : Γ.z = Δ.z) :
    Γ = Δ := by
  cases Γ; cases Δ; simp_all

/-- Two configurations agreeing on the vertex set (types, and bits of distinct pairs) are
isomorphic through the identity. -/
theorem iso_of_agree {Γ Δ : Config L} (hV : Γ.V = Δ.V) (ht : ∀ v ∈ Γ.V, Δ.t v = Γ.t v)
    (hz : ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ≠ w → Δ.z v w = Γ.z v w) : Γ.IsIso Δ :=
  ⟨Equiv.subtypeEquivRight (fun x => by rw [hV]), fun v => ht v v.2,
    fun v w hvw => hz v v.2 w w.2 (fun h => hvw (Subtype.ext h))⟩

/-- Isomorphisms transport compatibility. -/
theorem compatible_of_iso {Γ Δ : Config L} (h : Γ.IsIso Δ) (hΓ : Γ.Compatible ε) :
    Δ.Compatible ε := by
  obtain ⟨e, ht, hz⟩ := h
  intro a ha b hb hab
  obtain ⟨v, hv⟩ := e.surjective ⟨a, ha⟩
  obtain ⟨w, hw⟩ := e.surjective ⟨b, hb⟩
  have ha' : ((e v : Δ.V) : ℕ) = a := by rw [hv]
  have hb' : ((e w : Δ.V) : ℕ) = b := by rw [hw]
  subst ha' hb'
  have hvw : v ≠ w := by rintro rfl; exact hab rfl
  have hvw' : (v : ℕ) ≠ w := fun h => hvw (Subtype.ext h)
  rw [hz v w hvw, hz w v hvw.symm, ht, ht]
  exact hΓ v v.2 w w.2 hvw'

/-- Isomorphic configurations have the same number of vertices. -/
theorem card_eq_of_iso {Γ Δ : Config L} (h : Γ.IsIso Δ) : Γ.V.card = Δ.V.card := by
  obtain ⟨e, -, -⟩ := h
  simpa using Fintype.card_congr e

/-! ### Flips -/

@[simp] theorem flipBy_V (Γ : Config L) (U : Finset (Sym2 ℕ)) : (Γ.flipBy U).V = Γ.V := rfl
@[simp] theorem flipBy_t (Γ : Config L) (U : Finset (Sym2 ℕ)) : (Γ.flipBy U).t = Γ.t := rfl
@[simp] theorem flip_V (Γ : Config L) (v w : ℕ) : (Γ.flip v w).V = Γ.V := rfl
@[simp] theorem flip_t (Γ : Config L) (v w : ℕ) : (Γ.flip v w).t = Γ.t := rfl

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem flipBy_compatible {Γ : Config L} (hΓ : Γ.Compatible ε) (U : Finset (Sym2 ℕ)) :
    (Γ.flipBy U).Compatible ε := by
  intro a ha b hb hab
  have h := hΓ a ha b hb hab
  simp only [Config.flipBy] at *
  have hs : s(b, a) = s(a, b) := Sym2.eq_swap
  rw [hs]
  by_cases hU : s(a, b) ∈ U
  · simp only [ne_eq, hab, not_false_eq_true, hU, and_self, ite_true, Ne.symm hab]
    rw [← h]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  · simp [hU, h]

theorem flipBy_empty (Γ : Config L) : Γ.flipBy ∅ = Γ := by
  refine config_ext (by rfl) (by rfl) ?_
  funext a b
  simp [Config.flipBy]

theorem flipBy_insert (Γ : Config L) {e : Sym2 ℕ} {U : Finset (Sym2 ℕ)} (he : e ∉ U) :
    Γ.flipBy (insert e U) = (Γ.flipBy {e}).flipBy U := by
  refine config_ext (by rfl) (by rfl) ?_
  funext a b
  simp only [Config.flipBy, Finset.mem_insert, Finset.mem_singleton]
  by_cases hab : a ≠ b
  · by_cases h1 : s(a, b) = e
    · have h2 : s(a, b) ∉ U := h1 ▸ he
      simp [hab, h1, h2]
      subst h1; simp [h2]
    · by_cases h2 : s(a, b) ∈ U <;> simp [hab, h1, h2]
  · simp [hab]

/-- One flip, written with indicator functions. -/
theorem flip_z {Γ : Config L} {v w : ℕ} (hvw : v ≠ w) (a b : ℕ) :
    (Γ.flip v w).z a b = Γ.z a b +
      ((if a = v ∧ b = w then 1 else 0) + (if a = w ∧ b = v then 1 else 0)) := by
  simp only [Config.flip, Config.flipBy, Finset.mem_singleton, Sym2.eq_iff]
  by_cases h1 : a = v ∧ b = w
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hvw, Ne.symm hvw]
  · by_cases h2 : a = w ∧ b = v
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hvw, Ne.symm hvw]
    · simp [h1, h2]

/-- Finite difference along one more pair. -/
theorem diff_insert (A : Config L → ZMod 2) (Γ : Config L) {e : Sym2 ℕ} {S : Finset (Sym2 ℕ)}
    (he : e ∉ S) : diff A Γ (insert e S) = diff A Γ S + diff A (Γ.flipBy {e}) S := by
  unfold diff
  rw [Finset.sum_powerset_insert he]
  congr 1
  refine Finset.sum_congr rfl fun U hU => ?_
  rw [flipBy_insert Γ (fun h => he (Finset.mem_powerset.1 hU h))]

/-! ### Contraction along a labelling of the vertices -/

/-- Contraction of each fibre of `f` (on `Γ.V`) to its label: summed types and incidences. -/
def cmap (Γ : Config L) (f : ℕ → ℕ) : Config L where
  V := Γ.V.image f
  t := fun r => ∑ u ∈ Γ.V.filter (fun u => f u = r), Γ.t u
  z := fun r r' => ∑ u ∈ Γ.V.filter (fun u => f u = r),
    ∑ u' ∈ Γ.V.filter (fun u' => f u' = r'), Γ.z u u'

theorem contractBy_eq (Γ : Config L) (S : Finset (Sym2 ℕ)) :
    Γ.contractBy S = cmap Γ (rep Γ.V S) := rfl

theorem cmap_compatible {Γ : Config L} (hΓ : Γ.Compatible ε) (f : ℕ → ℕ) :
    (cmap Γ f).Compatible ε := by
  intro r hr r' hr' hrr'
  have key : ∀ u ∈ Γ.V.filter (fun u => f u = r), ∀ u' ∈ Γ.V.filter (fun u' => f u' = r'),
      Γ.z u u' + Γ.z u' u = ε (Γ.t u) * ε (Γ.t u') := by
    intro u hu u' hu'
    simp only [Finset.mem_filter] at hu hu'
    exact hΓ u hu.1 u' hu'.1 (by rintro rfl; exact hrr' (hu.2.symm.trans hu'.2))
  simp only [cmap]
  rw [Finset.sum_comm (s := Γ.V.filter (fun u => f u = r')), ← Finset.sum_add_distrib]
  calc ∑ u ∈ Γ.V.filter (fun u => f u = r), (∑ u' ∈ Γ.V.filter (fun u' => f u' = r'), Γ.z u u'
          + ∑ u' ∈ Γ.V.filter (fun u' => f u' = r'), Γ.z u' u)
        = ∑ u ∈ Γ.V.filter (fun u => f u = r),
            ∑ u' ∈ Γ.V.filter (fun u' => f u' = r'), ε (Γ.t u) * ε (Γ.t u') := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun u' hu' => key u hu u' hu'
    _ = _ := by rw [map_sum, map_sum, Finset.sum_mul_sum]

/-- Contractions along labellings inducing the same partition of `Γ.V` are isomorphic. -/
theorem cmap_iso {Γ : Config L} {f g : ℕ → ℕ}
    (h : ∀ u ∈ Γ.V, ∀ u' ∈ Γ.V, f u = f u' ↔ g u = g u') : (cmap Γ f).IsIso (cmap Γ g) := by
  classical
  have hpre : ∀ r : (cmap Γ f).V, ∃ u, u ∈ Γ.V ∧ f u = r := fun r => Finset.mem_image.1 r.2
  let p : (cmap Γ f).V → ℕ := fun r => (hpre r).choose
  have hp : ∀ r, p r ∈ Γ.V ∧ f (p r) = r := fun r => (hpre r).choose_spec
  let φ : (cmap Γ f).V → (cmap Γ g).V := fun r =>
    ⟨g (p r), Finset.mem_image_of_mem g (hp r).1⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro r₁ r₂ h12
      have h12' : g (p r₁) = g (p r₂) := congrArg Subtype.val h12
      apply Subtype.ext
      rw [← (hp r₁).2, ← (hp r₂).2]
      exact (h _ (hp r₁).1 _ (hp r₂).1).2 h12'
    · rintro ⟨r', hr'⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hr'
      refine ⟨⟨f u, Finset.mem_image_of_mem f hu⟩, Subtype.ext ?_⟩
      have := hp ⟨f u, Finset.mem_image_of_mem f hu⟩
      exact (h _ this.1 _ hu).1 this.2
  have hblock : ∀ r : (cmap Γ f).V,
      Γ.V.filter (fun x => g x = g (p r)) = Γ.V.filter (fun x => f x = r) := by
    intro r
    apply Finset.filter_congr
    intro x hx
    rw [← (hp r).2]
    exact (h x hx _ (hp r).1).symm
  refine ⟨Equiv.ofBijective φ hφ, fun r => ?_, fun r r' _ => ?_⟩
  · show ∑ u ∈ Γ.V.filter (fun x => g x = g (p r)), Γ.t u = ∑ u ∈ Γ.V.filter (fun x => f x = r), Γ.t u
    rw [hblock r]
  · show ∑ u ∈ Γ.V.filter (fun x => g x = g (p r)), ∑ u' ∈ Γ.V.filter (fun x => g x = g (p r')),
        Γ.z u u' = ∑ u ∈ Γ.V.filter (fun x => f x = r), ∑ u' ∈ Γ.V.filter (fun x => f x = r'),
        Γ.z u u'
    rw [hblock r, hblock r']

/-- The number of fibres depends only on the partition. -/
theorem card_image_eq_of_part {V : Finset ℕ} {f g : ℕ → ℕ}
    (h : ∀ u ∈ V, ∀ u' ∈ V, f u = f u' ↔ g u = g u') : (V.image f).card = (V.image g).card := by
  have := card_eq_of_iso (cmap_iso (Γ := (⟨V, fun _ => (0 : ℤ), fun _ _ => 0⟩ : Config ℤ)) h)
  exact this

theorem sum_sum_indicator (B B' : Finset ℕ) (v w : ℕ) :
    (∑ u ∈ B, ∑ u' ∈ B', if u = v ∧ u' = w then (1 : ZMod 2) else 0) =
      if v ∈ B ∧ w ∈ B' then 1 else 0 := by
  have : ∀ u, (∑ u' ∈ B', if u = v ∧ u' = w then (1 : ZMod 2) else 0) =
      if u = v then (if w ∈ B' then 1 else 0) else 0 := by
    intro u
    by_cases h : u = v
    · simp [h]
    · simp [h]
  simp only [this]
  rw [Finset.sum_ite_eq']
  by_cases hv : v ∈ B <;> by_cases hw : w ∈ B' <;> simp [hv, hw]

/-- Effect of one flip on a contraction. -/
theorem cmap_flip_z {Γ : Config L} {f : ℕ → ℕ} {v w : ℕ} (hvw : v ≠ w) (r r' : ℕ) :
    (cmap (Γ.flip v w) f).z r r' = (cmap Γ f).z r r' +
      ((if v ∈ Γ.V.filter (fun u => f u = r) ∧ w ∈ Γ.V.filter (fun u => f u = r') then 1 else 0) +
       (if w ∈ Γ.V.filter (fun u => f u = r) ∧ v ∈ Γ.V.filter (fun u => f u = r') then 1
        else 0)) := by
  simp only [cmap, flip_V, flip_z hvw]
  simp only [Finset.sum_add_distrib, sum_sum_indicator]

/-- A flip inside one fibre does not change the contraction. -/
theorem cmap_flip_same {Γ : Config L} {f : ℕ → ℕ} {v w : ℕ} (hvw : v ≠ w) (hf : f v = f w) :
    cmap (Γ.flip v w) f = cmap Γ f := by
  refine config_ext (by rfl) (by rfl) ?_
  funext r r'
  rw [cmap_flip_z hvw]
  have : (v ∈ Γ.V.filter (fun u => f u = r) ∧ w ∈ Γ.V.filter (fun u => f u = r')) ↔
      (w ∈ Γ.V.filter (fun u => f u = r) ∧ v ∈ Γ.V.filter (fun u => f u = r')) := by
    simp only [Finset.mem_filter, hf]; tauto
  rw [if_congr this rfl rfl, zmod2_add_self, add_zero]

/-- A flip between two fibres is the flip of the contraction. -/
theorem cmap_flip_diff {Γ : Config L} {f : ℕ → ℕ} {v w : ℕ} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V)
    (hf : f v ≠ f w) : cmap (Γ.flip v w) f = (cmap Γ f).flip (f v) (f w) := by
  have hvw : v ≠ w := by rintro rfl; exact hf rfl
  refine config_ext (by rfl) (by rfl) ?_
  funext r r'
  rw [cmap_flip_z hvw, flip_z hf]
  simp only [Finset.mem_filter, hv, hw, true_and]
  congr 2
  · simp only [eq_comm]
  · simp only [eq_comm]

/-! ### Merging two labels -/

/-- Relabel `b` as `a`. -/
def merge (f : ℕ → ℕ) (a b : ℕ) : ℕ → ℕ := fun u => if f u = b then a else f u

theorem merge_eq_iff {g : ℕ → ℕ} {a b x y : ℕ} (hab : a ≠ b) :
    merge g a b x = merge g a b y ↔
      g x = g y ∨ (g x = a ∧ g y = b) ∨ (g x = b ∧ g y = a) := by
  simp only [merge]
  split_ifs <;> omega

theorem merge_filter_a {V : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (hab : a ≠ b) :
    V.filter (fun u => merge f a b u = a) =
      V.filter (fun u => f u = a) ∪ V.filter (fun u => f u = b) := by
  rw [← Finset.filter_or]
  apply Finset.filter_congr
  intro u _
  simp only [merge]
  split_ifs <;> omega

theorem merge_filter_ne {V : Finset ℕ} {f : ℕ → ℕ} {a b x : ℕ} (hxa : x ≠ a) (hxb : x ≠ b) :
    V.filter (fun u => merge f a b u = x) = V.filter (fun u => f u = x) := by
  apply Finset.filter_congr
  intro u _
  simp only [merge]
  split_ifs <;> omega

theorem merge_image {V : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a ∈ V.image f) :
    V.image (merge f a b) = (V.image f).erase b := by
  ext x
  rw [Finset.mem_erase, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    unfold merge
    by_cases h : f u = b
    · rw [ite_eq_left h]; exact ⟨hab, Finset.mem_image.1 ha⟩
    · rw [ite_eq_right h]; exact ⟨h, u, hu, rfl⟩
  · rintro ⟨hxb, u, hu, rfl⟩
    exact ⟨u, hu, by unfold merge; rw [ite_eq_right hxb]⟩

/-- Contracting two labels of a contraction is the contraction along the merged labelling. -/
theorem merge_iso {Γ : Config L} {f : ℕ → ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a ∈ Γ.V.image f) :
    (cmap Γ (merge f a b)).IsIso ((cmap Γ f).contract a b) := by
  have hdisj : Disjoint (Γ.V.filter (fun u => f u = a)) (Γ.V.filter (fun u => f u = b)) :=
    Finset.disjoint_filter.2 (fun u _ h1 h2 => hab (h1.symm.trans h2))
  have hmem : ∀ r ∈ (cmap Γ (merge f a b)).V, r ≠ b := by
    intro r hr
    have : r ∈ (Γ.V.image f).erase b := by rw [← merge_image hab ha]; exact hr
    exact (Finset.mem_erase.1 this).1
  apply iso_of_agree
  · exact merge_image hab ha
  · intro r hr
    have hrb := hmem r hr
    by_cases hra : r = a
    · subst hra
      show Function.update (cmap Γ f).t r ((cmap Γ f).t r + (cmap Γ f).t b) r = _
      rw [Function.update_self]
      show _ = ∑ u ∈ Γ.V.filter (fun u => merge f r b u = r), Γ.t u
      rw [merge_filter_a hab, Finset.sum_union hdisj]
      rfl
    · show Function.update (cmap Γ f).t a ((cmap Γ f).t a + (cmap Γ f).t b) r = _
      rw [Function.update_of_ne hra]
      show _ = ∑ u ∈ Γ.V.filter (fun u => merge f a b u = r), Γ.t u
      rw [merge_filter_ne hra hrb]
      rfl
  · intro r hr r' hr' hrr'
    have hrb := hmem r hr
    have hr'b := hmem r' hr'
    show (if r = a then (cmap Γ f).z a r' + (cmap Γ f).z b r'
      else if r' = a then (cmap Γ f).z r a + (cmap Γ f).z r b else (cmap Γ f).z r r') =
      ∑ u ∈ Γ.V.filter (fun u => merge f a b u = r),
        ∑ u' ∈ Γ.V.filter (fun u' => merge f a b u' = r'), Γ.z u u'
    by_cases hra : r = a
    · subst hra
      have hr'a : r' ≠ r := Ne.symm hrr'
      rw [ite_eq_left rfl, merge_filter_a hab, Finset.sum_union hdisj, merge_filter_ne hr'a hr'b]
      rfl
    · by_cases hr'a : r' = a
      · subst hr'a
        rw [ite_eq_right hra, ite_eq_left rfl, merge_filter_ne hra hrb, merge_filter_a hab]
        simp only [cmap]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_union hdisj]
      · rw [ite_eq_right hra, ite_eq_right hr'a, merge_filter_ne hra hrb, merge_filter_ne hr'a hr'b]
        rfl

/-- The identity contraction. -/
theorem cmap_id_iso (Γ : Config L) : Γ.IsIso (cmap Γ id) := by
  apply iso_of_agree
  · simp [cmap]
  · intro v hv
    simp [cmap, Finset.filter_eq', hv]
  · intro v hv w hw _
    simp [cmap, Finset.filter_eq', hv, hw]

/-! ### Connectivity and blocks -/

theorem conn_refl (S : Finset (Sym2 ℕ)) (a : ℕ) : conn S a a := Relation.EqvGen.refl a
theorem conn_symm {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : conn S a b) : conn S b a :=
  Relation.EqvGen.symm a b h
theorem conn_trans {S : Finset (Sym2 ℕ)} {a b c : ℕ} (h1 : conn S a b) (h2 : conn S b c) :
    conn S a c := Relation.EqvGen.trans a b c h1 h2
theorem conn_of_mem {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : s(a, b) ∈ S) : conn S a b :=
  Relation.EqvGen.rel a b h
theorem conn_mono {S T : Finset (Sym2 ℕ)} (hST : S ⊆ T) {a b : ℕ} (h : conn S a b) :
    conn T a b :=
  Relation.EqvGen.mono (fun x y hxy => hST hxy) a b h

theorem conn_empty {a b : ℕ} (h : conn ∅ a b) : a = b :=
  (Equivalence.eqvGen_iff eq_equivalence).1
    (Relation.EqvGen.mono (fun x y hxy => absurd hxy (Finset.notMem_empty _)) a b h)

/-- Connectivity after adding one pair. -/
theorem conn_insert_iff {S : Finset (Sym2 ℕ)} {v w a b : ℕ} :
    conn (insert s(v, w) S) a b ↔
      conn S a b ∨ (conn S a v ∧ conn S w b) ∨ (conn S a w ∧ conn S v b) := by
  constructor
  · intro h
    let R : ℕ → ℕ → Prop := fun a b =>
      conn S a b ∨ (conn S a v ∧ conn S w b) ∨ (conn S a w ∧ conn S v b)
    have hR : Equivalence R := by
      refine ⟨fun a => Or.inl (conn_refl S a), fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
      · rcases hxy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (conn_symm h)
        · exact Or.inr (Or.inr ⟨conn_symm h2, conn_symm h1⟩)
        · exact Or.inr (Or.inl ⟨conn_symm h2, conn_symm h1⟩)
      · rcases hxy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases hyz with h' | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
        · exact Or.inl (conn_trans h h')
        · exact Or.inr (Or.inl ⟨conn_trans h h1', h2'⟩)
        · exact Or.inr (Or.inr ⟨conn_trans h h1', h2'⟩)
        · exact Or.inr (Or.inl ⟨h1, conn_trans h2 h'⟩)
        · exact Or.inr (Or.inl ⟨h1, h2'⟩)
        · exact Or.inl (conn_trans h1 h2')
        · exact Or.inr (Or.inr ⟨h1, conn_trans h2 h'⟩)
        · exact Or.inl (conn_trans h1 h2')
        · exact Or.inr (Or.inr ⟨h1, h2'⟩)
    have hmono : Relation.EqvGen R a b := by
      refine Relation.EqvGen.mono ?_ a b h
      intro x y hxy
      rcases Finset.mem_insert.1 hxy with he | he
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨conn_refl S _, conn_refl S _⟩)
        · exact Or.inr (Or.inr ⟨conn_refl S _, conn_refl S _⟩)
      · exact Or.inl (conn_of_mem he)
    exact hR.eqvGen_iff.1 hmono
  · have hsub : S ⊆ insert s(v, w) S := Finset.subset_insert _ _
    have hvw : conn (insert s(v, w) S) v w := conn_of_mem (Finset.mem_insert_self _ _)
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact conn_mono hsub h
    · exact conn_trans (conn_mono hsub h1) (conn_trans hvw (conn_mono hsub h2))
    · exact conn_trans (conn_mono hsub h1) (conn_trans (conn_symm hvw) (conn_mono hsub h2))

open Classical in
theorem rep_of_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u : ℕ} (hu : u ∈ V) :
    rep V S u = (V.filter (fun x => conn S x u)).min'
      ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩ := by
  unfold rep
  rw [dite_eq_left ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩]

theorem rep_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u : ℕ} (hu : u ∈ V) : rep V S u ∈ V := by
  classical
  rw [rep_of_mem hu]
  have := Finset.min'_mem (V.filter (fun x => conn S x u)) ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩
  exact (Finset.mem_filter.1 this).1

theorem rep_conn {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u : ℕ} (hu : u ∈ V) :
    conn S (rep V S u) u := by
  classical
  rw [rep_of_mem hu]
  have := Finset.min'_mem (V.filter (fun x => conn S x u)) ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩
  exact (Finset.mem_filter.1 this).2

theorem rep_eq_iff {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) :
    rep V S u = rep V S u' ↔ conn S u u' := by
  classical
  constructor
  · intro h
    have h1 := rep_conn (S := S) hu
    have h2 := rep_conn (S := S) hu'
    rw [h] at h1
    exact conn_trans (conn_symm h1) h2
  · intro h
    apply le_antisymm
    · rw [rep_of_mem hu]
      apply Finset.min'_le
      exact Finset.mem_filter.2 ⟨rep_mem hu', conn_trans (rep_conn hu') (conn_symm h)⟩
    · rw [rep_of_mem hu']
      apply Finset.min'_le
      exact Finset.mem_filter.2 ⟨rep_mem hu, conn_trans (rep_conn hu) h⟩

theorem mem_pairs {V : Finset ℕ} {e : Sym2 ℕ} :
    e ∈ pairs V ↔ ∃ v w, v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ s(v, w) = e := by
  unfold pairs
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨v, w, ⟨⟨hv, hw⟩, hvw⟩, rfl⟩; exact ⟨v, w, hv, hw, hvw, rfl⟩
  · rintro ⟨v, w, hv, hw, hvw, rfl⟩; exact ⟨v, w, ⟨⟨hv, hw⟩, hvw⟩, rfl⟩

theorem ncomp_empty (V : Finset ℕ) : ncomp V ∅ = V.card := by
  unfold ncomp
  apply Finset.card_image_of_injOn
  intro u hu u' hu' h
  exact conn_empty ((rep_eq_iff hu hu').1 h)

theorem ncomp_insert_of_conn {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (h : conn S v w) :
    ncomp V (insert s(v, w) S) = ncomp V S := by
  unfold ncomp
  apply card_image_eq_of_part
  intro u hu u' hu'
  rw [rep_eq_iff hu hu', rep_eq_iff hu hu', conn_insert_iff]
  constructor
  · rintro (h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h1
    · exact conn_trans h1 (conn_trans h h2)
    · exact conn_trans h1 (conn_trans (conn_symm h) h2)
  · exact Or.inl

/-- Blocks after adding a pair between two blocks: the two blocks are merged. -/
theorem part_insert {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (hv : v ∈ V) (hw : w ∈ V)
    (hc : ¬ conn S v w) : ∀ u ∈ V, ∀ u' ∈ V,
      (rep V (insert s(v, w) S) u = rep V (insert s(v, w) S) u' ↔
        merge (rep V S) (rep V S v) (rep V S w) u = merge (rep V S) (rep V S v) (rep V S w) u') := by
  intro u hu u' hu'
  have hab : rep V S v ≠ rep V S w := fun h => hc ((rep_eq_iff hv hw).1 h)
  rw [rep_eq_iff hu hu', conn_insert_iff, merge_eq_iff hab, rep_eq_iff hu hu', rep_eq_iff hu hv,
    rep_eq_iff hu' hw, rep_eq_iff hu hw, rep_eq_iff hu' hv]
  constructor
  · rintro (h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h1, conn_symm h2⟩)
    · exact Or.inr (Or.inr ⟨h1, conn_symm h2⟩)
  · rintro (h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h1, conn_symm h2⟩)
    · exact Or.inr (Or.inr ⟨h1, conn_symm h2⟩)

theorem ncomp_insert_of_not_conn {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (hv : v ∈ V)
    (hw : w ∈ V) (hc : ¬ conn S v w) : ncomp V (insert s(v, w) S) + 1 = ncomp V S := by
  have hab : rep V S v ≠ rep V S w := fun h => hc ((rep_eq_iff hv hw).1 h)
  unfold ncomp
  rw [card_image_eq_of_part (part_insert hv hw hc),
    merge_image hab (Finset.mem_image_of_mem _ hv),
    Finset.card_erase_of_mem (Finset.mem_image_of_mem _ hw)]
  have : 0 < (V.image (rep V S)).card :=
    Finset.card_pos.2 ⟨_, Finset.mem_image_of_mem _ hw⟩
  omega

/-- Edges plus components are at least the vertices. -/
theorem card_add_ncomp_ge {V : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs V) :
    V.card ≤ S.card + ncomp V S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ncomp_empty]
  | insert e S he ih =>
    obtain ⟨v, w, hv, hw, _, rfl⟩ := mem_pairs.1 (hS (Finset.mem_insert_self _ _))
    have ih' := ih ((Finset.subset_insert _ _).trans hS)
    rw [Finset.card_insert_of_notMem he]
    by_cases hc : conn S v w
    · rw [ncomp_insert_of_conn hc]; omega
    · have := ncomp_insert_of_not_conn hv hw hc; omega

theorem isForest_insert_iff {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (hv : v ∈ V)
    (hw : w ∈ V) (he : s(v, w) ∉ S) (hsub : insert s(v, w) S ⊆ pairs V) (hc : ¬ conn S v w) :
    IsForest V (insert s(v, w) S) ↔ IsForest V S := by
  have h1 := ncomp_insert_of_not_conn hv hw hc
  have h2 := Finset.card_insert_of_notMem he
  unfold IsForest
  constructor
  · rintro ⟨-, hc⟩; exact ⟨(Finset.subset_insert _ _).trans hsub, by omega⟩
  · rintro ⟨-, hc⟩; exact ⟨hsub, by omega⟩

theorem not_isForest_insert {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (he : s(v, w) ∉ S)
    (hsub : insert s(v, w) S ⊆ pairs V) (hc : conn S v w) : ¬ IsForest V (insert s(v, w) S) := by
  have h1 := ncomp_insert_of_conn (V := V) hc
  have h2 := Finset.card_insert_of_notMem he
  have h3 := card_add_ncomp_ge ((Finset.subset_insert _ _).trans hsub)
  rintro ⟨-, h⟩
  omega

open Classical in
theorem diff_eq_forest_aux (hA : CoefficientRules ε A) (S : Finset (Sym2 ℕ)) :
    ∀ Γ : Config L, Γ.Compatible ε → S ⊆ pairs Γ.V →
      diff A Γ S = if IsForest Γ.V S then A (cmap Γ (rep Γ.V S)) else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro Γ hΓ _
    have hF : IsForest Γ.V ∅ := ⟨Finset.empty_subset _, by simp [ncomp_empty]⟩
    rw [ite_eq_left hF]
    simp only [diff, Finset.powerset_empty, Finset.sum_singleton, flipBy_empty]
    have h1 : (cmap Γ id).IsIso (cmap Γ (rep Γ.V ∅)) := cmap_iso (fun u hu u' hu' => by
      rw [rep_eq_iff hu hu']
      exact ⟨fun h => by rw [show u = u' from h]; exact conn_refl _ _, conn_empty⟩)
    rw [hA.graph_dependence _ _ hΓ (cmap_id_iso Γ),
      hA.graph_dependence _ _ (cmap_compatible hΓ id) h1]
  | insert e S he ih =>
    intro Γ hΓ hsub
    obtain ⟨v, w, hv, hw, hvw, rfl⟩ := mem_pairs.1 (hsub (Finset.mem_insert_self _ _))
    have hsubS : S ⊆ pairs Γ.V := (Finset.subset_insert _ _).trans hsub
    rw [diff_insert A Γ he, ih Γ hΓ hsubS, ih (Γ.flipBy {s(v, w)}) (flipBy_compatible hΓ _) hsubS]
    change (if IsForest Γ.V S then A (cmap Γ (rep Γ.V S)) else 0) +
      (if IsForest Γ.V S then A (cmap (Γ.flip v w) (rep Γ.V S)) else 0) = _
    by_cases hc : conn S v w
    · rw [cmap_flip_same hvw ((rep_eq_iff hv hw).2 hc), ite_eq_right (not_isForest_insert he hsub hc)]
      exact zmod2_add_self _
    · have hne : rep Γ.V S v ≠ rep Γ.V S w := fun h => hc ((rep_eq_iff hv hw).1 h)
      rw [cmap_flip_diff hv hw hne]
      have hF := isForest_insert_iff hv hw he hsub hc
      by_cases hFS : IsForest Γ.V S
      · rw [ite_eq_left hFS, ite_eq_left hFS, ite_eq_left (hF.2 hFS)]
        rw [hA.contraction _ (cmap_compatible hΓ _) _ (Finset.mem_image_of_mem _ hv) _
          (Finset.mem_image_of_mem _ hw) hne]
        rw [← hA.graph_dependence _ _ (cmap_compatible hΓ _)
          (merge_iso hne (Finset.mem_image_of_mem _ hv))]
        apply hA.graph_dependence _ _ (cmap_compatible hΓ _)
        apply cmap_iso
        intro u hu u' hu'
        exact (part_insert hv hw hc u hu u' hu').symm
      · rw [ite_eq_right hFS, ite_eq_right hFS, ite_eq_right (fun h => hFS (hF.1 h)), add_zero]

end ForestAux

open ForestAux

/-- Contraction by a forest preserves reciprocity compatibility: blocks are disjoint and the
sign coordinate is additive (tex 2050–2054). Kind: PROVED. -/
theorem Config.Compatible.contractBy {Γ : Config L} (h : Γ.Compatible ε) (S : Finset (Sym2 ℕ)) :
    (Γ.contractBy S).Compatible ε :=
  cmap_compatible h _

open Classical in
/-- Forest product: iterated differences along a forest give the contracted symbol; a cycle
product is zero (tex 2200–2202, 10627–10633). Kind: PROVED. -/
theorem diff_eq_forest (hA : CoefficientRules ε A) {Γ : Config L} (hΓ : Γ.Compatible ε)
    {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs Γ.V) :
    diff A Γ S = if IsForest Γ.V S then A (Γ.contractBy S) else 0 :=
  diff_eq_forest_aux hA S Γ hΓ hS

end ZInQ.Manuscript.RC.Symbols
