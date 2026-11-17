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

omit [AddCommGroup L] in
/-- Extensionality for configurations (tex 2015–2041). Kind: PROVED (helper). -/
theorem config_ext {Γ Δ : Config L} (hV : Γ.V = Δ.V) (ht : Γ.t = Δ.t) (hz : Γ.z = Δ.z) :
    Γ = Δ := by
  cases Γ; cases Δ; simp_all

omit [AddCommGroup L] in
/-- Two configurations agreeing on the vertex set (types, and bits of distinct pairs) are
isomorphic through the identity (tex 2102–2110). Kind: PROVED (helper). -/
theorem iso_of_agree {Γ Δ : Config L} (hV : Γ.V = Δ.V) (ht : ∀ v ∈ Γ.V, Δ.t v = Γ.t v)
    (hz : ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ≠ w → Δ.z v w = Γ.z v w) : Γ.IsIso Δ :=
  ⟨Equiv.subtypeEquivRight (fun x => by rw [hV]), fun v => ht v v.2,
    fun v w hvw => hz v v.2 w w.2 (fun h => hvw (Subtype.ext h))⟩

/-- Isomorphisms transport compatibility (tex 2037–2041, 2102–2110). Kind: PROVED (helper). -/
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

omit [AddCommGroup L] in
/-- Isomorphic configurations have the same number of vertices (tex 2102–2110). Kind: PROVED
(helper). -/
theorem card_eq_of_iso {Γ Δ : Config L} (h : Γ.IsIso Δ) : Γ.V.card = Δ.V.card := by
  obtain ⟨e, -, -⟩ := h
  simpa using Fintype.card_congr e

/-! ### Flips -/

omit [AddCommGroup L] in
/-- A change of bits keeps the vertices (tex 2107–2111). Kind: PROVED (helper). -/
@[simp] theorem flipBy_V (Γ : Config L) (U : Finset (Sym2 ℕ)) : (Γ.flipBy U).V = Γ.V := rfl
omit [AddCommGroup L] in
/-- A change of bits keeps the types (tex 2107–2111). Kind: PROVED (helper). -/
@[simp] theorem flipBy_t (Γ : Config L) (U : Finset (Sym2 ℕ)) : (Γ.flipBy U).t = Γ.t := rfl
omit [AddCommGroup L] in
/-- A flip keeps the vertices (tex 2113–2116). Kind: PROVED (helper). -/
@[simp] theorem flip_V (Γ : Config L) (v w : ℕ) : (Γ.flip v w).V = Γ.V := rfl
omit [AddCommGroup L] in
/-- A flip keeps the types (tex 2113–2116). Kind: PROVED (helper). -/
@[simp] theorem flip_t (Γ : Config L) (v w : ℕ) : (Γ.flip v w).t = Γ.t := rfl

/-- Characteristic two: a repeated difference cancels (tex 10625–10627). Kind: PROVED (helper). -/
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- A change of independent bits keeps reciprocity compatibility (tex 2037–2041, 2113–2116). Kind:
PROVED (helper). -/
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

omit [AddCommGroup L] in
/-- The empty change of bits (tex 2219). Kind: PROVED (helper). -/
theorem flipBy_empty (Γ : Config L) : Γ.flipBy ∅ = Γ := by
  refine config_ext (by rfl) (by rfl) ?_
  funext a b
  simp [Config.flipBy]

omit [AddCommGroup L] in
/-- Changes of bits compose (tex 2219, 10625–10627). Kind: PROVED (helper). -/
theorem flipBy_insert (Γ : Config L) {e : Sym2 ℕ} {U : Finset (Sym2 ℕ)} (he : e ∉ U) :
    Γ.flipBy (insert e U) = (Γ.flipBy {e}).flipBy U := by
  refine config_ext (by rfl) (by rfl) ?_
  funext a b
  simp only [Config.flipBy, Finset.mem_insert, Finset.mem_singleton]
  by_cases hab : a ≠ b
  · by_cases h1 : s(a, b) = e
    · have h2 : s(a, b) ∉ U := h1 ▸ he
      simp [hab, h1]
      subst h1; simp [h2]
    · by_cases h2 : s(a, b) ∈ U <;> simp [hab, h1, h2]
  · simp [hab]

omit [AddCommGroup L] in
/-- One flip, written with indicator functions (tex 2113–2116). Kind: PROVED (helper). -/
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

omit [AddCommGroup L] in
/-- Finite difference along one more pair (tex 2219, 10625–10627). Kind: PROVED (helper). -/
theorem diff_insert (A : Config L → ZMod 2) (Γ : Config L) {e : Sym2 ℕ} {S : Finset (Sym2 ℕ)}
    (he : e ∉ S) : diff A Γ (insert e S) = diff A Γ S + diff A (Γ.flipBy {e}) S := by
  unfold diff
  rw [Finset.sum_powerset_insert he]
  congr 1
  refine Finset.sum_congr rfl fun U hU => ?_
  rw [flipBy_insert Γ (fun h => he (Finset.mem_powerset.1 hU h))]

/-! ### Contraction along a labelling of the vertices -/

/-- Contraction of each fibre of `f` (on `Γ.V`) to its label: summed types and incidences (tex
2050–2054). Helper definition. -/
def cmap (Γ : Config L) (f : ℕ → ℕ) : Config L where
  V := Γ.V.image f
  t := fun r => ∑ u ∈ Γ.V.filter (fun u => f u = r), Γ.t u
  z := fun r r' => ∑ u ∈ Γ.V.filter (fun u => f u = r),
    ∑ u' ∈ Γ.V.filter (fun u' => f u' = r'), Γ.z u u'

/-- Contraction by a forest is contraction along the block representatives (tex 2050–2054). Kind:
PROVED (helper). -/
theorem contractBy_eq (Γ : Config L) (S : Finset (Sym2 ℕ)) :
    Γ.contractBy S = cmap Γ (rep Γ.V S) := rfl

/-- Contraction along a labelling preserves compatibility: blocks are disjoint and the sign
coordinate is additive (tex 2037–2041, 2050–2054). Kind: PROVED (helper). -/
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

/-- Contractions along labellings inducing the same partition of `Γ.V` are isomorphic (tex
2102–2110). Kind: PROVED (helper). -/
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
  · show ∑ u ∈ Γ.V.filter (fun x => g x = g (p r)), Γ.t u =
      ∑ u ∈ Γ.V.filter (fun x => f x = r), Γ.t u
    rw [hblock r]
  · show ∑ u ∈ Γ.V.filter (fun x => g x = g (p r)), ∑ u' ∈ Γ.V.filter (fun x => g x = g (p r')),
        Γ.z u u' = ∑ u ∈ Γ.V.filter (fun x => f x = r), ∑ u' ∈ Γ.V.filter (fun x => f x = r'),
        Γ.z u u'
    rw [hblock r, hblock r']

/-- The number of fibres depends only on the partition (tex 2181–2185). Kind: PROVED (helper). -/
theorem card_image_eq_of_part {V : Finset ℕ} {f g : ℕ → ℕ}
    (h : ∀ u ∈ V, ∀ u' ∈ V, f u = f u' ↔ g u = g u') : (V.image f).card = (V.image g).card := by
  have := card_eq_of_iso (cmap_iso (Γ := (⟨V, fun _ => (0 : ℤ), fun _ _ => 0⟩ : Config ℤ)) h)
  exact this

/-- Double sum of a point indicator (tex 2050–2054). Kind: PROVED (helper). -/
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

/-- Effect of one flip on a contraction (tex 2113–2120). Kind: PROVED (helper). -/
theorem cmap_flip_z {Γ : Config L} {f : ℕ → ℕ} {v w : ℕ} (hvw : v ≠ w) (r r' : ℕ) :
    (cmap (Γ.flip v w) f).z r r' = (cmap Γ f).z r r' +
      ((if v ∈ Γ.V.filter (fun u => f u = r) ∧ w ∈ Γ.V.filter (fun u => f u = r') then 1 else 0) +
       (if w ∈ Γ.V.filter (fun u => f u = r) ∧ v ∈ Γ.V.filter (fun u => f u = r') then 1
        else 0)) := by
  simp only [cmap, flip_V, flip_z hvw]
  simp only [Finset.sum_add_distrib, sum_sum_indicator]

/-- A flip inside one fibre does not change the contraction (tex 10627–10633). Kind: PROVED
(helper). -/
theorem cmap_flip_same {Γ : Config L} {f : ℕ → ℕ} {v w : ℕ} (hvw : v ≠ w) (hf : f v = f w) :
    cmap (Γ.flip v w) f = cmap Γ f := by
  refine config_ext (by rfl) (by rfl) ?_
  funext r r'
  rw [cmap_flip_z hvw]
  have : (v ∈ Γ.V.filter (fun u => f u = r) ∧ w ∈ Γ.V.filter (fun u => f u = r')) ↔
      (w ∈ Γ.V.filter (fun u => f u = r) ∧ v ∈ Γ.V.filter (fun u => f u = r')) := by
    simp only [Finset.mem_filter, hf]; tauto
  rw [if_congr this rfl rfl, zmod2_add_self, add_zero]

/-- A flip between two fibres is the flip of the contraction (tex 2113–2120). Kind: PROVED (helper).
-/
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

/-- Relabel `b` as `a` (tex 2050–2054). Helper definition. -/
def merge (f : ℕ → ℕ) (a b : ℕ) : ℕ → ℕ := fun u => if f u = b then a else f u

/-- Fibres of a merged labelling (tex 2050–2054). Kind: PROVED (helper). -/
theorem merge_eq_iff {g : ℕ → ℕ} {a b x y : ℕ} :
    merge g a b x = merge g a b y ↔
      g x = g y ∨ (g x = a ∧ g y = b) ∨ (g x = b ∧ g y = a) := by
  simp only [merge]
  split_ifs <;> omega

/-- The merged fibre is the union of the two fibres (tex 2050–2054). Kind: PROVED (helper). -/
theorem merge_filter_a {V : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} :
    V.filter (fun u => merge f a b u = a) =
      V.filter (fun u => f u = a) ∪ V.filter (fun u => f u = b) := by
  rw [← Finset.filter_or]
  apply Finset.filter_congr
  intro u _
  simp only [merge]
  split_ifs <;> omega

/-- The other fibres are unchanged by merging (tex 2050–2054). Kind: PROVED (helper). -/
theorem merge_filter_ne {V : Finset ℕ} {f : ℕ → ℕ} {a b x : ℕ} (hxa : x ≠ a) (hxb : x ≠ b) :
    V.filter (fun u => merge f a b u = x) = V.filter (fun u => f u = x) := by
  apply Finset.filter_congr
  intro u _
  simp only [merge]
  split_ifs <;> omega

/-- Labels of a merged labelling (tex 2050–2054). Kind: PROVED (helper). -/
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

/-- Contracting two labels of a contraction is the contraction along the merged labelling (tex
2050–2054, 2113–2120). Kind: PROVED (helper). -/
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
      rw [merge_filter_a, Finset.sum_union hdisj]
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
      rw [ite_eq_left rfl, merge_filter_a, Finset.sum_union hdisj, merge_filter_ne hr'a hr'b]
      rfl
    · by_cases hr'a : r' = a
      · subst hr'a
        rw [ite_eq_right hra, ite_eq_left rfl, merge_filter_ne hra hrb, merge_filter_a]
        simp only [cmap]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_union hdisj]
      · rw [ite_eq_right hra, ite_eq_right hr'a, merge_filter_ne hra hrb, merge_filter_ne hr'a hr'b]
        rfl

/-- The identity contraction (tex 2050–2054). Kind: PROVED (helper). -/
theorem cmap_id_iso (Γ : Config L) : Γ.IsIso (cmap Γ id) := by
  apply iso_of_agree
  · simp [cmap]
  · intro v hv
    simp [cmap, Finset.filter_eq', hv]
  · intro v hv w hw _
    simp [cmap, Finset.filter_eq', hv, hw]

/-! ### Connectivity and blocks -/

/-- Connectivity is reflexive (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_refl (S : Finset (Sym2 ℕ)) (a : ℕ) : conn S a a := Relation.EqvGen.refl a
/-- Connectivity is symmetric (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_symm {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : conn S a b) : conn S b a :=
  Relation.EqvGen.symm a b h
/-- Connectivity is transitive (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_trans {S : Finset (Sym2 ℕ)} {a b c : ℕ} (h1 : conn S a b) (h2 : conn S b c) :
    conn S a c := Relation.EqvGen.trans a b c h1 h2
/-- A pair of the forest connects its ends (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_of_mem {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : s(a, b) ∈ S) : conn S a b :=
  Relation.EqvGen.rel a b h
/-- Connectivity is monotone in the pair set (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_mono {S T : Finset (Sym2 ℕ)} (hST : S ⊆ T) {a b : ℕ} (h : conn S a b) :
    conn T a b :=
  Relation.EqvGen.mono (fun _ _ hxy => hST hxy) a b h

/-- Without pairs only equal vertices are connected (tex 2181–2185). Kind: PROVED (helper). -/
theorem conn_empty {a b : ℕ} (h : conn ∅ a b) : a = b :=
  (Equivalence.eqvGen_iff eq_equivalence).1
    (Relation.EqvGen.mono (fun _ _ hxy => absurd hxy (Finset.notMem_empty _)) a b h)

/-- Connectivity after adding one pair (tex 2181–2185). Kind: PROVED (helper). -/
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
/-- The block representative of a vertex (tex 2181–2185). Kind: PROVED (helper). -/
theorem rep_of_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u : ℕ} (hu : u ∈ V) :
    rep V S u = (V.filter (fun x => conn S x u)).min'
      ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩ := by
  unfold rep
  rw [dite_eq_left ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩]

/-- The block representative is a vertex (tex 2181–2185). Kind: PROVED (helper). -/
theorem rep_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u : ℕ} (hu : u ∈ V) : rep V S u ∈ V := by
  classical
  rw [rep_of_mem hu]
  have := Finset.min'_mem (V.filter (fun x => conn S x u))
    ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩
  exact (Finset.mem_filter.1 this).1

/-- The block representative is connected to the vertex (tex 2181–2185). Kind: PROVED (helper). -/
theorem rep_conn {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u : ℕ} (hu : u ∈ V) :
    conn S (rep V S u) u := by
  classical
  rw [rep_of_mem hu]
  have := Finset.min'_mem (V.filter (fun x => conn S x u))
    ⟨u, Finset.mem_filter.2 ⟨hu, conn_refl S u⟩⟩
  exact (Finset.mem_filter.1 this).2

/-- Two vertices have the same representative exactly when they are connected (tex 2181–2185). Kind:
PROVED (helper). -/
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

/-- Membership in the pairs of distinct vertices (tex 2209–2219). Kind: PROVED (helper). -/
theorem mem_pairs {V : Finset ℕ} {e : Sym2 ℕ} :
    e ∈ pairs V ↔ ∃ v w, v ∈ V ∧ w ∈ V ∧ v ≠ w ∧ s(v, w) = e := by
  unfold pairs
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨v, w, ⟨⟨hv, hw⟩, hvw⟩, rfl⟩; exact ⟨v, w, hv, hw, hvw, rfl⟩
  · rintro ⟨v, w, hv, hw, hvw, rfl⟩; exact ⟨v, w, ⟨⟨hv, hw⟩, hvw⟩, rfl⟩

/-- Without pairs every vertex is its own block (tex 2181–2185). Kind: PROVED (helper). -/
theorem ncomp_empty (V : Finset ℕ) : ncomp V ∅ = V.card := by
  unfold ncomp
  apply Finset.card_image_of_injOn
  intro u hu u' hu' h
  exact conn_empty ((rep_eq_iff hu hu').1 h)

/-- A pair inside one block does not change the blocks (tex 10627–10633). Kind: PROVED (helper). -/
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

/-- Blocks after adding a pair between two blocks: the two blocks are merged (tex 2181–2185). Kind:
PROVED (helper). -/
theorem part_insert {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (hv : v ∈ V) (hw : w ∈ V)
    (hc : ¬ conn S v w) : ∀ u ∈ V, ∀ u' ∈ V,
      (rep V (insert s(v, w) S) u = rep V (insert s(v, w) S) u' ↔
        merge (rep V S) (rep V S v) (rep V S w) u =
          merge (rep V S) (rep V S v) (rep V S w) u') := by
  intro u hu u' hu'
  have hab : rep V S v ≠ rep V S w := fun h => hc ((rep_eq_iff hv hw).1 h)
  rw [rep_eq_iff hu hu', conn_insert_iff, merge_eq_iff, rep_eq_iff hu hu', rep_eq_iff hu hv,
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

/-- A pair between two blocks merges them (tex 2181–2185, 10627–10633). Kind: PROVED (helper). -/
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

/-- Edges plus components are at least the vertices (tex 2181–2185, 10627–10633). Kind: PROVED
(helper). -/
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

/-- A pair between two blocks keeps the forest condition (tex 2181–2185). Kind: PROVED (helper). -/
theorem isForest_insert_iff {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (hv : v ∈ V)
    (hw : w ∈ V) (he : s(v, w) ∉ S) (hsub : insert s(v, w) S ⊆ pairs V) (hc : ¬ conn S v w) :
    IsForest V (insert s(v, w) S) ↔ IsForest V S := by
  have h1 := ncomp_insert_of_not_conn hv hw hc
  have h2 := Finset.card_insert_of_notMem he
  unfold IsForest
  constructor
  · rintro ⟨-, hc⟩; exact ⟨(Finset.subset_insert _ _).trans hsub, by omega⟩
  · rintro ⟨-, hc⟩; exact ⟨hsub, by omega⟩

/-- A pair inside one block closes a cycle (tex 10627–10633). Kind: PROVED (helper). -/
theorem not_isForest_insert {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v w : ℕ} (he : s(v, w) ∉ S)
    (hsub : insert s(v, w) S ⊆ pairs V) (hc : conn S v w) : ¬ IsForest V (insert s(v, w) S) := by
  have h1 := ncomp_insert_of_conn (V := V) hc
  have h2 := Finset.card_insert_of_notMem he
  have h3 := card_add_ncomp_ge ((Finset.subset_insert _ _).trans hsub)
  rintro ⟨-, h⟩
  omega

open Classical in
/-- Forest product along a labelling by block representatives, by induction on the pair set (tex
2200–2202, 10627–10633). Kind: PROVED (helper). -/
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
    · rw [cmap_flip_same hvw ((rep_eq_iff hv hw).2 hc),
        ite_eq_right (not_isForest_insert he hsub hc)]
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


/-! ### Small facts used for seeds -/

/-- Values in the two-element field (tex 2068–2079). Kind: PROVED (helper). -/
theorem zmod2_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

/-- Values in the two-element field (tex 2068–2079). Kind: PROVED (helper). -/
theorem zmod2_eq_add_one_of_ne : ∀ x y : ZMod 2, x ≠ y → x = y + 1 := by decide

/-- Solving a contraction identity in characteristic two (tex 2113–2120). Kind: PROVED (helper). -/
theorem zmod2_eq_of_add {x y z : ZMod 2} (h : x + y = z) : y = z + x := by
  rw [← h, add_comm x y, add_assoc, zmod2_add_self, add_zero]

omit [AddCommGroup L] in
/-- Isomorphism of typed graphs is symmetric (tex 2102–2110). Kind: PROVED (helper). -/
theorem iso_symm {Γ Δ : Config L} (h : Γ.IsIso Δ) : Δ.IsIso Γ := by
  obtain ⟨e, ht, hz⟩ := h
  refine ⟨e.symm, fun a => ?_, fun a b hab => ?_⟩
  · have := ht (e.symm a)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · have hne : e.symm a ≠ e.symm b := fun h' => hab (e.symm.injective h')
    have := hz (e.symm a) (e.symm b) hne
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm

omit [AddCommGroup L] in
/-- Changes of bits commute (tex 10625–10627). Kind: PROVED (helper). -/
theorem flipBy_comm (Γ : Config L) (U U' : Finset (Sym2 ℕ)) :
    (Γ.flipBy U).flipBy U' = (Γ.flipBy U').flipBy U := by
  refine config_ext (by rfl) (by rfl) ?_
  funext a b
  simp only [Config.flipBy]
  ring

/-- Contraction of two vertices preserves compatibility (tex 2037–2041, 2050–2054). Kind: PROVED
(helper). -/
theorem contract_compatible {Γ : Config L} (hΓ : Γ.Compatible ε) {v w : ℕ} (hv : v ∈ Γ.V)
    (hw : w ∈ Γ.V) : (Γ.contract v w).Compatible ε := by
  intro a ha b hb hab
  simp only [Config.contract, Finset.mem_erase] at ha hb ⊢
  by_cases hav : a = v
  · subst hav
    have hbv : b ≠ a := Ne.symm hab
    simp only [hbv, ite_true, ite_false, Function.update_self, Function.update_of_ne hbv, map_add]
    linear_combination hΓ a hv b hb.2 hab + hΓ w hw b hb.2 (Ne.symm hb.1)
  · by_cases hbv : b = v
    · subst hbv
      simp only [hav, ite_true, ite_false, Function.update_self, Function.update_of_ne hav,
        map_add]
      linear_combination hΓ a ha.2 b hv hab + hΓ a ha.2 w hw ha.1
    · simp only [hav, hbv, ite_false, Function.update_of_ne hav, Function.update_of_ne hbv]
      exact hΓ a ha.2 b hb.2 hab

/-- Rank of a vertex in a finite set of naturals (tex 10614–10617). Kind: PROVED (helper). -/
theorem rank_lt {V : Finset ℕ} {v : ℕ} (hv : v ∈ V) : (V.filter (· < v)).card < V.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨v, hv, by simp⟩

/-- Ranks increase along the order (tex 10614–10617). Kind: PROVED (helper). -/
theorem rank_lt_rank {V : Finset ℕ} {v v' : ℕ} (hv : v ∈ V) (hlt : v < v') :
    (V.filter (· < v)).card < (V.filter (· < v')).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hlt⟩)]
  exact ⟨v, by simp [hv, hlt], by simp⟩

/-- Ranks are injective, giving distinct copies for distinct seed vertices (tex 10614–10617). Kind:
PROVED (helper). -/
theorem rank_injOn (V : Finset ℕ) : Set.InjOn (fun v => (V.filter (· < v)).card) V := by
  intro v hv v' hv' h
  simp only at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := rank_lt_rank hv hlt; omega
  · have := rank_lt_rank hv' hlt; omega

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

/-- Unit seed (tex 2177). -/
def IsUnitSeed (ε : L →+ ZMod 2) (A : Config L → ZMod 2) (Γ : Config L) : Prop :=
  Γ.Compatible ε ∧ A Γ = 1
/-- Minimum nonempty seed (tex 2178–2180). -/
def IsMinSeed (ε : L →+ ZMod 2) (A : Config L → ZMod 2) (Γ : Config L) : Prop :=
  IsUnitSeed ε A Γ ∧ Γ.V.Nonempty ∧
    ∀ Δ : Config L, IsUnitSeed ε A Δ → Δ.V.Nonempty → Γ.V.card ≤ Δ.V.card
/-- Partitionable list (tex 2181–2185): a contraction certificate. -/
def IsPartitionable (_ε : L →+ ZMod 2) (A : Config L → ZMod 2) (Γ : Config L) : Prop :=
  Γ.V.Nonempty ∧ ∃ S, IsForest Γ.V S ∧ A (Γ.contractBy S) = 1

/-- At a minimum seed every change of the internal bits keeps the value one (tex 2197–2200):
a nonzero difference would, by contraction, give a unit seed on fewer nonempty vertices. Kind:
PROVED (helper). -/
theorem ForestAux.minSeed_flipBy (hA : CoefficientRules ε A) {Γ : Config L}
    (hmin : IsMinSeed ε A Γ) : ∀ U ⊆ pairs Γ.V, A (Γ.flipBy U) = 1 := by
  classical
  intro U
  induction U using Finset.induction_on with
  | empty => intro _; rw [flipBy_empty]; exact hmin.1.2
  | insert e U he ih =>
    intro hsub
    obtain ⟨v, w, hv, hw, hvw, rfl⟩ := mem_pairs.1 (hsub (Finset.mem_insert_self _ _))
    have h1 := ih ((Finset.subset_insert _ _).trans hsub)
    have hcU : (Γ.flipBy U).Compatible ε := flipBy_compatible hmin.1.1 U
    have hc := hA.contraction (Γ.flipBy U) hcU v hv w hw hvw
    have h0 : A ((Γ.flipBy U).contract v w) = 0 := by
      by_contra hne
      have h1' : A ((Γ.flipBy U).contract v w) = 1 := zmod2_eq_one_of_ne_zero _ hne
      have hle := hmin.2.2 _ ⟨contract_compatible hcU hv hw, h1'⟩
        ⟨v, Finset.mem_erase.2 ⟨hvw, hv⟩⟩
      have : ((Γ.flipBy U).contract v w).V.card + 1 = Γ.V.card := Finset.card_erase_add_one hw
      omega
    rw [flipBy_insert Γ he, flipBy_comm]
    change A ((Γ.flipBy U).flip v w) = 1
    rw [zmod2_eq_of_add hc, h0, h1, zero_add]

/-- Minimum seeds: the value is independent of all internal pair bits and depends only on the
vertex types (tex 2192–2200). Kind: PROVED. -/
theorem minSeed_bits_irrelevant (hA : CoefficientRules ε A) {Γ : Config L}
    (hmin : IsMinSeed ε A Γ) {Δ : Config L} (hΔ : Δ.Compatible ε) (hV : Δ.V = Γ.V)
    (ht : ∀ v ∈ Γ.V, Δ.t v = Γ.t v) : A Δ = 1 := by
  classical
  let U : Finset (Sym2 ℕ) := ((Γ.V ×ˢ Γ.V).filter
    (fun p => p.1 ≠ p.2 ∧ Δ.z p.1 p.2 ≠ Γ.z p.1 p.2)).image (fun p => s(p.1, p.2))
  have hU : U ⊆ pairs Γ.V := by
    intro e he
    simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab, -⟩, rfl⟩ := he
    exact mem_pairs.2 ⟨a, b, ha, hb, hab, rfl⟩
  have hmemU : ∀ a ∈ Γ.V, ∀ b ∈ Γ.V, a ≠ b → (s(a, b) ∈ U ↔ Δ.z a b ≠ Γ.z a b) := by
    intro a ha b hb hab
    have key : Δ.z a b + Δ.z b a = Γ.z a b + Γ.z b a := by
      rw [hΔ a (hV ▸ ha) b (hV ▸ hb) hab, hmin.1.1 a ha b hb hab, ht a ha, ht b hb]
    simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hcd, hne⟩, he⟩
      rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2; subst h1 h2; exact hne
      · simp only at h1 h2; subst h1 h2
        intro h; apply hne
        linear_combination key - h
    · intro hne
      exact ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hab, hne⟩, rfl⟩
  have hiso : (Γ.flipBy U).IsIso Δ := by
    refine iso_of_agree (Γ := Γ.flipBy U) hV.symm ?_ ?_
    · intro v hv; exact ht v hv
    · intro a ha b hb hab
      show Δ.z a b = Γ.z a b + if a ≠ b ∧ s(a, b) ∈ U then 1 else 0
      by_cases h : Δ.z a b = Γ.z a b
      · rw [ite_eq_right (fun h' => (hmemU a ha b hb hab).1 h'.2 h), h, add_zero]
      · rw [ite_eq_left ⟨hab, (hmemU a ha b hb hab).2 h⟩]
        exact zmod2_eq_add_one_of_ne _ _ h
  rw [← hA.graph_dependence _ _ (flipBy_compatible hmin.1.1 U) hiso]
  exact minSeed_flipBy hA hmin U hU

/-- A contraction certificate makes the iterated difference one (tex 2200–2202).
Kind: PROVED. -/
theorem certificate_diff (hA : CoefficientRules ε A) {Γ : Config L} (hΓ : Γ.Compatible ε)
    {S : Finset (Sym2 ℕ)} (hS : IsForest Γ.V S) (h1 : A (Γ.contractBy S) = 1) :
    diff A Γ S = 1 := by
  rw [diff_eq_forest hA hΓ hS.1, ite_eq_left hS, h1]

/-- A contraction certificate makes the terminal polynomial nonzero (tex 2193–2195, 2200–2202).
Kind: PROVED. -/
theorem partitionable_terminalNonzero (hA : CoefficientRules ε A) {Γ : Config L}
    (hΓ : Γ.Compatible ε) (hP : IsPartitionable ε A Γ) : TerminalNonzero A Γ := by
  obtain ⟨-, S, hS, h1⟩ := hP
  have hd := certificate_diff hA hΓ hS h1
  unfold diff at hd
  have hne : ∑ U ∈ S.powerset, A (Γ.flipBy U) ≠ 0 := by rw [hd]; exact one_ne_zero
  obtain ⟨U, hU, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨U, (Finset.mem_powerset.1 hU).trans hS.1, zmod2_eq_one_of_ne_zero _ hne'⟩

/-- Anchors for the first `r-1` seed types and a nonempty remainder give a contraction
certificate (tex 2195–2196, 2203–2207): the anchors stay singleton clusters and the remainder is
merged by a star forest. Kind: PROVED. -/
theorem partitionable_of_anchors (hA : CoefficientRules ε A) {Γ₀ Γ : Config L}
    (hmin : IsMinSeed ε A Γ₀) (hΓ : Γ.Compatible ε) (htot : Γ.total = Γ₀.total)
    (s : ℕ) (hs : s ∈ Γ₀.V) (anc : ℕ → ℕ) (hanc : Set.InjOn anc (Γ₀.V.erase s))
    (hancV : ∀ v ∈ Γ₀.V.erase s, anc v ∈ Γ.V) (hanct : ∀ v ∈ Γ₀.V.erase s, Γ.t (anc v) = Γ₀.t v)
    (hrem : (Γ.V \ (Γ₀.V.erase s).image anc).Nonempty) : IsPartitionable ε A Γ := by
  classical
  set N := (Γ₀.V.erase s).image anc with hN
  set R := Γ.V \ N with hR
  obtain ⟨m, hm⟩ := hrem
  have hmV : m ∈ Γ.V := (Finset.mem_sdiff.1 hm).1
  have hmN : m ∉ N := (Finset.mem_sdiff.1 hm).2
  have hNV : N ⊆ Γ.V := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
    exact hancV v hv
  have hRV : R ⊆ Γ.V := Finset.sdiff_subset
  let S : Finset (Sym2 ℕ) := (R.erase m).image (fun u => s(m, u))
  let f : ℕ → ℕ := fun u => if u ∈ R then m else u
  have hconn : ∀ a b, conn S a b → (a = b ∨ (a ∈ R ∧ b ∈ R)) := by
    intro a b h
    let Q : ℕ → ℕ → Prop := fun a b => a = b ∨ (a ∈ R ∧ b ∈ R)
    have hQ : Equivalence Q := by
      refine ⟨fun a => Or.inl rfl, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩
      · rcases h with rfl | ⟨h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h2, h1⟩
      · rcases h1 with rfl | ⟨h1, h1'⟩
        · exact h2
        · rcases h2 with rfl | ⟨h2, h2'⟩
          · exact Or.inr ⟨h1, h1'⟩
          · exact Or.inr ⟨h1, h2'⟩
    refine hQ.eqvGen_iff.1 (Relation.EqvGen.mono (fun x y hxy => ?_) a b h)
    obtain ⟨u, hu, hxy'⟩ := Finset.mem_image.1 hxy
    have hu' := Finset.mem_erase.1 hu
    rcases Sym2.eq_iff.1 hxy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2; exact Or.inr ⟨hm, hu'.2⟩
    · subst h1 h2; exact Or.inr ⟨hu'.2, hm⟩
  have hconnm : ∀ a ∈ R, conn S m a := by
    intro a ha
    by_cases h : a = m
    · subst h; exact conn_refl _ _
    · exact conn_of_mem (Finset.mem_image.2 ⟨a, Finset.mem_erase.2 ⟨h, ha⟩, rfl⟩)
  have hpart : ∀ u ∈ Γ.V, ∀ u' ∈ Γ.V, rep Γ.V S u = rep Γ.V S u' ↔ f u = f u' := by
    intro u hu u' hu'
    rw [rep_eq_iff hu hu']
    constructor
    · intro h
      rcases hconn u u' h with rfl | ⟨h1, h2⟩
      · rfl
      · simp only [f, h1, h2, ite_true]
    · intro h
      by_cases h1 : u ∈ R <;> by_cases h2 : u' ∈ R
      · exact conn_trans (conn_symm (hconnm u h1)) (hconnm u' h2)
      · simp only [f, h1, h2, ite_true, ite_false] at h
        exact absurd (h ▸ hm) h2
      · simp only [f, h1, h2, ite_true, ite_false] at h
        exact absurd (h ▸ hm) h1
      · simp only [f, h1, h2, ite_false] at h
        rw [h]; exact conn_refl _ _
  -- the star is a forest
  have hSsub : S ⊆ pairs Γ.V := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
    have hu' := Finset.mem_erase.1 hu
    exact mem_pairs.2 ⟨m, u, hmV, hRV hu'.2, Ne.symm hu'.1, rfl⟩
  have hScard : S.card + 1 = R.card := by
    rw [Finset.card_image_of_injOn (fun u _ u' _ h => Sym2.congr_right.1 h)]
    exact Finset.card_erase_add_one hm
  have hfimage : Γ.V.image f = insert m N := by
    ext y
    simp only [Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨u, hu, rfl⟩
      by_cases h : u ∈ R
      · left; simp [f, h]
      · right; simp only [f, h, ite_false]
        by_contra hn; exact h (Finset.mem_sdiff.2 ⟨hu, hn⟩)
    · rintro (rfl | hy)
      · exact ⟨y, hmV, by simp [f]⟩
      · refine ⟨y, hNV hy, ?_⟩
        have : y ∉ R := fun h => (Finset.mem_sdiff.1 h).2 hy
        simp [f, this]
  have hncomp : ncomp Γ.V S = N.card + 1 := by
    unfold ncomp
    rw [card_image_eq_of_part hpart, hfimage, Finset.card_insert_of_notMem hmN]
  have hVcard : R.card + N.card = Γ.V.card := Finset.card_sdiff_add_card_eq_card hNV
  have hforest : IsForest Γ.V S := ⟨hSsub, by omega⟩
  -- the contracted graph is a copy of the seed with some bits
  have hfm : ∀ u ∈ Γ.V, f u = m ↔ u ∈ R := by
    intro u hu
    by_cases h : u ∈ R
    · simp [f, h]
    · simp only [f, h, ite_false, iff_false]
      rintro rfl; exact h hm
  have hfa : ∀ a ∈ N, ∀ u ∈ Γ.V, f u = a ↔ u = a := by
    intro a ha u hu
    have haR : a ∉ R := fun h => (Finset.mem_sdiff.1 h).2 ha
    by_cases h : u ∈ R
    · simp only [f, h, ite_true]
      constructor
      · rintro rfl; exact absurd ha hmN
      · rintro rfl; exact absurd h haR
    · simp [f, h]
  have hsumR : ∑ u ∈ R, Γ.t u = Γ₀.t s := by
    have h1 : ∑ u ∈ R, Γ.t u + ∑ u ∈ N, Γ.t u = Γ.total := Finset.sum_sdiff hNV
    have h2 : ∑ u ∈ N, Γ.t u = ∑ v ∈ Γ₀.V.erase s, Γ₀.t v := by
      rw [Finset.sum_image hanc]
      exact Finset.sum_congr rfl hanct
    have h3 : Γ₀.t s + ∑ v ∈ Γ₀.V.erase s, Γ₀.t v = Γ₀.total := Finset.add_sum_erase _ _ hs
    rw [h2, htot, ← h3] at h1
    exact add_right_cancel h1
  let φ : ℕ → ℕ := fun a => if a = s then m else anc a
  have hφmem : ∀ a ∈ Γ₀.V, φ a ∈ (ForestAux.cmap Γ f).V := by
    intro a ha
    show φ a ∈ Γ.V.image f
    rw [hfimage]
    by_cases h : a = s
    · simp [φ, h]
    · simp only [φ, h, ite_false]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨h, ha⟩))
  let Δ : Config L := ⟨Γ₀.V, Γ₀.t, fun a b => (ForestAux.cmap Γ f).z (φ a) (φ b)⟩
  let ψ : Δ.V → (ForestAux.cmap Γ f).V := fun a => ⟨φ a, hφmem a a.2⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      have hab' : φ a = φ b := congrArg Subtype.val hab
      apply Subtype.ext
      show a = b
      by_cases has : a = s <;> by_cases hbs : b = s
      · rw [has, hbs]
      · simp only [φ, has, hbs, ite_true, ite_false] at hab'
        exact absurd (hab' ▸ Finset.mem_image_of_mem anc (Finset.mem_erase.2 ⟨hbs, hb⟩)) hmN
      · simp only [φ, has, hbs, ite_true, ite_false] at hab'
        exact absurd (hab' ▸ Finset.mem_image_of_mem anc (Finset.mem_erase.2 ⟨has, ha⟩)) hmN
      · simp only [φ, has, hbs, ite_false] at hab'
        exact hanc (Finset.mem_erase.2 ⟨has, ha⟩) (Finset.mem_erase.2 ⟨hbs, hb⟩) hab'
    · rintro ⟨y, hy⟩
      have hy' : y ∈ insert m N := by rw [← hfimage]; exact hy
      rcases Finset.mem_insert.1 hy' with rfl | hyN
      · exact ⟨⟨s, hs⟩, Subtype.ext (by simp [ψ, φ])⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hyN
        have has := (Finset.mem_erase.1 ha).1
        exact ⟨⟨a, (Finset.mem_erase.1 ha).2⟩, Subtype.ext (by simp [ψ, φ, has])⟩
  have hiso : Δ.IsIso (ForestAux.cmap Γ f) := by
    refine ⟨Equiv.ofBijective ψ hψ, fun a => ?_, fun a b _ => rfl⟩
    show ∑ u ∈ Γ.V.filter (fun u => f u = φ a), Γ.t u = Γ₀.t a
    by_cases has : (a : ℕ) = s
    · rw [show φ a = m by simp [φ, has], Finset.filter_congr hfm, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hRV, hsumR, has]
    · have haN : anc a ∈ N := Finset.mem_image_of_mem anc (Finset.mem_erase.2 ⟨has, a.2⟩)
      rw [show φ a = anc a by simp [φ, has], Finset.filter_congr (hfa _ haN),
        Finset.filter_eq', ite_eq_left (hNV haN), Finset.sum_singleton]
      exact hanct a (Finset.mem_erase.2 ⟨has, a.2⟩)
  have hΔ : Δ.Compatible ε := compatible_of_iso (iso_symm hiso) (cmap_compatible hΓ f)
  have hΔ1 : A Δ = 1 := minSeed_bits_irrelevant hA hmin hΔ rfl (fun v _ => rfl)
  refine ⟨⟨m, hmV⟩, S, hforest, ?_⟩
  rw [contractBy_eq, hA.graph_dependence _ _ (cmap_compatible hΓ _) (cmap_iso hpart)]
  rw [← hΔ1]
  exact (hA.graph_dependence _ _ hΔ hiso).symm

/-- Reading a projection of the common alphabet (tex 2060–2065). -/
def Config.mapType {L' : Type*} [AddCommGroup L'] (π : L →+ L') (Γ : Config L) : Config L' :=
  { V := Γ.V, t := fun v => π (Γ.t v), z := Γ.z }

/-- A projection keeps compatibility, the sign coordinate factoring through it (tex 2060–2065).
Kind: PROVED (helper). -/
theorem ForestAux.mapType_compatible {L' : Type*} [AddCommGroup L'] {ε' : L' →+ ZMod 2}
    (π : L →+ L') (hε : ∀ x, ε' (π x) = ε x) {Γ : Config L} (hΓ : Γ.Compatible ε) :
    (Γ.mapType π).Compatible ε' := by
  intro a ha b hb hab
  show Γ.z a b + Γ.z b a = ε' (π (Γ.t a)) * ε' (π (Γ.t b))
  rw [hε, hε]
  exact hΓ a ha b hb hab

/-- Pulled-back coefficient rules: projections are additive, compatible with the sign
coordinate, preserve primary types and commute with flips and contractions (tex 2060–2065,
2102–2136). Kind: PROVED. -/
theorem CoefficientRules.mapType {L' : Type*} [AddCommGroup L'] {ε' : L' →+ ZMod 2}
    {A' : Config L' → ZMod 2} (hA : CoefficientRules ε' A') (π : L →+ L')
    (hε : ∀ x, ε' (π x) = ε x) : CoefficientRules ε (fun Γ => A' (Γ.mapType π)) := by
  refine ⟨fun Γ Δ hΓ hiso => ?_, fun Γ hΓ v hv w hw hvw => ?_, fun Γ hΓ v hv htv hn => ?_⟩
  · apply hA.graph_dependence _ _ (mapType_compatible π hε hΓ)
    obtain ⟨e, ht, hz⟩ := hiso
    exact ⟨e, fun v => congrArg π (ht v), hz⟩
  · have h1 : (Γ.flip v w).mapType π = (Γ.mapType π).flip v w := rfl
    have h2 : (Γ.contract v w).mapType π = (Γ.mapType π).contract v w := by
      refine config_ext (by rfl) ?_ (by rfl)
      funext u
      simp only [Config.mapType, Config.contract]
      by_cases huv : u = v
      · subst huv; simp [map_add]
      · simp [Function.update_of_ne huv]
    show A' (Γ.mapType π) + A' ((Γ.flip v w).mapType π) = A' ((Γ.contract v w).mapType π)
    rw [h1, h2]
    exact hA.contraction _ (mapType_compatible π hε hΓ) v hv w hw hvw
  · show A' (Γ.mapType π) = 0
    apply hA.primary_isolation _ (mapType_compatible π hε hΓ) v hv
    · show π (Γ.t v) = 0
      rw [htv, map_zero]
    · exact hn

/-- Projections commute with contraction (tex 2060–2065). Kind: PROVED (helper). -/
theorem ForestAux.contractBy_mapType {L' : Type*} [AddCommGroup L'] (π : L →+ L') (Γ : Config L)
    (S : Finset (Sym2 ℕ)) : (Γ.contractBy S).mapType π = (Γ.mapType π).contractBy S := by
  refine config_ext (by rfl) ?_ (by rfl)
  funext r
  exact map_sum π _ _

/-- One symbol on a configuration supplying, for every common label and every copy index below
`K`, a vertex of that label (tex 10598–10623): its terminal polynomial is nonzero. Kind: PROVED
(helper). -/
theorem ForestAux.terminal_of_supply {L' : Type*} [AddCommGroup L'] {ε' : L' →+ ZMod 2}
    (π : L →+ L') (hπ : Function.Surjective π) (hε : ∀ x, ε' (π x) = ε x)
    {A' : Config L' → ZMod 2} (hA' : CoefficientRules ε' A') {Γ₀ : Config L'}
    (hm : IsMinSeed ε' A' Γ₀) (ht₀ : Γ₀.total = 0) {Γ : Config L} (hΓ : Γ.Compatible ε)
    (htot : Γ.total = 0) (K : ℕ) (hK : Γ₀.V.card < K) (g : L → ℕ → ℕ)
    (hgV : ∀ ℓ j, j < K → g ℓ j ∈ Γ.V) (hgt : ∀ ℓ j, j < K → Γ.t (g ℓ j) = ℓ)
    (hginj : ∀ ℓ j ℓ' j', j < K → j' < K → g ℓ j = g ℓ' j' → j = j') :
    TerminalNonzero (fun Δ => A' (Δ.mapType π)) Γ := by
  classical
  obtain ⟨s, hs⟩ := hm.2.1
  let idx : ℕ → ℕ := fun v => (Γ₀.V.filter (· < v)).card
  have hidx : ∀ v ∈ Γ₀.V.erase s, idx v < K := fun v hv =>
    lt_trans (rank_lt (Finset.mem_of_mem_erase hv)) hK
  let anc : ℕ → ℕ := fun v => g (Function.surjInv hπ (Γ₀.t v)) (idx v)
  have hP : IsPartitionable ε' A' (Γ.mapType π) := by
    refine partitionable_of_anchors hA' hm (mapType_compatible π hε hΓ) ?_ s hs anc ?_ ?_ ?_ ?_
    · show ∑ v ∈ Γ.V, π (Γ.t v) = Γ₀.total
      rw [← map_sum]
      show π Γ.total = _
      rw [htot, map_zero, ht₀]
    · intro v hv v' hv' h
      exact rank_injOn Γ₀.V (Finset.mem_of_mem_erase hv) (Finset.mem_of_mem_erase hv')
        (hginj _ _ _ _ (hidx v hv) (hidx v' hv') h)
    · intro v hv
      exact hgV _ _ (hidx v hv)
    · intro v hv
      show π (Γ.t (g _ _)) = Γ₀.t v
      rw [hgt _ _ (hidx v hv)]
      exact Function.surjInv_eq hπ _
    · refine ⟨g 0 (K - 1), Finset.mem_sdiff.2 ⟨hgV _ _ (by omega), ?_⟩⟩
      intro hmem
      obtain ⟨v, hv, hveq⟩ := Finset.mem_image.1 hmem
      have h1 := hginj _ _ _ _ (hidx v hv) (by omega) hveq
      have h2 := rank_lt (Finset.mem_of_mem_erase hv)
      simp only [idx] at h1
      omega
  apply partitionable_terminalNonzero (hA'.mapType π hε) hΓ
  obtain ⟨hne, S, hS, h1⟩ := hP
  refine ⟨hne, S, hS, ?_⟩
  show A' ((Γ.contractBy S).mapType π) = 1
  rw [contractBy_mapType]
  exact h1

/-- Zero-total packets (App G, tex 10598–10623): an even number of copies of every common label
in each packet, one disjoint packet for every nonzero activation; at every nonzero address the
active list is nonempty, has total zero and has a contraction certificate for each projected
symbol separately. Kind: PROVED. -/
theorem packet_terminals [Fintype L] [DecidableEq L] (hL : ∀ x : L, x + x = 0)
    {L₁ L₂ : Type*} [AddCommGroup L₁] [AddCommGroup L₂] {ε₁ : L₁ →+ ZMod 2} {ε₂ : L₂ →+ ZMod 2}
    (π₁ : L →+ L₁) (π₂ : L →+ L₂) (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂)
    (hε₁ : ∀ x, ε₁ (π₁ x) = ε x) (hε₂ : ∀ x, ε₂ (π₂ x) = ε x)
    {A₁ : Config L₁ → ZMod 2} {A₂ : Config L₂ → ZMod 2}
    (hA₁ : CoefficientRules ε₁ A₁) (hA₂ : CoefficientRules ε₂ A₂)
    {Γ₁ : Config L₁} {Γ₂ : Config L₂} (hm₁ : IsMinSeed ε₁ A₁ Γ₁) (hm₂ : IsMinSeed ε₂ A₂ Γ₂)
    (ht₁ : Γ₁.total = 0) (ht₂ : Γ₂.total = 0) (b : ℕ) (hb : 1 ≤ b) :
    ∃ (V : Finset ℕ) (t : ℕ → L) (act' : ℕ → Option (Fin b → ZMod 2)),
      (∀ v ∈ V, ∃ w, w ≠ 0 ∧ act' v = some w) ∧ (∀ w, w ≠ 0 → ∃ v ∈ V, act' v = some w) ∧
      ∀ z : ℕ → ℕ → ZMod 2, (Config.mk V t z).Compatible ε → ∀ x : Fin b → ZMod 2, x ≠ 0 →
        ((Config.mk V t z).at act' x).V.Nonempty ∧ ((Config.mk V t z).at act' x).total = 0 ∧
        TerminalNonzero (fun Δ => A₁ (Δ.mapType π₁)) ((Config.mk V t z).at act' x) ∧
        TerminalNonzero (fun Δ => A₂ (Δ.mapType π₂)) ((Config.mk V t z).at act' x) := by
  classical
  -- the hypothesis `1 ≤ b` is not needed: a nonzero address already has a nonzero coordinate
  have _ : 1 ≤ b := hb
  set M := 2 * (Γ₁.V.card + Γ₂.V.card + 1) with hM
  have hMpos : 0 < M := by omega
  let I := (Fin b → ZMod 2) × L × Fin M
  let enc : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let num : I → ℕ := fun i => (enc i : ℕ)
  have hnum : Function.Injective num := fun i j h => enc.injective (Fin.ext h)
  let t : ℕ → L := fun n => if h : n < Fintype.card I then (enc.symm ⟨n, h⟩).2.1 else 0
  let act' : ℕ → Option (Fin b → ZMod 2) := fun n =>
    if h : n < Fintype.card I then some (enc.symm ⟨n, h⟩).1 else none
  have ht_num : ∀ i, t (num i) = i.2.1 := by
    intro i
    simp [t, num]
  have hact_num : ∀ i, act' (num i) = some i.1 := by
    intro i
    simp [act', num]
  let V : Finset ℕ := (Finset.univ.filter (fun i : I => i.1 ≠ 0)).image num
  refine ⟨V, t, act', ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨i.1, (Finset.mem_filter.1 hi).2, hact_num i⟩
  · intro w hw
    exact ⟨num (w, 0, ⟨0, hMpos⟩),
      Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩, rfl⟩, hact_num _⟩
  · intro z hz x hx
    have hpres : ∀ i : I, present act' x (num i) ↔ (∑ k, i.1 k * x k) = 1 := by
      intro i
      simp only [present, hact_num i]
    let F := Finset.univ.filter (fun i : I => i.1 ≠ 0 ∧ (∑ k, i.1 k * x k) = 1)
    have hVx : ((Config.mk V t z).at act' x).V = F.image num := by
      show V.filter (present act' x) = F.image num
      ext n
      simp only [Finset.mem_filter, Finset.mem_image, V, F, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, hp⟩
        exact ⟨i, ⟨hi, (hpres i).1 hp⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hp⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, (hpres i).2 hp⟩
    obtain ⟨k₀, hk₀⟩ : ∃ k, x k ≠ 0 := Function.ne_iff.1 hx
    let w₀ : Fin b → ZMod 2 := Pi.single k₀ 1
    have hw₀ : w₀ ≠ 0 := by
      intro h
      have := congrFun h k₀
      simp [w₀] at this
    have hw₀x : (∑ k, w₀ k * x k) = 1 := by
      simp only [w₀, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact ForestAux.zmod2_eq_one_of_ne_zero _ hk₀
    have hmemF : ∀ ℓ j, num (w₀, ℓ, j) ∈ ((Config.mk V t z).at act' x).V := by
      intro ℓ j
      rw [hVx]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw₀, hw₀x⟩)
    have hcompat : ((Config.mk V t z).at act' x).Compatible ε := by
      intro a ha c hc hac
      exact hz a (Finset.mem_filter.1 ha).1 c (Finset.mem_filter.1 hc).1 hac
    have hsumL : ∑ p : L × Fin M, p.1 = 0 := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      apply Finset.sum_eq_zero
      intro ℓ _
      rw [hM, two_mul, add_nsmul, ← nsmul_add, hL, nsmul_zero]
    have htot : ((Config.mk V t z).at act' x).total = 0 := by
      show ∑ n ∈ ((Config.mk V t z).at act' x).V, t n = 0
      rw [hVx, Finset.sum_image (fun i _ j _ h => hnum h)]
      simp only [ht_num]
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro w _
      by_cases hw : w ≠ 0 ∧ (∑ k, w k * x k) = 1
      · simp only [hw, ne_eq, not_false_eq_true, and_self, ite_true]
        exact hsumL
      · simp only [hw, ite_false, Finset.sum_const_zero]
    have hK₁ : Γ₁.V.card < M := by omega
    have hK₂ : Γ₂.V.card < M := by omega
    let g : L → ℕ → ℕ := fun ℓ j => num (w₀, ℓ, ⟨j % M, Nat.mod_lt _ hMpos⟩)
    have hgV : ∀ ℓ j, j < M → g ℓ j ∈ ((Config.mk V t z).at act' x).V :=
      fun ℓ j _ => hmemF _ _
    have hgt : ∀ ℓ j, j < M → ((Config.mk V t z).at act' x).t (g ℓ j) = ℓ :=
      fun ℓ j _ => ht_num _
    have hginj : ∀ ℓ j ℓ' j', j < M → j' < M → g ℓ j = g ℓ' j' → j = j' := by
      intro ℓ j ℓ' j' hj hj' h
      have h' := congrArg (fun i : I => (i.2.2 : ℕ)) (hnum h)
      simp only [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h'
      exact h'
    exact ⟨⟨_, hmemF 0 ⟨0, hMpos⟩⟩, htot,
      ForestAux.terminal_of_supply π₁ hπ₁ hε₁ hA₁ hm₁ ht₁ hcompat htot M hK₁ g hgV hgt hginj,
      ForestAux.terminal_of_supply π₂ hπ₂ hε₂ hA₂ hm₂ ht₂ hcompat htot M hK₂ g hgV hgt hginj⟩

end ZInQ.Manuscript.RC.Symbols
