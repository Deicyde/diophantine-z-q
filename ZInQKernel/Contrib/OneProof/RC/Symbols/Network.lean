import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
import ZInQKernel.Contrib.OneProof.RC.Symbols.Act
import ZInQKernel.Contrib.OneProof.RC.Symbols.Forest

/-!
# Lane RC2: network operators (tex 10625–10655)

Manuscript paragraph "Network operators and their degree" (tex 10625–10655), with the network
operator of `Core` (rooted forests, tex 2635–2655).

* `netOp_expansion`: a network of primary auxiliary vertices acts on a symbol by its operator.
  Expand in the bits incident to the auxiliary vertices (Möbius expansion over the present
  auxiliary edges), contract the chosen forest (forest product); a component with no terminal
  is an isolated primary vertex and vanishes by primary isolation; a rooted forest gives the
  forest difference of its induced terminal partition (the star forest).
* `netOp_expansion_multi`: networks with no edges between their auxiliary vertices act by the
  product of their operators (induction on the networks, with the action multiplicative).
* `netOp_constantCoeff`, `netOp_coeff_X`: the degree-zero and degree-one coefficients count
  rooted forests by their terminal partition.

The expansion is first proved relative to the forest product (`ForestProduct`, the statement
of `diff_eq_forest`), then specialized with `diff_eq_forest`.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

variable {L : Type*} [AddCommGroup L]

namespace NetworkProof

/-! ### Connectivity and block representatives -/

/-- Connectivity is reflexive. Helper for tex 10635–10650. Kind: PROVED. -/
theorem conn_refl (S : Finset (Sym2 ℕ)) (a : ℕ) : conn S a a := Relation.EqvGen.refl a

/-- Connectivity is symmetric. Helper for tex 10635–10650. Kind: PROVED. -/
theorem conn_symm {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : conn S a b) : conn S b a :=
  Relation.EqvGen.symm _ _ h

/-- Connectivity is transitive. Helper for tex 10635–10650. Kind: PROVED. -/
theorem conn_trans {S : Finset (Sym2 ℕ)} {a b c : ℕ} (h₁ : conn S a b) (h₂ : conn S b c) :
    conn S a c :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

/-- An edge connects its ends. Helper for tex 10635–10650. Kind: PROVED. -/
theorem conn_of_mem {S : Finset (Sym2 ℕ)} {a b : ℕ} (h : s(a, b) ∈ S) : conn S a b :=
  Relation.EqvGen.rel _ _ h

/-- Membership of a pair in `pairs V`. Helper for tex 10635–10650. Kind: PROVED. -/
theorem mk_mem_pairs {V : Finset ℕ} {a b : ℕ} : s(a, b) ∈ pairs V ↔ a ∈ V ∧ b ∈ V ∧ a ≠ b := by
  unfold pairs
  constructor
  · intro h
    obtain ⟨p, hp, hpe⟩ := mem_image.1 h
    obtain ⟨hpV, hpne⟩ := mem_filter.1 hp
    obtain ⟨h1, h2⟩ := mem_product.1 hpV
    rcases Sym2.eq_iff.1 hpe with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · subst e1; subst e2; exact ⟨h1, h2, hpne⟩
    · subst e1; subst e2; exact ⟨h2, h1, fun h => hpne h.symm⟩
  · rintro ⟨ha, hb, hab⟩
    exact mem_image.2 ⟨(a, b), mem_filter.2 ⟨mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩

/-- `pairs` is monotone. Helper for tex 10651–10655. Kind: PROVED. -/
theorem pairs_mono {V W : Finset ℕ} (h : V ⊆ W) : pairs V ⊆ pairs W := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.1 he
    exact mk_mem_pairs.2 ⟨h ha, h hb, hab⟩

/-- Off the vertex set, connectivity is trivial. -/
theorem conn_cases {V : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs V) {x y : ℕ}
    (h : conn S x y) : x = y ∨ (x ∈ V ∧ y ∈ V) := by
  induction h with
  | rel a b hab =>
    obtain ⟨ha, hb, _⟩ := mk_mem_pairs.1 (hS hab)
    exact Or.inr ⟨ha, hb⟩
  | refl a => exact Or.inl rfl
  | symm a b _ ih =>
    rcases ih with h | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h2, h1⟩
  | trans a b c _ _ ih₁ ih₂ =>
    rcases ih₁ with h | ⟨h1, h2⟩
    · subst h; exact ih₂
    · rcases ih₂ with h' | ⟨h1', h2'⟩
      · subst h'; exact Or.inr ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2'⟩

/-- A vertex outside `V` is connected only to itself. Helper for tex 10635–10655. Kind: PROVED. -/
theorem conn_eq_of_not_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs V) {x y : ℕ}
    (h : conn S x y) (hx : x ∉ V) : x = y := by
  rcases conn_cases hS h with h | ⟨h1, _⟩
  · exact h
  · exact absurd h1 hx

open Classical in
/-- The block representative is the least vertex of `V` connected to `v`. Helper for tex 10635–10650. Kind: PROVED. -/
theorem rep_spec {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (h : ∃ a ∈ V, conn S a v) :
    rep V S v ∈ V ∧ conn S (rep V S v) v ∧ ∀ u ∈ V, conn S u v → rep V S v ≤ u := by
  obtain ⟨a, ha, hav⟩ := h
  unfold rep
  split
  · next hne =>
    exact ⟨(mem_filter.1 (min'_mem _ hne)).1, (mem_filter.1 (min'_mem _ hne)).2,
      fun u hu huv => min'_le _ _ (mem_filter.2 ⟨hu, huv⟩)⟩
  · next hne => exact absurd ⟨a, mem_filter.2 ⟨ha, hav⟩⟩ hne

open Classical in
/-- With no vertex of `V` connected, the representative is the vertex itself. Helper for tex 10635–10650. Kind: PROVED. -/
theorem rep_of_not {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (h : ¬ ∃ a ∈ V, conn S a v) :
    rep V S v = v := by
  unfold rep
  split
  · next hne =>
    obtain ⟨a, ha⟩ := hne
    exact absurd ⟨a, (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩ h
  · rfl

/-- The representative lies in `V`. Helper for tex 10635–10650. Kind: PROVED. -/
theorem rep_mem {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (h : ∃ a ∈ V, conn S a v) :
    rep V S v ∈ V := (rep_spec h).1

/-- The representative is connected to the vertex. Helper for tex 10635–10650. Kind: PROVED. -/
theorem conn_rep {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (h : ∃ a ∈ V, conn S a v) :
    conn S (rep V S v) v := (rep_spec h).2.1

/-- The representative is minimal. Helper for tex 10635–10650. Kind: PROVED. -/
theorem rep_le {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u v : ℕ} (hu : u ∈ V) (h : conn S u v) :
    rep V S v ≤ u := (rep_spec ⟨u, hu, h⟩).2.2 u hu h

/-- Connected vertices have the same representative. Helper for tex 10635–10650. Kind: PROVED. -/
theorem rep_eq_of_conn {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u v : ℕ} (h : conn S u v)
    (hu : ∃ a ∈ V, conn S a u) : rep V S u = rep V S v := by
  have hv : ∃ a ∈ V, conn S a v := by
    obtain ⟨a, ha, hau⟩ := hu
    exact ⟨a, ha, conn_trans hau h⟩
  apply le_antisymm
  · exact rep_le (rep_mem hv) (conn_trans (conn_rep hv) (conn_symm h))
  · exact rep_le (rep_mem hu) (conn_trans (conn_rep hu) h)

/-- Equal representatives means connected. Helper for tex 10635–10650. Kind: PROVED. -/
theorem rep_eq_iff {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {u v : ℕ} (hu : ∃ a ∈ V, conn S a u)
    (hv : ∃ a ∈ V, conn S a v) : rep V S u = rep V S v ↔ conn S u v := by
  constructor
  · intro h
    have h1 := conn_rep hu
    have h2 := conn_rep hv
    rw [h] at h1
    exact conn_trans (conn_symm h1) h2
  · intro h
    exact rep_eq_of_conn h hu

/-- The representative of a representative is itself. Helper for tex 10635–10650. Kind: PROVED. -/
theorem rep_rep {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (h : ∃ a ∈ V, conn S a v) :
    rep V S (rep V S v) = rep V S v :=
  rep_eq_of_conn (conn_rep h) ⟨rep V S v, rep_mem h, conn_refl _ _⟩

/-- A vertex of `V` is connected to a vertex of `V`. Helper for tex 10635–10650. Kind: PROVED. -/
theorem self_conn {V : Finset ℕ} {S : Finset (Sym2 ℕ)} {v : ℕ} (hv : v ∈ V) :
    ∃ a ∈ V, conn S a v := ⟨v, hv, conn_refl _ _⟩

/-! ### Quotient by a block map -/

/-- Quotient of a configuration by a block map `ρ` (summed types and incidences). -/
noncomputable def bq (Γ : Config L) (ρ : ℕ → ℕ) : Config L where
  V := Γ.V.image ρ
  t := fun r => ∑ u ∈ Γ.V.filter (fun u => ρ u = r), Γ.t u
  z := fun r r' => ∑ u ∈ Γ.V.filter (fun u => ρ u = r),
    ∑ u' ∈ Γ.V.filter (fun u' => ρ u' = r'), Γ.z u u'

/-- Contraction by `S` is the quotient by the representative map. Helper for tex 10637–10640. Kind: PROVED. -/
theorem contractBy_eq_bq (Γ : Config L) (S : Finset (Sym2 ℕ)) :
    Γ.contractBy S = bq Γ (rep Γ.V S) := rfl

/-- The quotient only reads the block map on the vertex set. Helper for tex 10637–10640. Kind: PROVED. -/
theorem bq_congr {Γ : Config L} {ρ σ : ℕ → ℕ} (h : ∀ u ∈ Γ.V, ρ u = σ u) : bq Γ ρ = bq Γ σ := by
  have hf : ∀ r, Γ.V.filter (fun u => ρ u = r) = Γ.V.filter (fun u => σ u = r) := fun r =>
    filter_congr (fun u hu => by rw [h u hu])
  simp only [bq, Config.mk.injEq]
  refine ⟨image_congr (fun u hu => h u hu), funext fun r => by rw [hf r],
    funext fun r => funext fun r' => by rw [hf r, hf r']⟩

omit [AddCommGroup L] in
/-- Configurations agreeing on their vertex data are isomorphic. Helper for tex 10637–10640. Kind: PROVED. -/
theorem isIso_of_agree {Γ Δ : Config L} (hV : Γ.V = Δ.V) (ht : ∀ v ∈ Γ.V, Γ.t v = Δ.t v)
    (hz : ∀ v ∈ Γ.V, ∀ w ∈ Γ.V, v ≠ w → Γ.z v w = Δ.z v w) : Γ.IsIso Δ := by
  refine ⟨Equiv.subtypeEquivRight (fun x => by rw [hV]), fun v => (ht v v.2).symm,
    fun v w hvw => (hz v v.2 w w.2 (fun h => hvw (Subtype.ext h))).symm⟩

/-- A quotient of a compatible configuration is compatible (blocks are disjoint, the sign coordinate is additive; tex 2037–2054). Helper. Kind: PROVED. -/
theorem bq_compatible {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε) (ρ : ℕ → ℕ) :
    (bq Γ ρ).Compatible ε := by
  intro r hr r' hr' hne
  simp only [bq]
  rw [sum_comm (s := Γ.V.filter (fun u => ρ u = r')), ← sum_add_distrib, map_sum, map_sum,
    sum_mul_sum]
  refine sum_congr rfl (fun u hu => ?_)
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun u' hu' => ?_)
  obtain ⟨huV, hur⟩ := mem_filter.1 hu
  obtain ⟨hu'V, hu'r⟩ := mem_filter.1 hu'
  refine hΓ u huV u' hu'V (fun h => hne ?_)
  rw [← hur, ← hu'r, h]

/-- Quotients by block maps inducing the same partition are isomorphic. Helper for tex 10637–10640. Kind: PROVED. -/
theorem bq_isIso {Γ : Config L} {ρ σ : ℕ → ℕ}
    (h : ∀ u ∈ Γ.V, ∀ v ∈ Γ.V, ρ u = ρ v ↔ σ u = σ v) : (bq Γ ρ).IsIso (bq Γ σ) := by
  classical
  -- choose a preimage of every block value
  have hpre : ∀ r ∈ Γ.V.image ρ, ∃ u ∈ Γ.V, ρ u = r := fun r hr => by
    simpa using hr
  let c : (Γ.V.image ρ) → ℕ := fun r => Classical.choose (hpre r.1 r.2)
  have hc : ∀ r, c r ∈ Γ.V ∧ ρ (c r) = r.1 := fun r => Classical.choose_spec (hpre r.1 r.2)
  let f : (Γ.V.image ρ) → (Γ.V.image σ) := fun r => ⟨σ (c r), mem_image_of_mem σ (hc r).1⟩
  have hfinj : Function.Injective f := by
    intro r₁ r₂ hr
    have h' : σ (c r₁) = σ (c r₂) := congrArg Subtype.val hr
    apply Subtype.ext
    rw [← (hc r₁).2, ← (hc r₂).2]
    exact (h _ (hc r₁).1 _ (hc r₂).1).2 h'
  have hfsurj : Function.Surjective f := by
    rintro ⟨s, hs⟩
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hs
    refine ⟨⟨ρ u, mem_image_of_mem ρ hu⟩, Subtype.ext ?_⟩
    show σ (c ⟨ρ u, _⟩) = σ u
    exact (h _ (hc _).1 _ hu).1 (hc _).2
  refine ⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩, fun r => ?_, fun r r' _ => ?_⟩
  · show ∑ u ∈ Γ.V.filter (fun u => σ u = σ (c r)), Γ.t u =
      ∑ u ∈ Γ.V.filter (fun u => ρ u = r.1), Γ.t u
    refine sum_congr (filter_congr (fun u hu => ?_)) (fun _ _ => rfl)
    rw [← (hc r).2]
    exact (h u hu _ (hc r).1).symm
  · show ∑ u ∈ Γ.V.filter (fun u => σ u = σ (c r)),
        ∑ u' ∈ Γ.V.filter (fun u' => σ u' = σ (c r')), Γ.z u u' =
      ∑ u ∈ Γ.V.filter (fun u => ρ u = r.1), ∑ u' ∈ Γ.V.filter (fun u' => ρ u' = r'.1), Γ.z u u'
    have e1 : Γ.V.filter (fun u => σ u = σ (c r)) = Γ.V.filter (fun u => ρ u = r.1) :=
      filter_congr (fun u hu => by rw [← (hc r).2]; exact (h u hu _ (hc r).1).symm)
    have e2 : Γ.V.filter (fun u => σ u = σ (c r')) = Γ.V.filter (fun u => ρ u = r'.1) :=
      filter_congr (fun u hu => by rw [← (hc r').2]; exact (h u hu _ (hc r').1).symm)
    rw [e1, e2]

/-! ### Möbius expansion over a powerset -/

/-- Möbius expansion over a powerset in characteristic two: summing the differences over all subsets recovers the value at the top. Helper for tex 10635–10637 ("expand in the bits"). Kind: PROVED. -/
theorem sum_powerset_sum_powerset {α : Type*} [DecidableEq α] (N : Finset α) :
    ∀ g : Finset α → ZMod 2, ∑ S ∈ N.powerset, ∑ U ∈ S.powerset, g U = g N := by
  induction N using Finset.induction_on with
  | empty => intro g; simp
  | insert e N he ih =>
    intro g
    rw [sum_powerset_insert he]
    have h2 : ∀ S ∈ N.powerset, ∑ U ∈ (insert e S).powerset, g U =
        ∑ U ∈ S.powerset, g U + ∑ U ∈ S.powerset, g (insert e U) := by
      intro S hS
      have heS : e ∉ S := fun h => he (mem_powerset.1 hS h)
      rw [sum_powerset_insert heS]
    rw [sum_congr rfl h2, sum_add_distrib, ← add_assoc, zmod2_add_self, zero_add]
    exact ih (fun U => g (insert e U))

/-! ### Star forest of the induced terminal partition -/

open Classical in
/-- Membership in the star forest. Helper for tex 10637–10640. Kind: PROVED. -/
theorem mem_starForest {T : Finset ℕ} {S : Finset (Sym2 ℕ)} {e : Sym2 ℕ} :
    e ∈ starForest T S ↔ ∃ a ∈ T, rep T S a ≠ a ∧ s(rep T S a, a) = e := by
  unfold starForest
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := mem_image.1 h
    exact ⟨a, (mem_filter.1 ha).1, (mem_filter.1 ha).2, rfl⟩
  · rintro ⟨a, ha, hne, rfl⟩
    exact mem_image.2 ⟨a, mem_filter.2 ⟨ha, hne⟩, rfl⟩

/-- The star forest consists of terminal pairs. Helper for tex 10637–10640. Kind: PROVED. -/
theorem starForest_subset_pairs (T : Finset ℕ) (S : Finset (Sym2 ℕ)) :
    starForest T S ⊆ pairs T := by
  intro e he
  obtain ⟨a, ha, hne, rfl⟩ := mem_starForest.1 he
  exact mk_mem_pairs.2 ⟨rep_mem (self_conn ha), ha, hne⟩

/-- Star-forest connectivity implies connectivity through `S`. Helper for tex 10637–10640. Kind: PROVED. -/
theorem conn_of_conn_starForest {T : Finset ℕ} {S : Finset (Sym2 ℕ)} {x y : ℕ}
    (h : conn (starForest T S) x y) : conn S x y := by
  induction h with
  | rel a b hab =>
    obtain ⟨c, hc, _, hce⟩ := mem_starForest.1 hab
    have hcr : conn S (rep T S c) c := conn_rep (self_conn hc)
    rcases Sym2.eq_iff.1 hce with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hcr
    · rw [← h1, ← h2]; exact conn_symm hcr
  | refl a => exact conn_refl _ _
  | symm a b _ ih => exact conn_symm ih
  | trans a b c _ _ ih₁ ih₂ => exact conn_trans ih₁ ih₂

/-- A terminal is star-connected to its representative. Helper for tex 10637–10640. Kind: PROVED. -/
theorem conn_starForest_rep {T : Finset ℕ} {S : Finset (Sym2 ℕ)} {a : ℕ} (ha : a ∈ T) :
    conn (starForest T S) (rep T S a) a := by
  by_cases h : rep T S a = a
  · rw [h]; exact conn_refl _ _
  · exact conn_of_mem (mem_starForest.2 ⟨a, ha, h, rfl⟩)

/-- The star forest induces the same terminal representatives as `S`. Helper for tex 10637–10640. Kind: PROVED. -/
theorem rep_starForest {T : Finset ℕ} {S : Finset (Sym2 ℕ)} {a : ℕ} (ha : a ∈ T) :
    rep T (starForest T S) a = rep T S a := by
  apply le_antisymm
  · exact rep_le (rep_mem (self_conn ha)) (conn_starForest_rep ha)
  · have hm : rep T (starForest T S) a ∈ T := rep_mem (self_conn ha)
    exact rep_le hm (conn_of_conn_starForest (conn_rep (self_conn ha)))

open Classical in
/-- The representatives are the fixed points of `rep`. Helper for tex 10637–10640. Kind: PROVED. -/
theorem image_rep_eq_filter (T : Finset ℕ) (S : Finset (Sym2 ℕ)) :
    T.image (rep T S) = T.filter (fun a => rep T S a = a) := by
  ext r
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rep_mem (self_conn ha), rep_rep (self_conn ha)⟩
  · rintro ⟨hr, hrr⟩
    exact ⟨r, hr, hrr⟩

open Classical in
/-- The star forest has one edge per non-representative terminal. Helper for tex 10637–10640. Kind: PROVED. -/
theorem card_starForest (T : Finset ℕ) (S : Finset (Sym2 ℕ)) :
    (starForest T S).card = (T.filter (fun a => rep T S a ≠ a)).card := by
  unfold starForest
  apply card_image_of_injOn
  intro a ha b hb hab
  have ha' := mem_filter.1 (mem_coe.1 ha)
  simp only at hab
  rcases Sym2.eq_iff.1 hab with ⟨_, h⟩ | ⟨h1, h2⟩
  · exact h
  · rw [h2, ← h1]
    rw [rep_rep (self_conn ha'.1)]


open Classical in
/-- The star forest is a forest on the terminals. Helper for tex 10637–10640 ("their forest difference"). Kind: PROVED. -/
theorem isForest_starForest (T : Finset ℕ) (S : Finset (Sym2 ℕ)) :
    IsForest T (starForest T S) := by
  refine ⟨starForest_subset_pairs T S, ?_⟩
  unfold ncomp
  rw [image_congr (fun a ha => rep_starForest (S := S) (mem_coe.1 ha)), image_rep_eq_filter,
    card_starForest, add_comm]
  exact card_filter_add_card_filter_not _

/-! ### Zeroing the auxiliary bits -/

/-- `Γ` with every auxiliary-incident bit set to zero. -/
def zeroAux (Γ : Config L) (X : Finset ℕ) : Config L where
  V := Γ.V
  t := Γ.t
  z := fun a b => if a ∈ X ∨ b ∈ X then 0 else Γ.z a b

/-- Zeroing the auxiliary-incident bits keeps compatibility (auxiliary vertices are primary). Helper for tex 10635–10637. Kind: PROVED. -/
theorem zeroAux_compatible {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε)
    {X : Finset ℕ} (hX : ∀ x ∈ X, Γ.t x = 0) : (zeroAux Γ X).Compatible ε := by
  intro v hv w hw hne
  show (if v ∈ X ∨ w ∈ X then 0 else Γ.z v w) + (if w ∈ X ∨ v ∈ X then 0 else Γ.z w v) =
    ε (Γ.t v) * ε (Γ.t w)
  by_cases h : v ∈ X ∨ w ∈ X
  · rw [ite_eq_left h, ite_eq_left h.symm, add_zero]
    rcases h with h | h
    · rw [hX v h, map_zero, zero_mul]
    · rw [hX w h, map_zero, mul_zero]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]
    exact hΓ v hv w hw hne

/-- Restriction keeps compatibility. Helper for tex 10635–10655. Kind: PROVED. -/
theorem restrict_compatible {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε)
    {W : Finset ℕ} (hW : W ⊆ Γ.V) : (Γ.restrict W).Compatible ε :=
  fun v hv w hw hne => hΓ v (hW hv) w (hW hw) hne

/-- Flipping pair bits keeps compatibility. Helper for tex 10651–10655. Kind: PROVED. -/
theorem flipBy_compatible {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε)
    (U : Finset (Sym2 ℕ)) : (Γ.flipBy U).Compatible ε := by
  intro v hv w hw hne
  show Γ.z v w + (if v ≠ w ∧ s(v, w) ∈ U then 1 else 0) +
    (Γ.z w v + (if w ≠ v ∧ s(w, v) ∈ U then 1 else 0)) = ε (Γ.t v) * ε (Γ.t w)
  have hsw : (if w ≠ v ∧ s(w, v) ∈ U then (1 : ZMod 2) else 0) =
      if v ≠ w ∧ s(v, w) ∈ U then 1 else 0 := by
    rw [Sym2.eq_swap]
    exact if_congr ⟨fun h => ⟨fun e => h.1 e.symm, h.2⟩, fun h => ⟨fun e => h.1 e.symm, h.2⟩⟩
      rfl rfl
  rw [hsw, ← hΓ v hv w hw hne]
  have key : ∀ a b c : ZMod 2, a + c + (b + c) = a + b := by decide
  exact key _ _ _

omit [AddCommGroup L] in
/-- Membership of a pair in the network edges. Helper for tex 10635–10637. Kind: PROVED. -/
theorem mk_mem_netEdges {Γ : Config L} {T X : Finset ℕ} {v w : ℕ} :
    s(v, w) ∈ netEdges Γ T X ↔ v ≠ w ∧
      ((v ∈ X ∧ w ∈ T ∪ X ∧ Γ.z v w = 1) ∨ (w ∈ X ∧ v ∈ T ∪ X ∧ Γ.z w v = 1)) := by
  unfold netEdges
  constructor
  · intro h
    obtain ⟨p, hp, hpe⟩ := mem_image.1 h
    obtain ⟨hpX, hne, hz⟩ := mem_filter.1 hp
    obtain ⟨h1, h2⟩ := mem_product.1 hpX
    rcases Sym2.eq_iff.1 hpe with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · subst e1; subst e2; exact ⟨hne, Or.inl ⟨h1, h2, hz⟩⟩
    · subst e1; subst e2; exact ⟨fun h => hne h.symm, Or.inr ⟨h1, h2, hz⟩⟩
  · rintro ⟨hne, ⟨h1, h2, hz⟩ | ⟨h1, h2, hz⟩⟩
    · exact mem_image.2 ⟨(v, w), mem_filter.2 ⟨mem_product.2 ⟨h1, h2⟩, hne, hz⟩, rfl⟩
    · exact mem_image.2 ⟨(w, v), mem_filter.2 ⟨mem_product.2 ⟨h1, h2⟩, fun h => hne h.symm, hz⟩,
        Sym2.eq_swap⟩

omit [AddCommGroup L] in
/-- Network edges are pairs of network vertices. Helper for tex 10635–10637. Kind: PROVED. -/
theorem netEdges_subset_pairs {Γ : Config L} {T X : Finset ℕ} :
    netEdges Γ T X ⊆ pairs (T ∪ X) := by
  intro e he
  induction e using Sym2.ind with
  | _ v w =>
    obtain ⟨hne, ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩⟩ := mk_mem_netEdges.1 he
    · exact mk_mem_pairs.2 ⟨mem_union_right T h1, h2, hne⟩
    · exact mk_mem_pairs.2 ⟨h2, mem_union_right T h1, hne⟩

/-- Auxiliary-incident bits are symmetric (reciprocity with a primary vertex). Helper for tex 10635–10637. Kind: PROVED. -/
theorem aux_bit_symm {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε) {X : Finset ℕ}
    (hX : ∀ x ∈ X, Γ.t x = 0) {v w : ℕ} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) (hne : v ≠ w)
    (h : v ∈ X ∨ w ∈ X) : Γ.z v w = Γ.z w v := by
  have h0 : Γ.z v w + Γ.z w v = 0 := by
    rw [hΓ v hv w hw hne]
    rcases h with h | h
    · rw [hX v h, map_zero, zero_mul]
    · rw [hX w h, map_zero, mul_zero]
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact key _ _ h0

/-- Flipping exactly the present auxiliary edges turns the zeroed configuration back into
`Γ` (tex 10635–10637). Kind: PROVED. -/
theorem flip_zeroAux_iso {ε : L →+ ZMod 2} {Γ : Config L} (hΓ : Γ.Compatible ε)
    {T X : Finset ℕ} (hV : Γ.V = T ∪ X) (hX : ∀ x ∈ X, Γ.t x = 0) :
    Γ.IsIso ((zeroAux Γ X).flipBy (netEdges Γ T X)) := by
  refine isIso_of_agree rfl (fun _ _ => rfl) (fun v hv w hw hvw => ?_)
  show Γ.z v w = (if v ∈ X ∨ w ∈ X then 0 else Γ.z v w) +
    (if v ≠ w ∧ s(v, w) ∈ netEdges Γ T X then 1 else 0)
  have hv' : v ∈ T ∪ X := hV ▸ hv
  have hw' : w ∈ T ∪ X := hV ▸ hw
  by_cases hx : v ∈ X ∨ w ∈ X
  · have hsym := aux_bit_symm hΓ hX hv hw hvw hx
    have hmem : s(v, w) ∈ netEdges Γ T X ↔ Γ.z v w = 1 := by
      rw [mk_mem_netEdges]
      constructor
      · rintro ⟨_, ⟨_, _, h⟩ | ⟨_, _, h⟩⟩
        · exact h
        · rw [hsym]; exact h
      · intro h
        refine ⟨hvw, ?_⟩
        rcases hx with hx | hx
        · exact Or.inl ⟨hx, hw', h⟩
        · exact Or.inr ⟨hx, hv', by rw [← hsym]; exact h⟩
    rw [ite_eq_left hx, zero_add]
    by_cases h1 : Γ.z v w = 1
    · rw [ite_eq_left ⟨hvw, hmem.2 h1⟩, h1]
    · rw [ite_eq_right (fun h => h1 (hmem.1 h.2))]
      have key : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
      exact key _ h1
  · have hnot : s(v, w) ∉ netEdges Γ T X := by
      rw [mk_mem_netEdges]
      rintro ⟨_, ⟨h, _⟩ | ⟨h, _⟩⟩
      · exact hx (Or.inl h)
      · exact hx (Or.inr h)
    rw [ite_eq_right hx, ite_eq_right (fun h => hnot h.2), add_zero]

/-- Auxiliary vertices contribute nothing to a block sum that vanishes on them. Helper for tex 10637–10640. Kind: PROVED. -/
theorem sum_filter_aux {M : Type*} [AddCommMonoid M] {T X V : Finset ℕ} (hV : V = T ∪ X)
    (P : ℕ → Prop) [DecidablePred P] (g : ℕ → M) (hg : ∀ x ∈ X, x ∉ T → g x = 0) :
    ∑ u ∈ V.filter P, g u = ∑ u ∈ T.filter P, g u := by
  symm
  apply sum_subset (filter_subset_filter _ (hV ▸ subset_union_left))
  intro u hu hnot
  have huV := (mem_filter.1 hu).1
  have huT : u ∉ T := fun h => hnot (mem_filter.2 ⟨h, (mem_filter.1 hu).2⟩)
  rw [hV] at huV
  exact hg u ((mem_union.1 huV).resolve_left huT) huT


end NetworkProof

open Classical in
/-- The forest product (the statement of `diff_eq_forest`, tex 2200–2202, 10627–10633) as a
property of a symbol: iterated differences along a forest give the contracted symbol, a
non-forest gives zero. -/
def ForestProduct (ε : L →+ ZMod 2) (A : Config L → ZMod 2) : Prop :=
  ∀ Γ : Config L, Γ.Compatible ε → ∀ S ⊆ pairs Γ.V,
    diff A Γ S = if IsForest Γ.V S then A (Γ.contractBy S) else 0

namespace NetworkProof

open NetworkProof

/-- A rooted forest: contracting it in the zeroed configuration gives the forest difference of
the induced terminal partition (tex 10637–10640, "a component meeting several terminals gives
their forest difference"). Kind: PROVED. -/
theorem rooted_contract {ε : L →+ ZMod 2} {A : Config L → ZMod 2} (hA : CoefficientRules ε A)
    (hF : ForestProduct ε A) {Γ : Config L} (hΓ : Γ.Compatible ε) {T X : Finset ℕ}
    (hV : Γ.V = T ∪ X) (hTX : Disjoint T X) (hX : ∀ x ∈ X, Γ.t x = 0) {S : Finset (Sym2 ℕ)}
    (hroot : ∀ x ∈ X, ∃ a ∈ T, conn S x a) :
    A ((zeroAux Γ X).contractBy S) = diff A (Γ.restrict T) (starForest T S) := by
  have hΓ0 : (zeroAux Γ X).Compatible ε := zeroAux_compatible hΓ hX
  have hTsub : T ⊆ Γ.V := hV ▸ subset_union_left
  have hTV : ∀ u ∈ Γ.V, ∃ a ∈ T, conn S a u := by
    intro u hu
    rw [hV] at hu
    rcases mem_union.1 hu with h | h
    · exact ⟨u, h, conn_refl _ _⟩
    · obtain ⟨a, ha, hxa⟩ := hroot u h
      exact ⟨a, ha, conn_symm hxa⟩
  -- change of block map: the least terminal of each block
  have hb : A ((zeroAux Γ X).contractBy S) = A (bq (zeroAux Γ X) (rep T S)) := by
    rw [contractBy_eq_bq]
    refine hA.graph_dependence _ _ (bq_compatible hΓ0 _) (bq_isIso (fun u hu v hv => ?_))
    change u ∈ Γ.V at hu
    change v ∈ Γ.V at hv
    change rep Γ.V S u = rep Γ.V S v ↔ rep T S u = rep T S v
    rw [rep_eq_iff (self_conn hu) (self_conn hv), rep_eq_iff (hTV u hu) (hTV v hv)]
  -- the auxiliary vertices contribute nothing to types and incidences
  have hzT : ∀ u ∈ T, ∀ u' ∈ T, (zeroAux Γ X).z u u' = Γ.z u u' := by
    intro u hu u' hu'
    show (if u ∈ X ∨ u' ∈ X then 0 else Γ.z u u') = Γ.z u u'
    rw [ite_eq_right]
    rintro (h | h)
    · exact disjoint_left.1 hTX hu h
    · exact disjoint_left.1 hTX hu' h
  have hzX : ∀ u u', u ∈ X ∨ u' ∈ X → (zeroAux Γ X).z u u' = 0 := fun u u' h => ite_eq_left h
  have hc : A (bq (zeroAux Γ X) (rep T S)) = A (bq (Γ.restrict T) (rep T S)) := by
    refine hA.graph_dependence _ _ (bq_compatible hΓ0 _) (isIso_of_agree ?_ ?_ ?_)
    · show Γ.V.image (rep T S) = T.image (rep T S)
      apply Subset.antisymm
      · intro r hr
        obtain ⟨u, hu, rfl⟩ := mem_image.1 hr
        obtain ⟨a, ha, hau⟩ := hTV u hu
        exact mem_image.2 ⟨a, ha, rep_eq_of_conn hau (self_conn ha)⟩
      · exact image_subset_image hTsub
    · intro r _
      show ∑ u ∈ Γ.V.filter (fun u => rep T S u = r), Γ.t u =
        ∑ u ∈ T.filter (fun u => rep T S u = r), Γ.t u
      exact sum_filter_aux hV _ Γ.t (fun x hx _ => hX x hx)
    · intro r _ r' _ _
      show ∑ u ∈ Γ.V.filter (fun u => rep T S u = r),
          ∑ u' ∈ Γ.V.filter (fun u' => rep T S u' = r'), (zeroAux Γ X).z u u' =
        ∑ u ∈ T.filter (fun u => rep T S u = r), ∑ u' ∈ T.filter (fun u' => rep T S u' = r'),
          Γ.z u u'
      refine (sum_filter_aux hV _ _ ?_).trans (sum_congr rfl (fun u hu => ?_))
      · intro x hx _
        exact sum_eq_zero (fun u' _ => hzX x u' (Or.inl hx))
      · refine (sum_filter_aux hV _ _ ?_).trans (sum_congr rfl (fun u' hu' => ?_))
        · intro x hx _
          exact hzX u x (Or.inr hx)
        · exact hzT u (mem_filter.1 hu).1 u' (mem_filter.1 hu').1
  have hd : bq (Γ.restrict T) (rep T S) = (Γ.restrict T).contractBy (starForest T S) := by
    rw [contractBy_eq_bq]
    exact bq_congr (fun a ha => (rep_starForest ha).symm)
  have he : diff A (Γ.restrict T) (starForest T S) =
      A ((Γ.restrict T).contractBy (starForest T S)) := by
    rw [hF (Γ.restrict T) (restrict_compatible hΓ hTsub) _ (starForest_subset_pairs T S)]
    exact ite_eq_left (isForest_starForest T S)
  rw [hb, hc, hd, he]

/-- A forest with a terminal-free component: the contracted block is an isolated primary vertex,
so the contribution vanishes by primary isolation (tex 10637–10639). Kind: PROVED. -/
theorem unrooted_contract {ε : L →+ ZMod 2} {A : Config L → ZMod 2} (hA : CoefficientRules ε A)
    {Γ : Config L} (hΓ : Γ.Compatible ε) {T X : Finset ℕ} (hV : Γ.V = T ∪ X)
    (hX : ∀ x ∈ X, Γ.t x = 0) (S : Finset (Sym2 ℕ)) {x : ℕ} (hx : x ∈ X)
    (hno : ∀ a ∈ T, ¬ conn S x a) :
    A ((zeroAux Γ X).contractBy S) = 0 := by
  have hxV : x ∈ Γ.V := hV ▸ mem_union_right T hx
  have hblk : ∀ u ∈ Γ.V, rep Γ.V S u = rep Γ.V S x → u ∈ X := by
    intro u hu h
    have hc : conn S u x := (rep_eq_iff (self_conn hu) (self_conn hxV)).1 h
    have hu' : u ∈ T ∪ X := hV ▸ hu
    rcases mem_union.1 hu' with hT | hX'
    · exact absurd (conn_symm hc) (hno u hT)
    · exact hX'
  rw [contractBy_eq_bq]
  refine hA.primary_isolation _ (bq_compatible (zeroAux_compatible hΓ hX) _) (rep Γ.V S x)
    (mem_image_of_mem _ hxV) ?_ ?_
  · show ∑ u ∈ Γ.V.filter (fun u => rep Γ.V S u = rep Γ.V S x), Γ.t u = 0
    exact sum_eq_zero (fun u hu => hX u (hblk u (mem_filter.1 hu).1 (mem_filter.1 hu).2))
  · intro w _ _
    constructor
    · show ∑ u ∈ Γ.V.filter (fun u => rep Γ.V S u = rep Γ.V S x),
        ∑ u' ∈ Γ.V.filter (fun u' => rep Γ.V S u' = w), (zeroAux Γ X).z u u' = 0
      refine sum_eq_zero (fun u hu => sum_eq_zero (fun u' _ => ?_))
      exact ite_eq_left (Or.inl (hblk u (mem_filter.1 hu).1 (mem_filter.1 hu).2))
    · show ∑ u ∈ Γ.V.filter (fun u => rep Γ.V S u = w),
        ∑ u' ∈ Γ.V.filter (fun u' => rep Γ.V S u' = rep Γ.V S x), (zeroAux Γ X).z u u' = 0
      refine sum_eq_zero (fun u _ => sum_eq_zero (fun u' hu' => ?_))
      exact ite_eq_left (Or.inr (hblk u' (mem_filter.1 hu').1 (mem_filter.1 hu').2))

/-! ### The action on sums and on squarefree monomials -/

/-- The action is additive over finite sums of polynomials. Helper for tex 10635–10650. Kind: PROVED. -/
theorem act_finset_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Sym2 ℕ) (ZMod 2))
    (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act (∑ i ∈ s, p i) f U = ∑ i ∈ s, act (p i) f U := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, act_zero]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, act_add]
    exact congrArg (fun y => act (p i) f U + y) ih

/-- A product of distinct variables is the indicator monomial. Helper for tex 10641–10649. Kind: PROVED. -/
theorem prod_X_eq_monomial (F : Finset (Sym2 ℕ)) :
    (∏ e ∈ F, MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) =
      MvPolynomial.monomial (ind F) 1 := by
  rw [ind, MvPolynomial.monomial_sum_one]
  rfl

/-- A product of distinct variables acts by the iterated difference. Helper for tex 10635–10650. Kind: PROVED. -/
theorem act_prod_X (F : Finset (Sym2 ℕ)) (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act (∏ e ∈ F, MvPolynomial.X e) f U = ∑ W ∈ F.powerset, f (symmDiff U W) := by
  rw [prod_X_eq_monomial, act_monomial, one_mul, actT_ind]
  rfl

/-- Symmetric difference with the empty set. Helper. Kind: PROVED. -/
theorem empty_symmDiff' (W : Finset (Sym2 ℕ)) : symmDiff (∅ : Finset (Sym2 ℕ)) W = W :=
  bot_symmDiff W

end NetworkProof

open NetworkProof

/-- **Network expansion relative to the forest product** (tex 10635–10650): expand in the bits
incident to the auxiliary vertices, contract the chosen forest edges; a component with no
terminal vanishes by primary isolation, a rooted forest gives the forest difference of its
terminal partition. Kind: PROVED (from the coefficient rules and the forest product). -/
theorem netOp_expansion_of_forest {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) (hF : ForestProduct ε A) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (T X : Finset ℕ) (hV : Γ.V = T ∪ X) (hTX : Disjoint T X) (hX : ∀ x ∈ X, Γ.t x = 0) :
    A Γ = act (netOp Γ T X) (fun U => A ((Γ.restrict T).flipBy U)) ∅ := by
  classical
  have hΓ0 : (zeroAux Γ X).Compatible ε := zeroAux_compatible hΓ hX
  have hNp : netEdges Γ T X ⊆ pairs Γ.V := hV ▸ netEdges_subset_pairs
  rw [hA.graph_dependence _ _ hΓ (flip_zeroAux_iso hΓ hV hX),
    ← sum_powerset_sum_powerset (netEdges Γ T X) (fun U => A ((zeroAux Γ X).flipBy U))]
  have h3 : ∀ S ∈ (netEdges Γ T X).powerset,
      (∑ U ∈ S.powerset, A ((zeroAux Γ X).flipBy U)) =
      if IsRootedForest T X S then
        act (∏ e ∈ starForest T S, MvPolynomial.X e) (fun U => A ((Γ.restrict T).flipBy U)) ∅
      else 0 := by
    intro S hS
    have hSp : S ⊆ pairs Γ.V := (mem_powerset.1 hS).trans hNp
    have hd := hF (zeroAux Γ X) hΓ0 S hSp
    change diff A (zeroAux Γ X) S = _
    rw [hd, act_prod_X]
    change (if IsForest Γ.V S then A ((zeroAux Γ X).contractBy S) else 0) = _
    by_cases hfor : IsForest Γ.V S
    · rw [ite_eq_left hfor]
      by_cases hroot : ∀ x ∈ X, ∃ a ∈ T, conn S x a
      · have hrf : IsRootedForest T X S := ⟨hV ▸ hfor, hroot⟩
        rw [ite_eq_left hrf, rooted_contract hA hF hΓ hV hTX hX hroot]
        simp only [diff, empty_symmDiff']
      · rw [ite_eq_right (fun h => hroot h.2)]
        push Not at hroot
        obtain ⟨x, hx, hno⟩ := hroot
        exact unrooted_contract hA hΓ hV hX S hx hno
    · rw [ite_eq_right hfor, ite_eq_right (fun h => hfor (hV ▸ h.1))]
  rw [sum_congr rfl h3, ← sum_filter, netOp, act_finset_sum]

namespace NetworkProof

/-! ### Several networks -/

omit [AddCommGroup L] in
/-- The network operator only depends on the network edges. Helper for tex 10651–10655. Kind: PROVED. -/
theorem netOp_congr_edges {Γ Δ : Config L} {T X : Finset ℕ}
    (h : netEdges Γ T X = netEdges Δ T X) : netOp Γ T X = netOp Δ T X := by
  unfold netOp; rw [h]

omit [AddCommGroup L] in
/-- Flipping terminal pairs does not change the network edges. Helper for tex 10651–10655. Kind: PROVED. -/
theorem netEdges_flipBy_restrict {Γ : Config L} {T X : Finset ℕ} (hTX : Disjoint T X)
    (T' : Finset ℕ) {W : Finset (Sym2 ℕ)} (hW : W ⊆ pairs T) :
    netEdges ((Γ.restrict T').flipBy W) T X = netEdges Γ T X := by
  unfold netEdges
  congr 1
  apply filter_congr
  intro p hp
  have hp1 : p.1 ∈ X := (mem_product.1 hp).1
  have hnot : ¬ (p.1 ≠ p.2 ∧ s(p.1, p.2) ∈ W) := fun h =>
    disjoint_left.1 hTX (mk_mem_pairs.1 (hW h.2)).1 hp1
  show (p.1 ≠ p.2 ∧ Γ.z p.1 p.2 + (if p.1 ≠ p.2 ∧ s(p.1, p.2) ∈ W then 1 else 0) = 1) ↔
    (p.1 ≠ p.2 ∧ Γ.z p.1 p.2 = 1)
  rw [ite_eq_right hnot, add_zero]

/-- Adding isolated vertices does not change representatives. Helper for tex 10651–10655. Kind: PROVED. -/
theorem rep_union_eq {V Y W : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs W)
    (hYW : Disjoint Y W) {a : ℕ} (ha : a ∈ V) (haW : a ∈ W) : rep (V ∪ Y) S a = rep V S a := by
  apply le_antisymm
  · exact rep_le (mem_union_left Y (rep_mem (self_conn ha))) (conn_rep (self_conn ha))
  · have hr : rep (V ∪ Y) S a ∈ V ∪ Y := rep_mem (self_conn (mem_union_left Y ha))
    have hc : conn S (rep (V ∪ Y) S a) a := conn_rep (self_conn (mem_union_left Y ha))
    rcases mem_union.1 hr with h | h
    · exact rep_le h hc
    · have hnW : rep (V ∪ Y) S a ∉ W := disjoint_left.1 hYW h
      have he := conn_eq_of_not_mem hS hc hnW
      rw [he] at h
      exact absurd haW (disjoint_left.1 hYW h)

/-- An isolated added vertex is its own representative. Helper for tex 10651–10655. Kind: PROVED. -/
theorem rep_union_of_mem_Y {V Y W : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs W)
    (hYW : Disjoint Y W) {y : ℕ} (hy : y ∈ Y) : rep (V ∪ Y) S y = y := by
  have hc : conn S (rep (V ∪ Y) S y) y := conn_rep (self_conn (mem_union_right V hy))
  exact (conn_eq_of_not_mem hS (conn_symm hc) (disjoint_left.1 hYW hy)).symm

/-- Isolated added vertices are added components. Helper for tex 10651–10655. Kind: PROVED. -/
theorem ncomp_union_isolated {V Y : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs V)
    (hVY : Disjoint V Y) : ncomp (V ∪ Y) S = ncomp V S + Y.card := by
  have hYV : Disjoint Y V := hVY.symm
  unfold ncomp
  have h1 : V.image (rep (V ∪ Y) S) = V.image (rep V S) :=
    image_congr (fun a ha => rep_union_eq hS hYV (mem_coe.1 ha) (mem_coe.1 ha))
  have h2 : Y.image (rep (V ∪ Y) S) = Y := by
    have h3 : Y.image (rep (V ∪ Y) S) = Y.image id :=
      image_congr (fun y hy => rep_union_of_mem_Y (V := V) hS hYV (mem_coe.1 hy))
    rw [h3, image_id]
  rw [image_union, h1, h2]
  apply card_union_of_disjoint
  rw [disjoint_left]
  intro r hr hrY
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hr
  exact disjoint_left.1 hVY (rep_mem (self_conn ha)) hrY

/-- Adding isolated vertices keeps the forest condition. Helper for tex 10651–10655. Kind: PROVED. -/
theorem isForest_union_isolated {V Y : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs V)
    (hVY : Disjoint V Y) : IsForest (V ∪ Y) S ↔ IsForest V S := by
  unfold IsForest
  rw [ncomp_union_isolated hS hVY, card_union_of_disjoint hVY]
  constructor
  · rintro ⟨_, h⟩; exact ⟨hS, by omega⟩
  · rintro ⟨_, h⟩; exact ⟨hS.trans (pairs_mono subset_union_left), by omega⟩

/-- Adding isolated terminals does not change the star forest. Helper for tex 10651–10655. Kind: PROVED. -/
theorem starForest_union_isolated {T Y W : Finset ℕ} {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs W)
    (hYW : Disjoint Y W) (hTW : T ⊆ W) : starForest (T ∪ Y) S = starForest T S := by
  classical
  unfold starForest
  have hfil : (T ∪ Y).filter (fun a => rep (T ∪ Y) S a ≠ a) =
      T.filter (fun a => rep T S a ≠ a) := by
    rw [filter_union]
    have hY : Y.filter (fun a => rep (T ∪ Y) S a ≠ a) = ∅ := by
      apply filter_eq_empty_iff.2
      intro y hy h
      exact h (rep_union_of_mem_Y hS hYW hy)
    rw [hY, union_empty]
    apply filter_congr
    intro a ha
    rw [rep_union_eq hS hYW ha (hTW ha)]
  rw [hfil]
  apply image_congr
  intro a ha
  have ha' := (mem_filter.1 (mem_coe.1 ha)).1
  show s(rep (T ∪ Y) S a, a) = s(rep T S a, a)
  rw [rep_union_eq hS hYW ha' (hTW ha')]

omit [AddCommGroup L] in
/-- The operator of a network does not see further terminal-like vertices that have no edge to
its auxiliary vertices (tex 10651–10655, "distinct networks have no edges between their
auxiliary vertices"). Kind: PROVED. -/
theorem netOp_union_terminals {Γ : Config L} {T X Y : Finset ℕ}
    (hXY : Disjoint X Y) (hTY : Disjoint T Y) (hsep : ∀ x ∈ X, ∀ y ∈ Y, Γ.z x y = 0) :
    netOp Γ (T ∪ Y) X = netOp Γ T X := by
  classical
  have hYW : Disjoint Y (T ∪ X) := disjoint_union_right.2 ⟨hTY.symm, hXY.symm⟩
  have hE : netEdges Γ (T ∪ Y) X = netEdges Γ T X := by
    ext e
    induction e using Sym2.ind with
    | _ v w =>
      rw [mk_mem_netEdges, mk_mem_netEdges]
      have key : ∀ a b, a ∈ X → b ∈ (T ∪ Y) ∪ X → Γ.z a b = 1 → b ∈ T ∪ X := by
        intro a b ha hb hz
        rcases mem_union.1 hb with hb | hb
        · rcases mem_union.1 hb with hb | hb
          · exact mem_union_left X hb
          · rw [hsep a ha b hb] at hz; exact absurd hz (by decide)
        · exact mem_union_right T hb
      have mono : T ∪ X ⊆ (T ∪ Y) ∪ X := union_subset_union subset_union_left (subset_refl X)
      constructor
      · rintro ⟨hne, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
        · exact ⟨hne, Or.inl ⟨h1, key v w h1 h2 h3, h3⟩⟩
        · exact ⟨hne, Or.inr ⟨h1, key w v h1 h2 h3, h3⟩⟩
      · rintro ⟨hne, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
        · exact ⟨hne, Or.inl ⟨h1, mono h2, h3⟩⟩
        · exact ⟨hne, Or.inr ⟨h1, mono h2, h3⟩⟩
  unfold netOp
  rw [hE]
  apply sum_congr
  · apply filter_congr
    intro S hS
    have hSp : S ⊆ pairs (T ∪ X) := (mem_powerset.1 hS).trans netEdges_subset_pairs
    unfold IsRootedForest
    have hUnion : (T ∪ Y) ∪ X = (T ∪ X) ∪ Y := by
      ext u; simp only [mem_union]; tauto
    rw [hUnion, isForest_union_isolated hSp hYW.symm]
    apply and_congr_right
    intro _
    constructor
    · intro h x hx
      obtain ⟨a, ha, hxa⟩ := h x hx
      rcases mem_union.1 ha with ha | ha
      · exact ⟨a, ha, hxa⟩
      · have he := conn_eq_of_not_mem hSp (conn_symm hxa) (disjoint_left.1 hYW ha)
        exact absurd (he ▸ ha) (disjoint_left.1 hXY hx)
    · intro h x hx
      obtain ⟨a, ha, hxa⟩ := h x hx
      exact ⟨a, mem_union_left Y ha, hxa⟩
  · intro S hS
    have hSp : S ⊆ pairs (T ∪ X) :=
      (mem_powerset.1 (mem_filter.1 hS).1).trans netEdges_subset_pairs
    rw [starForest_union_isolated hSp hYW subset_union_left]

omit [AddCommGroup L] in
/-- The variables of a network operator are terminal pairs. Helper for tex 10651–10655. Kind: PROVED. -/
theorem netOp_support_vars {Γ : Config L} {T X : Finset ℕ} {m : Sym2 ℕ →₀ ℕ}
    (hm : m ∈ (netOp Γ T X).support) : m.support ⊆ pairs T := by
  classical
  unfold netOp at hm
  obtain ⟨S, _, hS⟩ := mem_biUnion.1 (MvPolynomial.support_sum hm)
  rw [prod_X_eq_monomial] at hS
  have h1 := MvPolynomial.support_monomial_subset hS
  rw [mem_singleton] at h1
  rw [h1, ind_support]
  exact starForest_subset_pairs T S

/-- Shifting the function by a flip set moves the evaluation point. Helper for tex 10651–10655. Kind: PROVED. -/
theorem act_shift (p : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f : Finset (Sym2 ℕ) → ZMod 2)
    (W : Finset (Sym2 ℕ)) : act p (fun U => f (symmDiff W U)) ∅ = act p f W := by
  rw [act_eq_sum p _ ∅ subset_rfl, act_eq_sum p f W subset_rfl]
  refine sum_congr rfl (fun m _ => ?_)
  congr 1
  unfold actT
  split_ifs
  · refine sum_congr rfl (fun W' _ => ?_)
    rw [empty_symmDiff']
  · rfl

omit [AddCommGroup L] in
/-- Successive flips compose by symmetric difference. Helper for tex 10651–10655. Kind: PROVED. -/
theorem flipBy_restrict_flipBy (Γ : Config L) (T T' : Finset ℕ) (W U : Finset (Sym2 ℕ)) :
    (((Γ.restrict T').flipBy W).restrict T).flipBy U = (Γ.restrict T).flipBy (symmDiff W U) := by
  have hz : ∀ a b, Γ.z a b + (if a ≠ b ∧ s(a, b) ∈ W then (1 : ZMod 2) else 0) +
      (if a ≠ b ∧ s(a, b) ∈ U then 1 else 0) =
      Γ.z a b + (if a ≠ b ∧ s(a, b) ∈ symmDiff W U then 1 else 0) := by
    intro a b
    rw [add_assoc]
    congr 1
    by_cases hab : a = b
    · simp [hab]
    · have two : (1 : ZMod 2) + 1 = 0 := rfl
      by_cases h1 : s(a, b) ∈ W <;> by_cases h2 : s(a, b) ∈ U <;>
        simp [hab, h1, h2, Finset.mem_symmDiff, two]
  show Config.mk T Γ.t (fun a b => Γ.z a b + (if a ≠ b ∧ s(a, b) ∈ W then (1 : ZMod 2) else 0) +
      (if a ≠ b ∧ s(a, b) ∈ U then 1 else 0)) =
    Config.mk T Γ.t (fun a b => Γ.z a b + (if a ≠ b ∧ s(a, b) ∈ symmDiff W U then 1 else 0))
  congr 1
  funext a b
  exact hz a b

/-- The indicator monomial of `F` is one variable exactly when `F` is a singleton. Helper for tex 10641–10649. Kind: PROVED. -/
theorem ind_eq_single_iff (F : Finset (Sym2 ℕ)) (e : Sym2 ℕ) :
    ind F = Finsupp.single e 1 ↔ F = {e} := by
  constructor
  · intro h
    ext x
    have hx := DFunLike.congr_fun h x
    rw [ind_apply, Finsupp.single_apply] at hx
    rw [mem_singleton]
    by_cases h1 : x ∈ F <;> by_cases h2 : e = x
    · exact ⟨fun _ => h2.symm, fun _ => h1⟩
    · rw [ite_eq_left h1, ite_eq_right h2] at hx; exact absurd hx one_ne_zero
    · rw [ite_eq_right h1, ite_eq_left h2] at hx; exact absurd hx.symm one_ne_zero
    · exact ⟨fun h => absurd h h1, fun h => absurd h.symm h2⟩
  · rintro rfl
    rw [ind, sum_singleton]

end NetworkProof

open NetworkProof

/-- **Distinct networks multiply, relative to the forest product** (tex 10651–10655): networks
with no edges between their auxiliary vertices act by the product of their operators.
Kind: PROVED (from the coefficient rules and the forest product). -/
theorem netOp_expansion_multi_of_forest {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) (hF : ForestProduct ε A) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (T : Finset ℕ) {κ : Type*} (N : Finset κ) (Xf : κ → Finset ℕ)
    (hV : Γ.V = T ∪ N.biUnion Xf) (hTX : ∀ ν ∈ N, Disjoint T (Xf ν))
    (hdisj : ∀ ν ∈ N, ∀ μ ∈ N, ν ≠ μ → Disjoint (Xf ν) (Xf μ))
    (hX : ∀ ν ∈ N, ∀ x ∈ Xf ν, Γ.t x = 0)
    (hsep : ∀ ν ∈ N, ∀ μ ∈ N, ν ≠ μ → ∀ x ∈ Xf ν, ∀ y ∈ Xf μ, Γ.z x y = 0) :
    A Γ = act (∏ ν ∈ N, netOp Γ T (Xf ν)) (fun U => A ((Γ.restrict T).flipBy U)) ∅ := by
  classical
  induction N using Finset.induction_on generalizing Γ with
  | empty =>
    rw [prod_empty, act_one]
    refine hA.graph_dependence _ _ hΓ (isIso_of_agree ?_ (fun _ _ => rfl) (fun v _ w _ _ => ?_))
    · show Γ.V = T
      rw [hV, biUnion_empty, union_empty]
    · show Γ.z v w = Γ.z v w + (if v ≠ w ∧ s(v, w) ∈ (∅ : Finset (Sym2 ℕ)) then 1 else 0)
      rw [ite_eq_right (fun h => notMem_empty _ h.2), add_zero]
  | insert ν N hν ih =>
    have hνN : ν ∈ insert ν N := mem_insert_self ν N
    have hTY : Disjoint T (N.biUnion Xf) :=
      (disjoint_biUnion_right _ _ _).2 (fun μ hμ => hTX μ (mem_insert_of_mem hμ))
    have hXY : Disjoint (Xf ν) (N.biUnion Xf) :=
      (disjoint_biUnion_right _ _ _).2 (fun μ hμ => hdisj ν hνN μ (mem_insert_of_mem hμ)
        (fun h => hν (h ▸ hμ)))
    have hsepν : ∀ x ∈ Xf ν, ∀ y ∈ N.biUnion Xf, Γ.z x y = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ, hyμ⟩ := mem_biUnion.1 hy
      exact hsep ν hνN μ (mem_insert_of_mem hμ) (fun h => hν (h ▸ hμ)) x hx y hyμ
    have hV' : Γ.V = (T ∪ N.biUnion Xf) ∪ Xf ν := by
      rw [hV, biUnion_insert]
      ext u; simp only [mem_union]; tauto
    have hTX' : Disjoint (T ∪ N.biUnion Xf) (Xf ν) :=
      disjoint_union_left.2 ⟨hTX ν hνN, hXY.symm⟩
    have hsub : T ∪ N.biUnion Xf ⊆ Γ.V := by rw [hV']; exact subset_union_left
    refine (netOp_expansion_of_forest hA hF Γ hΓ (T ∪ N.biUnion Xf) (Xf ν) hV' hTX'
      (hX ν hνN)).trans ?_
    rw [prod_insert hν, act_mul, netOp_union_terminals hXY hTY hsepν]
    apply act_congr_fun
    intro m hm W hW
    have hWT : W ⊆ pairs T := hW.trans (netOp_support_vars hm)
    rw [empty_symmDiff']
    show A ((Γ.restrict (T ∪ N.biUnion Xf)).flipBy W) =
      act (∏ μ ∈ N, netOp Γ T (Xf μ)) (fun U => A ((Γ.restrict T).flipBy U)) W
    have hih := ih ((Γ.restrict (T ∪ N.biUnion Xf)).flipBy W)
      (flipBy_compatible (restrict_compatible hΓ hsub) W) rfl
      (fun μ hμ => hTX μ (mem_insert_of_mem hμ))
      (fun μ hμ μ' hμ' h => hdisj μ (mem_insert_of_mem hμ) μ' (mem_insert_of_mem hμ') h)
      (fun μ hμ x hx => hX μ (mem_insert_of_mem hμ) x hx)
      (fun μ hμ μ' hμ' h x hx y hy => by
        show Γ.z x y + (if x ≠ y ∧ s(x, y) ∈ W then 1 else 0) = 0
        rw [ite_eq_right (fun h' => disjoint_left.1 (hTX μ (mem_insert_of_mem hμ))
          (mk_mem_pairs.1 (hWT h'.2)).1 hx), add_zero]
        exact hsep μ (mem_insert_of_mem hμ) μ' (mem_insert_of_mem hμ') h x hx y hy)
    rw [hih, prod_congr rfl (fun μ hμ => netOp_congr_edges
      (netEdges_flipBy_restrict (hTX μ (mem_insert_of_mem hμ)) _ hWT)),
      ← act_shift _ (fun U => A ((Γ.restrict T).flipBy U)) W]
    simp only [flipBy_restrict_flipBy]

open Classical in
/-- Degree-zero coefficient of a network operator: the number of rooted forests whose terminal
partition is discrete (tex 10641–10649). Kind: PROVED. -/
theorem netOp_constantCoeff (Γ : Config L) (T X : Finset ℕ) :
    MvPolynomial.constantCoeff (netOp Γ T X) =
      (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = ∅)).card : ZMod 2) := by
  have h0 : ∀ F : Finset (Sym2 ℕ), MvPolynomial.constantCoeff
      (∏ e ∈ F, MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) = if F = ∅ then 1 else 0 := by
    intro F
    rw [map_prod]
    simp only [MvPolynomial.constantCoeff_X]
    rcases F.eq_empty_or_nonempty with h | ⟨e, he⟩
    · rw [h, prod_empty, ite_eq_left rfl]
    · rw [prod_eq_zero he rfl, ite_eq_right (ne_empty_of_mem he)]
  unfold netOp
  rw [map_sum, sum_congr rfl (fun S _ => h0 _), sum_boole, filter_filter]

open Classical in
/-- Degree-one coefficient of a network operator at the pair `{a, c}`: the number of rooted
forests whose terminal partition joins exactly `a` and `c` (tex 10641–10649). Kind: PROVED. -/
theorem netOp_coeff_X (Γ : Config L) (T X : Finset ℕ) {a c : ℕ} (ha : a ∈ T) (hc : c ∈ T)
    (hac : a ≠ c) :
    (netOp Γ T X).coeff (Finsupp.single s(a, c) 1) =
      (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = {s(a, c)})).card : ZMod 2) := by
  have h1 : ∀ F : Finset (Sym2 ℕ), (∏ e ∈ F, MvPolynomial.X e :
      MvPolynomial (Sym2 ℕ) (ZMod 2)).coeff (Finsupp.single s(a, c) 1) =
      if F = {s(a, c)} then 1 else 0 := by
    intro F
    rw [prod_X_eq_monomial, MvPolynomial.coeff_monomial]
    exact ite_cond_congr (propext (ind_eq_single_iff F _))
  unfold netOp
  rw [MvPolynomial.coeff_sum, sum_congr rfl (fun S _ => h1 _), sum_boole, filter_filter]

/-! ### The exact targets, with the forest product of `Forest` -/

section Targets

variable {ε : L →+ ZMod 2} {A : Config L → ZMod 2}

/-- Every symbol satisfying the coefficient rules has the forest product (`diff_eq_forest`,
tex 2200–2202, 10627–10633). Kind: PROVED. -/
theorem forestProduct_of_rules (hA : CoefficientRules ε A) : ForestProduct ε A :=
  fun _ hΓ _ hS => diff_eq_forest hA hΓ hS

/-- **Network expansion** (tex 10635–10650): expand in the auxiliary bits, contract forests;
terminal-free components vanish by primary isolation. Kind: PROVED. -/
theorem netOp_expansion (hA : CoefficientRules ε A) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (T X : Finset ℕ) (hV : Γ.V = T ∪ X) (hTX : Disjoint T X) (hX : ∀ x ∈ X, Γ.t x = 0) :
    A Γ = act (netOp Γ T X) (fun U => A ((Γ.restrict T).flipBy U)) ∅ :=
  netOp_expansion_of_forest hA (forestProduct_of_rules hA) Γ hΓ T X hV hTX hX

/-- **Distinct networks multiply** (tex 10651–10655). Kind: PROVED. -/
theorem netOp_expansion_multi (hA : CoefficientRules ε A) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (T : Finset ℕ) {κ : Type*} (N : Finset κ) (Xf : κ → Finset ℕ)
    (hV : Γ.V = T ∪ N.biUnion Xf) (hTX : ∀ ν ∈ N, Disjoint T (Xf ν))
    (hdisj : ∀ ν ∈ N, ∀ μ ∈ N, ν ≠ μ → Disjoint (Xf ν) (Xf μ))
    (hX : ∀ ν ∈ N, ∀ x ∈ Xf ν, Γ.t x = 0)
    (hsep : ∀ ν ∈ N, ∀ μ ∈ N, ν ≠ μ → ∀ x ∈ Xf ν, ∀ y ∈ Xf μ, Γ.z x y = 0) :
    A Γ = act (∏ ν ∈ N, netOp Γ T (Xf ν)) (fun U => A ((Γ.restrict T).flipBy U)) ∅ :=
  netOp_expansion_multi_of_forest hA (forestProduct_of_rules hA) Γ hΓ T N Xf hV hTX hdisj hX
    hsep

end Targets

end ZInQ.Manuscript.RC.Symbols
