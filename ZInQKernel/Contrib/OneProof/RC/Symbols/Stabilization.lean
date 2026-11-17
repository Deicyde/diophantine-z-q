import ZInQKernel.Contrib.OneProof.RC.Symbols.Core

/-!
# Lane RC2: compatible finite graph tables on one ultrafilter (tex 10508–10552)

Manuscript: Proposition `ex:app-odd-stabilization` and its proof (tex 10508–10552).

* `RulesUpTo`: the coefficient rules valid at one finite odd stage for the cutoff `W`.
* `label_type_stabilizes`: bounded abstract data stabilize on the ultrafilter (pigeonhole: a
  finite union of sets lies in an ultrafilter iff one of them does).
* `limSymbol`, `limSymbol_spec`: the limit symbol, the value occurring on an ultrafilter-large set
  of stages, configuration by configuration.
* `normalize`, `normalize_iso`: a configuration with at most `W + 1` vertices is isomorphic to its
  normalization, with vertices `0, …, n - 1`; normalized data form a finite type.
* `cutoff_table_stabilizes`: for each cutoff `W`, one table (on normalized data) occurs on a set
  in the ultrafilter; on that set every stage table agrees with the limit symbol on all compatible
  configurations with at most `W + 1` vertices. Hence the selected tables agree on their common
  restrictions and their union is the limit symbol.
* `limSymbol_rules`: every rule instance involves finitely many configurations and is inherited
  at the cutoff `W = |V(Γ)|`.
* `odd_stabilization`: the proposition.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

variable {L : Type*} [AddCommGroup L]

/-- The coefficient rules on configurations with at most `W+1` vertices: the rules valid at one
finite odd stage for the cutoff `W` (tex 10533–10538). -/
structure RulesUpTo (ε : L →+ ZMod 2) (A : Config L → ZMod 2) (W : ℕ) : Prop where
  graph_dependence : ∀ Γ Δ : Config L, Γ.V.card ≤ W + 1 → Γ.Compatible ε → Γ.IsIso Δ → A Γ = A Δ
  contraction : ∀ Γ : Config L, Γ.V.card ≤ W + 1 → Γ.Compatible ε → ∀ v ∈ Γ.V, ∀ w ∈ Γ.V,
    v ≠ w → A Γ + A (Γ.flip v w) = A (Γ.contract v w)
  primary_isolation : ∀ Γ : Config L, Γ.V.card ≤ W + 1 → Γ.Compatible ε → ∀ v ∈ Γ.V,
    Γ.t v = 0 → (∀ w ∈ Γ.V, w ≠ v → Γ.z v w = 0 ∧ Γ.z w v = 0) → A Γ = 0

/-- Bounded abstract label data stabilize on the ultrafilter (tex 10510–10512, 10527–10532).
Kind: PROVED (pigeonhole: the finitely many fibres of `f` cover `I`, and a finite union of sets
lies in an ultrafilter iff one of them does). -/
theorem label_type_stabilizes {I α : Type*} [Finite α] (𝒰 : Ultrafilter I) (f : I → α) :
    ∃ a, ∀ᶠ i in (𝒰 : Filter I), f i = a := by
  have huniv : (⋃ a ∈ (Set.univ : Set α), {i | f i = a}) ∈ 𝒰 := by
    have h : (⋃ a ∈ (Set.univ : Set α), {i | f i = a}) = Set.univ := by
      ext i
      simp
    rw [h]
    exact Filter.univ_mem
  obtain ⟨a, -, ha⟩ := (Ultrafilter.finite_biUnion_mem_iff Set.finite_univ).mp huniv
  exact ⟨a, ha⟩

/-- The limit symbol: on each configuration, the value of the stage symbols on a set in the
ultrafilter (tex 10515–10517, 10540–10544). -/
noncomputable def limSymbol {I : Type*} (𝒰 : Ultrafilter I) (A : I → Config L → ZMod 2) :
    Config L → ZMod 2 :=
  fun Γ => Classical.choose (label_type_stabilizes 𝒰 (fun i => A i Γ))

omit [AddCommGroup L] in
/-- The stage symbols take the limit value on a set in the ultrafilter, configuration by
configuration (tex 10515–10517, 10540–10544). Kind: PROVED. -/
theorem limSymbol_spec {I : Type*} (𝒰 : Ultrafilter I) (A : I → Config L → ZMod 2)
    (Γ : Config L) : ∀ᶠ i in (𝒰 : Filter I), A i Γ = limSymbol 𝒰 A Γ :=
  Classical.choose_spec (label_type_stabilizes 𝒰 (fun i => A i Γ))

/-- Normalized configuration data with at most `W + 1` vertices, named `0, …, n - 1`: the vertex
count `n ≤ W + 1`, the types and the bits (padded beyond `n`). A finite type when `L` is finite
(tex 10513–10514, 10538–10540). -/
abbrev NormData (L : Type*) (W : ℕ) : Type _ :=
  Fin (W + 2) × (Fin (W + 1) → L) × (Fin (W + 1) → Fin (W + 1) → ZMod 2)

/-- The configuration with vertices `0, …, n - 1` given by normalized data (tex 10513–10514). -/
def normConfig {W : ℕ} (d : NormData L W) : Config L where
  V := Finset.range (d.1 : ℕ)
  t := fun a => if h : a < W + 1 then d.2.1 ⟨a, h⟩ else 0
  z := fun a b => if h : a < W + 1 ∧ b < W + 1 then d.2.2 ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- Normalization of a configuration with at most `W + 1` vertices: its vertices are renamed
increasingly to `0, …, n - 1` (tex 10513–10514). -/
noncomputable def normalize {W : ℕ} (Γ : Config L) (hc : Γ.V.card ≤ W + 1) : NormData L W :=
  (⟨Γ.V.card, by omega⟩,
    fun j => if h : (j : ℕ) < Γ.V.card then Γ.t (Γ.V.orderIsoOfFin rfl ⟨j, h⟩) else 0,
    fun j k => if h : (j : ℕ) < Γ.V.card ∧ (k : ℕ) < Γ.V.card then
      Γ.z (Γ.V.orderIsoOfFin rfl ⟨j, h.1⟩) (Γ.V.orderIsoOfFin rfl ⟨k, h.2⟩) else 0)

/-- A configuration is isomorphic to its normalization (tex 10513–10514, 10538–10540).
Kind: PROVED. -/
theorem normalize_iso {W : ℕ} (Γ : Config L) (hc : Γ.V.card ≤ W + 1) :
    Γ.IsIso (normConfig (normalize Γ hc)) := by
  let e := Γ.V.orderIsoOfFin (rfl : Γ.V.card = Γ.V.card)
  let f : Γ.V ≃ (normConfig (normalize Γ hc)).V :=
    e.symm.toEquiv.trans (Fin.equivSubtype.trans
      (Equiv.subtypeEquivRight fun x => Finset.mem_range.symm))
  have hf : ∀ v : Γ.V, ((f v : ℕ)) = ((e.symm v : Fin Γ.V.card) : ℕ) := fun v => rfl
  have hlt : ∀ v : Γ.V, ((e.symm v : Fin Γ.V.card) : ℕ) < W + 1 := fun v =>
    lt_of_lt_of_le (e.symm v).isLt hc
  have hval : ∀ v : Γ.V, (e ⟨((e.symm v : Fin Γ.V.card) : ℕ), (e.symm v).isLt⟩ : ℕ) = v :=
    fun v => by rw [Fin.eta, OrderIso.apply_symm_apply]
  refine ⟨f, fun v => ?_, fun v w _ => ?_⟩
  · change (if h : ((f v : ℕ)) < W + 1 then _ else 0) = Γ.t v
    rw [dite_eq_left (show ((f v : ℕ)) < W + 1 from hlt v)]
    change (if h : ((e.symm v : Fin Γ.V.card) : ℕ) < Γ.V.card then
      Γ.t (e ⟨((e.symm v : Fin Γ.V.card) : ℕ), h⟩) else 0) = Γ.t v
    rw [dite_eq_left (e.symm v).isLt, hval v]
  · change (if h : ((f v : ℕ)) < W + 1 ∧ ((f w : ℕ)) < W + 1 then _ else 0) = Γ.z v w
    rw [dite_eq_left (show ((f v : ℕ)) < W + 1 ∧ ((f w : ℕ)) < W + 1 from ⟨hlt v, hlt w⟩)]
    change (if h : ((e.symm v : Fin Γ.V.card) : ℕ) < Γ.V.card ∧
        ((e.symm w : Fin Γ.V.card) : ℕ) < Γ.V.card then
      Γ.z (e ⟨((e.symm v : Fin Γ.V.card) : ℕ), h.1⟩) (e ⟨((e.symm w : Fin Γ.V.card) : ℕ), h.2⟩)
      else 0) = Γ.z v w
    rw [dite_eq_left ⟨(e.symm v).isLt, (e.symm w).isLt⟩, hval v, hval w]

/-- **One table per cutoff** (tex 10512–10517, 10533–10544): for every cutoff `W`, the valid
stages give finitely many possible tables on compatible typed graphs with at most `W + 1`
vertices (through normalized data, by graph dependence at the stages); one table occurs on a set
in the ultrafilter, and on that set every stage table agrees with the limit symbol on all those
graphs. In particular the selected tables agree on their common restrictions, and their union
is the limit symbol. Kind: PROVED. -/
theorem cutoff_table_stabilizes [Finite L] {I : Type*} (𝒰 : Ultrafilter I)
    (ε : L →+ ZMod 2) (A : I → Config L → ZMod 2)
    (hvalid : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RulesUpTo ε (A i) W) (W : ℕ) :
    ∀ᶠ i in (𝒰 : Filter I), ∀ Γ : Config L, Γ.V.card ≤ W + 1 → Γ.Compatible ε →
      A i Γ = limSymbol 𝒰 A Γ := by
  -- the table of stage `i` on normalized data
  obtain ⟨T, hT⟩ := label_type_stabilizes 𝒰
    (fun i => fun d : NormData L W => A i (normConfig d))
  -- on valid stages the table determines the symbol on all graphs of the cutoff
  have htab : ∀ i, RulesUpTo ε (A i) W → (fun d : NormData L W => A i (normConfig d)) = T →
      ∀ Γ : Config L, ∀ hc : Γ.V.card ≤ W + 1, Γ.Compatible ε → A i Γ = T (normalize Γ hc) := by
    intro i hR hTi Γ hc hΓ
    rw [← hTi]
    exact hR.graph_dependence Γ _ hc hΓ (normalize_iso Γ hc)
  filter_upwards [hvalid W, hT] with i hR hTi
  intro Γ hc hΓ
  obtain ⟨j, hRj, hTj, hj⟩ := ((hvalid W).and (hT.and (limSymbol_spec 𝒰 A Γ))).exists
  rw [htab i hR hTi Γ hc hΓ, ← hj, htab j hRj hTj Γ hc hΓ]

/-- The limit symbol satisfies the coefficient rules (tex 10518–10519, 10545–10546): each rule
instance involves finitely many configurations and is inherited at the cutoff `W = |V(Γ)|`.
Kind: PROVED. -/
theorem limSymbol_rules {I : Type*} (𝒰 : Ultrafilter I) (ε : L →+ ZMod 2)
    (A : I → Config L → ZMod 2)
    (hvalid : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RulesUpTo ε (A i) W) :
    CoefficientRules ε (limSymbol 𝒰 A) := by
  refine ⟨fun Γ Δ hΓ hiso => ?_, fun Γ hΓ v hv w hw hvw => ?_, fun Γ hΓ v hv htv hz => ?_⟩
  · obtain ⟨i, hR, h1, h2⟩ := ((hvalid Γ.V.card).and
      ((limSymbol_spec 𝒰 A Γ).and (limSymbol_spec 𝒰 A Δ))).exists
    rw [← h1, ← h2]
    exact hR.graph_dependence Γ Δ (Nat.le_succ _) hΓ hiso
  · obtain ⟨i, hR, h1, h2, h3⟩ := ((hvalid Γ.V.card).and ((limSymbol_spec 𝒰 A Γ).and
      ((limSymbol_spec 𝒰 A (Γ.flip v w)).and (limSymbol_spec 𝒰 A (Γ.contract v w))))).exists
    rw [← h1, ← h2, ← h3]
    exact hR.contraction Γ (Nat.le_succ _) hΓ v hv w hw hvw
  · obtain ⟨i, hR, h1⟩ := ((hvalid Γ.V.card).and (limSymbol_spec 𝒰 A Γ)).exists
    rw [← h1]
    exact hR.primary_isolation Γ (Nat.le_succ _) hΓ v hv htv hz

/-- `ex:app-odd-stabilization` (tex 10508–10552). Kind: PROVED. The limit symbol is
`limSymbol 𝒰 A`; it satisfies the coefficient rules (`limSymbol_rules`), and a finite family of
compatible tests lies in one cutoff, where the selected table agrees with the limit symbol on an
ultrafilter-large set of actual stages (`cutoff_table_stabilizes`). -/
theorem odd_stabilization [Fintype L] [DecidableEq L] {I : Type*} (𝒰 : Ultrafilter I)
    (ε : L →+ ZMod 2) (A : I → Config L → ZMod 2)
    (hvalid : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RulesUpTo ε (A i) W) :
    ∃ Ainf : Config L → ZMod 2, CoefficientRules ε Ainf ∧
      ∀ (n : ℕ) (Γs : Fin n → Config L), (∀ k, (Γs k).Compatible ε) →
        ∀ᶠ i in (𝒰 : Filter I), ∀ k, A i (Γs k) = Ainf (Γs k) := by
  refine ⟨limSymbol 𝒰 A, limSymbol_rules 𝒰 ε A hvalid, fun n Γs hΓs => ?_⟩
  filter_upwards [cutoff_table_stabilizes 𝒰 ε A hvalid (∑ k, (Γs k).V.card)] with i hi k
  have hk : (Γs k).V.card ≤ ∑ k, (Γs k).V.card :=
    Finset.single_le_sum (f := fun k => (Γs k).V.card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
  exact hi (Γs k) (le_trans hk (Nat.le_succ _)) (hΓs k)

end ZInQ.Manuscript.RC.Symbols
