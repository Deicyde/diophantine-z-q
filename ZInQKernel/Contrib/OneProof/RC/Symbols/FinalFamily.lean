import ZInQKernel.Contrib.OneProof.RC.Symbols.Address
import ZInQKernel.Contrib.OneProof.RC.Symbols.Forest

/-!
# Lane RC2: the finite typed graphs of the final family (tex 2656–2701; App G 10587–10623)

The zero-total packets supply, for both symbols separately, nonzero terminal polynomials at every
nonzero address in one common alphabet; the two-symbol address lemma then gives one typed graph
on which both symbols are one at every nonzero address. The prime realization and the choice of
the actual theta stage (App G `ex:app-final-family`) are outside this lane.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

variable {L : Type*} [AddCommGroup L]

/-- Compatible bits for any typed vertex set: the forward bit of `u < v` is `ε_u ε_v`. -/
def stdBits (ε : L →+ ZMod 2) (t : ℕ → L) : ℕ → ℕ → ZMod 2 :=
  fun u v => if u < v then ε (t u) * ε (t v) else 0

/-- Auxiliary result for the final family graphs, tex 2656–2701 and 10587–10623. Kind: PROVED. -/
theorem stdBits_compatible (ε : L →+ ZMod 2) (V : Finset ℕ) (t : ℕ → L) :
    (Config.mk V t (stdBits ε t)).Compatible ε := by
  intro u _ v _ huv
  simp only [stdBits]
  rcases lt_or_gt_of_ne huv with h | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
  · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add, mul_comm]

/-- Primary auxiliary vertices do not change the total type at any address (tex 10622–10623:
"Every added network vertex is primary, so the total common label remains zero at each
address"). -/
theorem total_at_of_extends {b : ℕ} (Γ Γ' : Config L) (act' act'' : ℕ → Option (Fin b → ZMod 2))
    (hext : Γ.Extends Γ') (hact : ∀ v ∈ Γ.V, act'' v = act' v)
    (hnew : ∀ v ∈ Γ'.V, v ∉ Γ.V → Γ'.t v = 0) (x : Fin b → ZMod 2) :
    (Γ'.at act'' x).total = (Γ.at act' x).total := by
  classical
  unfold Config.total
  have hsplit : (Γ'.at act'' x).V =
      (Γ.at act' x).V ∪ ((Γ'.at act'' x).V.filter (fun v => v ∉ Γ.V)) := by
    ext v
    simp only [Config.at, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hv, hp⟩
      by_cases hvΓ : v ∈ Γ.V
      · left
        refine ⟨hvΓ, ?_⟩
        simpa [present, hact v hvΓ] using hp
      · exact Or.inr ⟨⟨hv, hp⟩, hvΓ⟩
    · rintro (⟨hvΓ, hp⟩ | ⟨⟨hv, hp⟩, _⟩)
      · exact ⟨hext.1 hvΓ, by simpa [present, hact v hvΓ] using hp⟩
      · exact ⟨hv, hp⟩
  have hdisj : Disjoint (Γ.at act' x).V ((Γ'.at act'' x).V.filter (fun v => v ∉ Γ.V)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_filter.mp hv').2 (Finset.filter_subset _ _ hv)
  rw [hsplit, Finset.sum_union hdisj]
  have h0 : ∑ v ∈ (Γ'.at act'' x).V.filter (fun v => v ∉ Γ.V), (Γ'.at act'' x).t v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    exact hnew v (Finset.filter_subset _ _ hv'.1) hv'.2
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun v hv => ?_
  exact hext.2.1 v (Finset.filter_subset _ _ hv)

/-- **The finite typed graphs of the final family** (tex 2656–2672, 2695–2701; App G
10587–10623, `ex:sec7-two-symbol-address`). Kind: PROVED from the coefficient rules. Two
symbols reading separately surjective projections of one finite elementary common alphabet,
each with a minimum nonempty unit seed of projected total zero (the filters containing one): for
every `b ≥ 1` there is one compatible typed graph with nonzero linear activations on which both
symbols are one at every nonzero address, the active configurations having total common label
zero. -/
theorem final_family_graphs [Fintype L] [DecidableEq L] (hL : ∀ x : L, x + x = 0)
    {ε : L →+ ZMod 2} {L₁ L₂ : Type*} [AddCommGroup L₁] [AddCommGroup L₂]
    {ε₁ : L₁ →+ ZMod 2} {ε₂ : L₂ →+ ZMod 2}
    (π₁ : L →+ L₁) (π₂ : L →+ L₂) (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂)
    (hε₁ : ∀ x, ε₁ (π₁ x) = ε x) (hε₂ : ∀ x, ε₂ (π₂ x) = ε x)
    {A₁ : Config L₁ → ZMod 2} {A₂ : Config L₂ → ZMod 2}
    (hA₁ : CoefficientRules ε₁ A₁) (hA₂ : CoefficientRules ε₂ A₂)
    {Γ₁ : Config L₁} {Γ₂ : Config L₂} (hm₁ : IsMinSeed ε₁ A₁ Γ₁) (hm₂ : IsMinSeed ε₂ A₂ Γ₂)
    (ht₁ : Γ₁.total = 0) (ht₂ : Γ₂.total = 0) (b : ℕ) (hb : 1 ≤ b) :
    ∃ (Γ : Config L) (act' : ℕ → Option (Fin b → ZMod 2)),
      Γ.Compatible ε ∧ (∀ v ∈ Γ.V, ∃ w, w ≠ 0 ∧ act' v = some w) ∧
      AddressConclusion ε ![fun Δ => A₁ (Δ.mapType π₁), fun Δ => A₂ (Δ.mapType π₂)] Γ act' ∧
      ∀ x : Fin b → ZMod 2, x ≠ 0 → (Γ.at act' x).total = 0 := by
  obtain ⟨V, t, act', hact, hall, hpk⟩ :=
    packet_terminals hL π₁ π₂ hπ₁ hπ₂ hε₁ hε₂ hA₁ hA₂ hm₁ hm₂ ht₁ ht₂ b hb
  have hc := stdBits_compatible ε V t
  refine ⟨Config.mk V t (stdBits ε t), act', hc, hact, ?_, fun x hx => (hpk _ hc x hx).2.1⟩
  exact two_symbol_address (hA₁.mapType π₁ hε₁) (hA₂.mapType π₂ hε₂) b hb _ hc act' hact hall
    (fun x hx => (hpk _ hc x hx).2.2.1) (fun x hx => (hpk _ hc x hx).2.2.2)

end ZInQ.Manuscript.RC.Symbols
