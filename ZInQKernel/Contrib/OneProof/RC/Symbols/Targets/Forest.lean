import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
namespace ZInQ.Manuscript.RC.Symbols
open Finset
variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {A : Config L → ZMod 2}

theorem Config.Compatible.contractBy {Γ : Config L} (h : Γ.Compatible ε) (S : Finset (Sym2 ℕ)) :
    (Γ.contractBy S).Compatible ε := sorry

open Classical in
/-- Forest product: iterated differences along a forest give the contracted symbol; a cycle
product is zero (tex 2200–2202, 10627–10633). -/
theorem diff_eq_forest (hA : CoefficientRules ε A) {Γ : Config L} (hΓ : Γ.Compatible ε)
    {S : Finset (Sym2 ℕ)} (hS : S ⊆ pairs Γ.V) :
    diff A Γ S = if IsForest Γ.V S then A (Γ.contractBy S) else 0 := sorry

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

theorem minSeed_bits_irrelevant (hA : CoefficientRules ε A) {Γ : Config L}
    (hmin : IsMinSeed ε A Γ) {Δ : Config L} (hΔ : Δ.Compatible ε) (hV : Δ.V = Γ.V)
    (ht : ∀ v ∈ Γ.V, Δ.t v = Γ.t v) : A Δ = 1 := sorry

theorem certificate_diff (hA : CoefficientRules ε A) {Γ : Config L} (hΓ : Γ.Compatible ε)
    {S : Finset (Sym2 ℕ)} (hS : IsForest Γ.V S) (h1 : A (Γ.contractBy S) = 1) :
    diff A Γ S = 1 := sorry

theorem partitionable_terminalNonzero (hA : CoefficientRules ε A) {Γ : Config L}
    (hΓ : Γ.Compatible ε) (hP : IsPartitionable ε A Γ) : TerminalNonzero A Γ := sorry

theorem partitionable_of_anchors (hA : CoefficientRules ε A) {Γ₀ Γ : Config L}
    (hmin : IsMinSeed ε A Γ₀) (hΓ : Γ.Compatible ε) (htot : Γ.total = Γ₀.total)
    (s : ℕ) (hs : s ∈ Γ₀.V) (anc : ℕ → ℕ) (hanc : Set.InjOn anc (Γ₀.V.erase s))
    (hancV : ∀ v ∈ Γ₀.V.erase s, anc v ∈ Γ.V) (hanct : ∀ v ∈ Γ₀.V.erase s, Γ.t (anc v) = Γ₀.t v)
    (hrem : (Γ.V \ (Γ₀.V.erase s).image anc).Nonempty) : IsPartitionable ε A Γ := sorry

/-- Reading a projection of the common alphabet (tex 2060–2065). -/
def Config.mapType {L' : Type*} [AddCommGroup L'] (π : L →+ L') (Γ : Config L) : Config L' :=
  { V := Γ.V, t := fun v => π (Γ.t v), z := Γ.z }

theorem CoefficientRules.mapType {L' : Type*} [AddCommGroup L'] {ε' : L' →+ ZMod 2}
    {A' : Config L' → ZMod 2} (hA : CoefficientRules ε' A') (π : L →+ L')
    (hε : ∀ x, ε' (π x) = ε x) : CoefficientRules ε (fun Γ => A' (Γ.mapType π)) := sorry

/-- Zero-total packets (App G, tex 10598–10623). -/
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
        TerminalNonzero (fun Δ => A₂ (Δ.mapType π₂)) ((Config.mk V t z).at act' x) := sorry
end ZInQ.Manuscript.RC.Symbols
