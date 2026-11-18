import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.H2

/-!
# UnramifiedComplex: inflation identifies the unramified classes

Manuscript `diophantine_zq.tex`, tex 4699–4701: "The unramified condition at a good place has the
same degree-zero invariants as the full local complex and injects in degree one."

For a surjective continuous homomorphism `π : Γ → G` (for `Γ = G_{K_w}`, `G = Gal(K_w^ur/K_w)`:
restriction to `K_w^ur`) and a continuous `G`-module `W`, `resRep X π` is `W` as a `Γ`-module.

* `infl : H¹(G, W) → H¹(Γ, W)`, Mathlib's `ContinuousCohomology.map π (𝟙 _) 1`; injective
  (`infl_injective`, through Tau Ceti's explicit comparison and its naturality);
* `h1ur := range infl ⊆ H¹(Γ, W)`, the unramified classes, `h1urEquiv : H¹(G, W) ≃ₗ H¹_ur`;
* `h0InflEquiv : H⁰(G, W) ≃ₗ H⁰(Γ, W)` (same invariants);
* for `G ≃ₜ* ℤ̂` and finite `W`: `card_h1_eq_card_h0` (`|W ⧸ (Φ−1)W| = |ker (Φ−1)|`),
  `card_h1ur : |H¹_ur| = |H⁰(G, W)|`, and `finrank_h1ur : dim H¹_ur = h⁰` over a finite field.

Kinds: everything PROVED.
-/

open CategoryTheory TauCeti.ContCohomology
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {k : Type} [Ring k] [TopologicalSpace k] (X : TopRep.{0} k G)
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (π : Γ →ₜ* G)

attribute [local instance] TopRep.distribMulAction

/-- `W` as a `Γ`-module through `π : Γ → G` (for `π : G_{K_w} → Gal(K_w^ur/K_w)`: the unramified
module `W` as a module for the full local Galois group). -/
abbrev resRep : TopRep k Γ := TopRep.res (π : Γ →* G) X

/-- The restricted action is continuous. -/
theorem continuousSMul_resRep [ContinuousSMul G X.V] : ContinuousSMul Γ (resRep X π).V :=
  ⟨(continuous_smul (M := G) (X := X.V)).comp ((map_continuous π).prodMap continuous_id)⟩

attribute [local instance] continuousSMul_resRep

/-- **Inflation** `H¹(G, W) → H¹(Γ, W)` along `π`, on Mathlib's continuous cohomology. -/
def infl : continuousCohomology 1 X →ₗ[k] continuousCohomology 1 (resRep X π) :=
  (_root_.ContinuousCohomology.map π (𝟙 (resRep X π)) 1).hom.toLinearMap

/-- Inflation on Tau Ceti's explicit `H¹` is injective for surjective `π`. -/
theorem explicitMap1_id_injective [ContinuousSMul G X.V] [DiscreteTopology X.V]
    (hπ : Function.Surjective π) :
    Function.Injective (explicitMap1 G X.V Γ (resRep X π).V π (AddMonoidHom.id X.V)
      continuous_id (fun _ _ => rfl)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitMap1_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine AddMonoidHom.mem_range.2 ⟨m, funext fun g => ?_⟩
    obtain ⟨γ, rfl⟩ := hπ g
    have := congrFun hm γ
    rw [d0_apply] at this ⊢
    exact this

/-- **Inflation `H¹(G, W) → H¹(Γ, W)` is injective** for surjective `π`. PROVED. -/
theorem infl_injective [ContinuousSMul G X.V] [DiscreteTopology X.V]
    (hπ : Function.Surjective π) : Function.Injective (infl X π) := by
  have key := X.explicitH1AddEquivContinuousCohomologyOfDiscrete_map (resRep X π) π
    (𝟙 (resRep X π)) (AddMonoidHom.id X.V) (fun _ => rfl) (fun _ _ => rfl)
  intro a b hab
  obtain ⟨x, rfl⟩ := X.explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective a
  obtain ⟨y, rfl⟩ := X.explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective b
  have hab' : _root_.ContinuousCohomology.map π (𝟙 (resRep X π)) 1
      (X.explicitH1AddEquivContinuousCohomologyOfDiscrete x) =
      _root_.ContinuousCohomology.map π (𝟙 (resRep X π)) 1
      (X.explicitH1AddEquivContinuousCohomologyOfDiscrete y) := hab
  rw [key, key] at hab'
  rw [explicitMap1_id_injective X π hπ
    ((resRep X π).explicitH1AddEquivContinuousCohomologyOfDiscrete.injective hab')]

/-- **The unramified classes** `H¹_ur ⊆ H¹(Γ, W)`: the image of inflation from `G`. -/
def h1ur : Submodule k (continuousCohomology 1 (resRep X π)) := LinearMap.range (infl X π)

/-- Inflation identifies `H¹(G, W)` with `H¹_ur`. -/
def h1urEquiv [ContinuousSMul G X.V] [DiscreteTopology X.V] (hπ : Function.Surjective π) :
    continuousCohomology 1 X ≃ₗ[k] h1ur X π :=
  LinearEquiv.ofInjective _ (infl_injective X π hπ)

/-- For `π` surjective, `W^Γ = W^G` inside `W`. -/
theorem invariants_resRep (hπ : Function.Surjective π) :
    (resRep X π).ρ.invariants = X.ρ.invariants := by
  ext u
  simp only [ContRepresentation.mem_invariants]
  constructor
  · intro h g
    obtain ⟨γ, rfl⟩ := hπ g
    exact h γ
  · intro h γ
    exact h (π γ)

/-- **Degree zero: `H⁰(G, W) ≅ H⁰(Γ, W)`** for `π` surjective — the unramified condition has the
degree-zero invariants of the full local complex (tex 4699–4700). -/
def h0InflEquiv (hπ : Function.Surjective π) :
    continuousCohomology 0 X ≃ₗ[k] continuousCohomology 0 (resRep X π) :=
  (_root_.ContinuousCohomology.zeroIso X).toContinuousLinearEquiv.toLinearEquiv ≪≫ₗ
    LinearEquiv.ofEq _ _ (invariants_resRep X π hπ).symm ≪≫ₗ
    (_root_.ContinuousCohomology.zeroIso (resRep X π)).toContinuousLinearEquiv.symm.toLinearEquiv

/-- For an endomorphism `f` of a finite module, `|W ⧸ f W| = |ker f|`. -/
theorem card_quot_range_eq_card_ker {W : Type} [AddCommGroup W] [Module k W] [Finite W]
    (f : W →ₗ[k] W) : Nat.card (W ⧸ LinearMap.range f) = Nat.card (LinearMap.ker f) := by
  have h1 := (LinearMap.range f).card_eq_card_quotient_mul_card
  have h2 := (LinearMap.ker f).card_eq_card_quotient_mul_card
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h2
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (h2.trans (mul_comm _ _)))

variable (e : G ≃ₜ* TauCeti.zHat.{0})

include e in
/-- **`|H¹(G, W)| = |H⁰(G, W)|`** for `G ≃ₜ* ℤ̂` and finite discrete `W`
(`|W ⧸ (Φ − 1)W| = |ker (Φ − 1)|`). PROVED. -/
theorem card_h1_eq_card_h0 [ContinuousSMul G X.V] [DiscreteTopology X.V] [Finite X.V] :
    Nat.card (continuousCohomology 1 X) = Nat.card (continuousCohomology 0 X) := by
  rw [← Nat.card_congr (h1Equiv e X).toEquiv, ← Nat.card_congr (h0Equiv e X).toEquiv,
    Nat.card_congr (h1Iso (frob e X)).toLinearEquiv.toEquiv,
    Nat.card_congr (h0Iso (frob e X)).toLinearEquiv.toEquiv]
  exact card_quot_range_eq_card_ker _

include e in
/-- **`|H¹_ur| = |H⁰|`** (tex 4699–4701: the unramified condition injects in degree one, with the
dimension of the degree-zero invariants). PROVED. -/
theorem card_h1ur [ContinuousSMul G X.V] [DiscreteTopology X.V] [Finite X.V]
    (hπ : Function.Surjective π) :
    Nat.card (h1ur X π) = Nat.card (continuousCohomology 0 X) := by
  rw [← Nat.card_congr (h1urEquiv X π hπ).toEquiv, card_h1_eq_card_h0 X e]

include e in
/-- `H⁰(G, W)` is finite for finite `W`. -/
theorem finite_h0 [ContinuousSMul G X.V] [DiscreteTopology X.V] [Finite X.V] :
    Finite (continuousCohomology 0 X) :=
  have : Finite ((frobCx (frob e X)).homology 0) :=
    Finite.of_equiv _ (h0Iso (frob e X)).toLinearEquiv.symm.toEquiv
  Finite.of_equiv _ (h0Equiv e X).toEquiv

include e in
/-- **`dim H¹_ur = h⁰`** over a finite field `k` (e.g. `𝔽₂`). PROVED. -/
theorem finrank_h1ur {k : Type} [Field k] [Finite k] [TopologicalSpace k] (X : TopRep.{0} k G)
    [ContinuousSMul G X.V] [DiscreteTopology X.V] [Finite X.V] (hπ : Function.Surjective π) :
    Module.finrank k (h1ur X π) = Module.finrank k (continuousCohomology 0 X) := by
  have hc := card_h1ur X π e hπ
  have : Finite (continuousCohomology 0 X) := finite_h0 X e
  have : Finite (h1ur X π) := Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.card_pos.ne')
  have h1 := Module.natCard_eq_pow_finrank (K := k) (V := h1ur X π)
  have h0 := Module.natCard_eq_pow_finrank (K := k) (V := continuousCohomology 0 X)
  rw [hc, h0] at h1
  exact (Nat.pow_right_injective Finite.one_lt_card h1).symm

end ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
