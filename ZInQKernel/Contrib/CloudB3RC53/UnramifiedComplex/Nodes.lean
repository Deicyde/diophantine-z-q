import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.Places

/-!
# UnramifiedComplex: the nodes

Manuscript `diophantine_zq.tex`, tex 3478–3481 ("the unramified complex `[Φ-1]` in degrees zero and
one"), tex 4551–4573 (row "unramified"), tex 4699–4701 ("the unramified condition at a good place
has the same degree-zero invariants as the full local complex and injects in degree one").

The claims about `U^ur = [W --(Φ−1)--> W]` (`frobCx`, a two-term `CochainComplex` of `k`-modules
indexed by `ℤ`, Mathlib's `HomologicalComplex.double`), each a `Prop` with its proof. All objects
are genuine: Mathlib's `continuousCohomology`, Tau Ceti's `Gal(K_w^ur/K_w) ≃ₜ* ℤ̂` and arithmetic
Frobenius, the restriction `G_{K_w} → Gal(K_w^ur/K_w)`.

Kinds: all PROVED.
-/

open CategoryTheory TauCeti.ContCohomology NumberField IsDedekindDomain
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

open ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction

/-- **Tex 3478–3481 (PROVED): `U^ur` is concentrated in degrees `0, 1`**, with `H⁰ = ker (Φ − 1)`
(`h0Iso`), `H¹ = W ⧸ (Φ − 1)W` (`h1Iso`) and `Hⁿ = 0` otherwise. -/
def UnramifiedComplexHomology : Prop :=
  ∀ (k : Type) [Ring k] (W : Type) [AddCommGroup W] [Module k W] (Φ : W →ₗ[k] W) (n : ℤ),
    n ≠ 0 → n ≠ 1 → Limits.IsZero ((frobCx Φ).homology n)

theorem unramifiedComplexHomology_proof : UnramifiedComplexHomology :=
  fun _ _ _ _ _ Φ n h0 h1 => isZero_homology Φ n h0 h1

/-- **Tex 3478–3481 (PROVED): `H⁰` of `U^ur` is continuous `H⁰` of `ℤ̂`.** For `G ≃ₜ* ℤ̂` and a
discrete continuous `G`-module `W`, `ker (Φ − 1) = W^G` (so `h0Equiv` identifies `H⁰(U^ur)` with
`continuousCohomology 0 X`). -/
def UnramifiedH0Comparison : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : G ≃ₜ* TauCeti.zHat.{0})
    (k : Type) [Ring k] [TopologicalSpace k] (X : TopRep.{0} k G) [ContinuousSMul G X.V]
    [DiscreteTopology X.V], LinearMap.ker (frob e X - 1) = X.ρ.invariants

theorem unramifiedH0Comparison_proof : UnramifiedH0Comparison :=
  fun _ _ _ _ e _ _ _ X _ _ => ker_frob_sub_one e X

/-- **Tex 3478–3481 (PROVED): `H¹` of `U^ur` is continuous `H¹` of `ℤ̂`.** For `G ≃ₜ* ℤ̂` and a
finite discrete continuous `G`-module `W`, `[f] ↦ f(Frob)` is a bijection from Tau Ceti's explicit
continuous `H¹(G, W)` onto `W ⧸ (Φ − 1)W = H¹(U^ur)` (so `h1Equiv` identifies `H¹(U^ur)` with
`continuousCohomology 1 X`). -/
def UnramifiedH1Comparison : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : G ≃ₜ* TauCeti.zHat.{0})
    (k : Type) [Ring k] [TopologicalSpace k] (X : TopRep.{0} k G) [ContinuousSMul G X.V]
    [DiscreteTopology X.V] [Finite X.V], Function.Bijective (h1ToCoinv e X)

theorem unramifiedH1Comparison_proof : UnramifiedH1Comparison :=
  fun _ _ _ _ e _ _ _ X _ _ _ => ⟨h1ToCoinv_injective e X, h1ToCoinv_surjective e X⟩

/-- **(PROVED) Cohomological dimension one: `H²(ℤ̂, W) = 0`** for finite discrete `W`, on
Mathlib's `continuousCohomology 2`. -/
def ZHatH2Vanishes : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [LocallyCompactSpace G] (_ : G ≃ₜ* TauCeti.zHat.{0})
    (k : Type) [Ring k] [TopologicalSpace k] (X : TopRep.{0} k G) [ContinuousSMul G X.V]
    [DiscreteTopology X.V] [Finite X.V], Subsingleton (continuousCohomology 2 X)

theorem zHatH2Vanishes_proof : ZHatH2Vanishes :=
  fun _ _ _ _ _ _ _ e _ _ _ X _ _ _ => subsingleton_continuousCohomology_two e X

/-- **Tex 4699–4701 (PROVED): the unramified condition injects in degree one, with the dimension
of `H⁰`.** At a finite place `w` of a number field `K`, for a finite discrete continuous
`Gal(K_w^ur/K_w)`-module `W` over a finite field `k`: inflation
`H¹(Gal(K_w^ur/K_w), W) → H¹(G_{K_w}, W)` is injective, and its image `H¹_ur` has dimension
`h⁰(Gal(K_w^ur/K_w), W)`. -/
def UnramifiedClassesDim : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k : Type) [Field k]
    [Finite k] [TopologicalSpace k] (X : TopRep.{0} k (GUr K w)) [ContinuousSMul (GUr K w) X.V]
    [DiscreteTopology X.V] [Finite X.V],
    Function.Injective (infl X (resUr K w)) ∧
      Module.finrank k (h1ur X (resUr K w)) = Module.finrank k (continuousCohomology 0 X)

theorem unramifiedClassesDim_proof : UnramifiedClassesDim :=
  fun K _ _ w _ _ _ _ X _ _ _ =>
    ⟨infl_injective X (resUr K w) (resUr_surjective K w), ur_finrank_h1ur K w X⟩

/-- **Tex 4699–4700 (PROVED): the unramified condition has the degree-zero invariants of the full
local complex**: `W^{G_{K_w}} = W^{Gal(K_w^ur/K_w)}`. -/
def UnramifiedSameInvariants : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k : Type) [Ring k]
    [TopologicalSpace k] (X : TopRep.{0} k (GUr K w)),
    (resRep X (resUr K w)).ρ.invariants = X.ρ.invariants

theorem unramifiedSameInvariants_proof : UnramifiedSameInvariants :=
  fun K _ _ w _ _ _ X => invariants_resRep X (resUr K w) (resUr_surjective K w)

end ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
