import ZInQKernel.Contrib.CloudB3RC53.UnramifiedComplex.Inflation
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalConditions

/-!
# UnramifiedComplex: `U_w^ur` at a finite place of a number field

Manuscript `diophantine_zq.tex`, tex 3478–3481, 4551–4573 (row "unramified, `w ∤ 2`": `4`), and
4699–4701.

For a number field `K` and a finite place `w`, `G = Gal(K_w^ur/K_w)` is `GUr K w`
(`RankCounts/LocalConditions.lean`), `eUr : G ≃ₜ* ℤ̂` is Tau Ceti's
`maximalUnramifiedGaloisGroupEquivZHat`, under which `frobElt` is Tau Ceti's arithmetic Frobenius
`maximalUnramifiedFrobenius` (`frobElt_eUr`), and `resUr : G_{K_w} → G` is restriction (continuous,
surjective).

For a finite discrete continuous `G`-module `W` (`X : TopRep k G`):

* `urCx K w X = [W --(Φ_w − 1)--> W]` (degrees `0, 1`), `urH0Equiv`, `urH1Equiv`;
* `ur_subsingleton_H2 : H²(G, W) = 0`;
* `ur_finrank_h1ur : dim H¹_ur(K_w, W) = h⁰(G, W)` with `H¹_ur ⊆ H¹(G_{K_w}, W)` the image of
  inflation.

Non-vacuity on the residual module `W = 𝔽₂²` (trivial action): `finrank_urCx_W2`
(`h⁰ + h¹ = 4` computed on the complex, Elliot's table row) and `finrank_h1ur_W2`
(`dim H¹_ur = 2`).

Kinds: everything PROVED.
-/

open CategoryTheory TauCeti.ContCohomology NumberField IsDedekindDomain
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.UnramifiedComplex

open ZInQ.Contrib.CloudB3RC53.RankCounts

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

attribute [local instance] TopRep.distribMulAction

/-- `Gal(K_w^ur/K_w) ≃ₜ* ℤ̂` (Tau Ceti), sending the arithmetic Frobenius to `1`. -/
abbrev eUr : GUr K w ≃ₜ* TauCeti.zHat.{0} :=
  TauCeti.maximalUnramifiedGaloisGroupEquivZHat (w.adicCompletion K)
    (AlgebraicClosure (w.adicCompletion K))

/-- The Frobenius of `frobCx` at `w` is Tau Ceti's arithmetic Frobenius of `K_w^ur/K_w`. -/
theorem frobElt_eUr : frobElt (eUr K w) =
    TauCeti.maximalUnramifiedFrobenius (w.adicCompletion K)
      (AlgebraicClosure (w.adicCompletion K)) := by
  simp [frobElt, eUr]

/-- Restriction `G_{K_w} → Gal(K_w^ur/K_w)`. -/
def resUr : Field.absoluteGaloisGroup (w.adicCompletion K) →ₜ* GUr K w :=
  ⟨AlgEquiv.restrictNormalHom _, InfiniteGalois.restrictNormalHom_continuous _⟩

/-- Restriction to `K_w^ur` is surjective. -/
theorem resUr_surjective : Function.Surjective (resUr K w) :=
  AlgEquiv.restrictNormalHom_surjective _

set_option synthInstance.maxHeartbeats 400000 in
/-- `Gal(K_w^ur/K_w)` is locally compact. -/
theorem locallyCompactSpace_GUr : LocallyCompactSpace (GUr K w) :=
  have : T2Space (GUr K w) := krullTopology_t2
  have : WeaklyLocallyCompactSpace (GUr K w) :=
    ⟨fun _ => ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

section General

variable {k : Type} [Ring k] [TopologicalSpace k] (X : TopRep.{0} k (GUr K w))

/-- **Elliot's unramified local condition `U_w^ur = [W --(Φ_w−1)--> W]`** at a finite place `w`
of `K`, for an unramified coefficient module `W` (a continuous representation of
`Gal(K_w^ur/K_w)`), with `Φ_w` the arithmetic Frobenius (`frobElt_eUr`). -/
abbrev urCx : CochainComplex (ModuleCat.{0} k) ℤ := frobCx (frob (eUr K w) X)

variable [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V]

/-- `H⁰(U_w^ur) ≅ H⁰(Gal(K_w^ur/K_w), W)`. -/
def urH0Equiv : (urCx K w X).homology 0 ≃ₗ[k] continuousCohomology 0 X := h0Equiv (eUr K w) X

/-- `H¹(U_w^ur) ≅ H¹(Gal(K_w^ur/K_w), W)` for finite `W`. -/
def urH1Equiv [Finite X.V] : (urCx K w X).homology 1 ≃+ continuousCohomology 1 X :=
  h1Equiv (eUr K w) X

/-- `H²(Gal(K_w^ur/K_w), W) = 0` for finite `W`. -/
theorem ur_subsingleton_H2 [Finite X.V] : Subsingleton (continuousCohomology 2 X) :=
  have := locallyCompactSpace_GUr K w
  subsingleton_continuousCohomology_two (eUr K w) X

/-- `dim H¹_ur(K_w, W) = h⁰(Gal(K_w^ur/K_w), W)` inside `H¹(G_{K_w}, W)`, over a finite field. -/
theorem ur_finrank_h1ur {k : Type} [Field k] [Finite k] [TopologicalSpace k]
    (X : TopRep.{0} k (GUr K w)) [ContinuousSMul (GUr K w) X.V] [DiscreteTopology X.V]
    [Finite X.V] :
    Module.finrank k (h1ur X (resUr K w)) = Module.finrank k (continuousCohomology 0 X) :=
  finrank_h1ur (resUr K w) (eUr K w) X (resUr_surjective K w)

end General

section Trivial

/-- `W = 𝔽₂²` with trivial action, the residual coefficient module of tex 4479–4480. -/
abbrev W2 : TopRep (ZMod 2) (GUr K w) := trivialRepS (GUr K w) (Fin 2 → ZMod 2)

/-- The trivial action is continuous. -/
theorem continuousSMul_W2 :
    letI := TopRep.distribMulAction (W2 K w)
    ContinuousSMul (GUr K w) (W2 K w).V :=
  letI := TopRep.distribMulAction (W2 K w)
  ⟨continuous_snd⟩

/-- On the trivial module the Frobenius is the identity. -/
theorem frob_W2 : frob (eUr K w) (W2 K w) = 1 := LinearMap.ext fun _ => rfl

/-- **Non-vacuity, and Elliot's table row "unramified": `Σ_a h^a(U_w^ur) = 4`** for `W = 𝔽₂²`
(tex 4565–4566), computed on the complex itself: `Φ = 1`, so both cohomology groups are `W`. -/
theorem finrank_urCx_W2 :
    Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 0) +
      Module.finrank (ZMod 2) ((urCx K w (W2 K w)).homology 1) = 4 := by
  rw [(h0Iso _).toLinearEquiv.finrank_eq, (h1Iso _).toLinearEquiv.finrank_eq]
  rw [frob_W2, sub_self, LinearMap.ker_zero, LinearMap.range_zero, finrank_top,
    (Submodule.quotEquivOfEqBot ⊥ rfl).finrank_eq]
  simp

/-- **Non-vacuity of the inflation statement:** for `W = 𝔽₂²`, `dim H¹_ur(K_w, W) = 2`. -/
theorem finrank_h1ur_W2 : Module.finrank (ZMod 2) (h1ur (W2 K w) (resUr K w)) = 2 := by
  let _ := TopRep.distribMulAction (W2 K w)
  have := continuousSMul_W2 K w
  rw [ur_finrank_h1ur, finrank_H0_trivialRepS]
  simp

end Trivial

end ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
