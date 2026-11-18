import Mathlib

/-!
# RankCounts: the global Galois group `G_{K,S}` and the global prints behind (5.1)

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4519–4533:

> Inflation from `G_{K,S₀}` into `G_{K,S_T}` is injective on `H¹` with trivial coefficients.
> Consequently `h⁰(G_{K,S₀},W) = 2`, `h¹(G_{K,S₀},W) ≤ 4s`. The global Euler characteristic and
> cohomological-dimension statements [Milne, I.4.10 and I.5.1], applied over the imaginary
> quadratic field `K`, give `h⁰ − h¹ + h² = −2`, `H^{>2} = 0`, `h² = h¹ − 4`.

Here `W = E[2] = 𝔽₂²` with trivial action (tex 4479–4480) and `S₀` contains the places above
`2N`, in particular those above `2`.

Lane RC6 (`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`)
takes these counts as the fields `h0_eq : h0 = 2` and `euler : (h0 : ℤ) - h1 + h2 = -2` of its
structure `ResidualRankCounts`, without a Galois group, because "`G_{K,S}` … not available in
Mathlib". This file supplies:

* `unramifiedOutside K S` (genuine): the maximal extension `K_S` of `K` inside an algebraic closure
  that is unramified at every prime outside `S`, as the supremum of the finite Galois subextensions
  unramified outside `S` (ramification index one at every prime above a prime `v ∉ S`); and
  `GaloisGroupS K S = Gal(K_S/K)` with Mathlib's Krull topology. No condition is imposed at
  infinite places: as in Milne, `S` is understood to contain the archimedean places.
* Two printed leaves over these genuine objects and Mathlib's `continuousCohomology`, specialized
  to totally complex `K` and to `𝔽₂`-modules (the case used, tex 4526–4531): Milne ADT I.4.10
  (vanishing in degrees `> 2` without real places) and Milne ADT I.5.1 (Tate's global
  Euler–Poincaré characteristic).
* PROVED consequences: `H⁰` of a trivial representation is the module (any topological group); an
  imaginary quadratic field has one complex place; and, from the two prints, for the trivial
  module `W = 𝔽₂²` over an imaginary quadratic field the exact counts `h⁰ = 2`,
  `h⁰ − h¹ + h² = −2`, `H^{>2} = 0` (`globalCounts_of_prints`), which are RC6's fields `h0_eq` and
  `euler` with `h_i := dim H^i(G_{K,S}, W)`.

Conventions (same as RC6's `LocalPrints.lean`): Mathlib's `continuousCohomology` is the
cohomology of homogeneous continuous cochains; for a profinite group and a discrete module it is the
usual continuous cochain cohomology (GLUE: standard comparison). Mathlib's `ContRepresentation` does
not require the action to be jointly continuous, so the prints carry that hypothesis (a discrete
`G_S`-module in Milne's sense).

Kinds: `IsUnramifiedOutside`, `unramifiedOutside`, `GaloisGroupS`, `trivialRepS`: genuine
definitions. `MilneADT_I_4_10_totallyComplex`, `MilneADT_I_5_1_totallyComplex`: PRINT, locator as
the manuscript cites it (tex 4526 `\cite[I.4.10 and I.5.1]{milne}`), UNVERIFIED (no print read).
Everything else: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open NumberField IsDedekindDomain CategoryTheory

/-! ### The maximal extension unramified outside `S` -/

section Defs

variable (K : Type) [Field K] [NumberField K]

/-- A subextension `L` of `K̄/K` is **unramified outside `S`** (a set of finite primes of `K`) if
every prime ideal `Q` of the integral closure of `𝒪_K` in `L` lying over a prime `v ∉ S` has
ramification index one over `𝒪_K`. (For finite `L/K` this is the usual notion; no condition at the
infinite places.) -/
def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 K)))
    (L : IntermediateField K (AlgebraicClosure K)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ Q : Ideal (integralClosure (𝓞 K) L), Q.IsPrime →
    Q.LiesOver v.asIdeal → Q.ramificationIdx (𝓞 K) = 1

/-- **`K_S`**: the maximal subextension of `K̄/K` unramified outside `S`, the compositum of all
finite subextensions unramified outside `S` (Milne ADT I §4, notation `K_S`). We take the
supremum over the finite *Galois* subextensions unramified outside `S`: this is the same field,
since the maximal extension unramified outside `S` is Galois over `K` and is the union of its
finite Galois subextensions, each of which is unramified outside `S` (standard); with this form
`K_S/K` is visibly normal (`Inflation.lean`). -/
def unramifiedOutside (S : Set (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K (AlgebraicClosure K) :=
  ⨆ (L : IntermediateField K (AlgebraicClosure K))
    (_ : FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S L), L

/-- **`G_S = G_{K,S} = Gal(K_S/K)`**, with Mathlib's Krull topology (a profinite group). -/
abbrev GaloisGroupS (S : Set (HeightOneSpectrum (𝓞 K))) : Type :=
  unramifiedOutside K S ≃ₐ[K] unramifiedOutside K S

example (S : Set (HeightOneSpectrum (𝓞 K))) : IsTopologicalGroup (GaloisGroupS K S) :=
  inferInstance

end Defs

/-- The trivial representation of a topological group `G` on an `𝔽₂`-vector space `V`, as an
object of `TopRep (ZMod 2) G`. -/
abbrev trivialRepS (G : Type) [Group G] [TopologicalSpace G] (V : Type) [AddCommGroup V]
    [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul (ZMod 2) V] : TopRep (ZMod 2) G :=
  TopRep.of (ContRepresentation.trivial (ZMod 2) G V)

/-! ### The printed leaves -/

/-- **PRINT — Milne, *Arithmetic Duality Theorems*, Ch. I, Theorem 4.10, as cited at tex 4526
(`\cite[I.4.10 and I.5.1]{milne}`, "cohomological-dimension statements"), specialized to totally
complex `K` and finite discrete `𝔽₂`-modules.** UNVERIFIED (no print read; the subpart of 4.10
carrying the statement is not checked).

Form used (tex 4529, `H^{>2} = 0`): for a number field `K` and a finite set `S` of primes containing
those above `#M = 2^{dim M}` (and, implicitly, the archimedean places), and a finite discrete
`G_S`-module `M`, `H^r(G_S, M) → ⊕_{v real} H^r(K_v, M)` is an isomorphism for `r ≥ 3`; when `K` has
no real place, `H^r(G_S, M) = 0` for `r ≥ 3`. -/
def MilneADT_I_4_10_totallyComplex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
      (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      ∀ M : TopRep.{0} (ZMod 2) (GaloisGroupS K S), Finite M → DiscreteTopology M →
        Continuous (fun x : GaloisGroupS K S × M => M.ρ x.1 x.2) →
        ∀ n, 2 < n → Subsingleton (continuousCohomology n M)

/-- **PRINT — Milne, *Arithmetic Duality Theorems*, Ch. I, Theorem 5.1 (Tate's global
Euler–Poincaré characteristic), as cited at tex 4526 (`\cite[I.4.10 and I.5.1]{milne}`),
specialized to totally complex `K` and finite discrete `𝔽₂`-modules.** UNVERIFIED (no print read).

Milne: for `S` finite containing the archimedean places and the primes dividing `#M`, and `M` a
finite `G_S`-module, the groups `H^r(G_S, M)` are finite and
`χ(G_S, M) = [H⁰][H²]/[H¹] = ∏_{v arch} [H⁰(G_v, M)] / |[M]|_v`.
For `K` totally complex every archimedean `v` is complex, `G_v = 1`, `H⁰(G_v, M) = M` and
`|[M]|_v = [M]²`; so `χ = [M]^{-r₂}` with `r₂` the number of complex places. For an `𝔽₂`-module
`M` of dimension `n`, `[M] = 2ⁿ` and in dimensions `h⁰ − h¹ + h² = −r₂ n`. (The specialization
restricts only the hypotheses; the formula is the print's, evaluated.) The finiteness of
`H⁰, H¹, H²` is part of the printed setting of Theorem 5.1. -/
def MilneADT_I_5_1_totallyComplex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
      (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      ∀ M : TopRep.{0} (ZMod 2) (GaloisGroupS K S), Finite M → DiscreteTopology M →
        Continuous (fun x : GaloisGroupS K S × M => M.ρ x.1 x.2) →
        Module.Finite (ZMod 2) (continuousCohomology 0 M) ∧
        Module.Finite (ZMod 2) (continuousCohomology 1 M) ∧
        Module.Finite (ZMod 2) (continuousCohomology 2 M) ∧
        ((Module.finrank (ZMod 2) (continuousCohomology 0 M) : ℤ) -
            Module.finrank (ZMod 2) (continuousCohomology 1 M) +
            Module.finrank (ZMod 2) (continuousCohomology 2 M) =
          -((InfinitePlace.nrComplexPlaces K : ℤ) * Module.finrank (ZMod 2) M))

/-! ### PROVED consequences -/

/-- `H⁰` of a trivial representation of any topological group is the whole module.
PROVED (Mathlib's `ContinuousCohomology.zeroIso : H⁰(G, A) ≅ A^G`). Used at tex 4522
(`h⁰(G_{K,S₀}, W) = 2` for `W = E[2]` rational of rank two). -/
theorem finrank_H0_trivialRepS (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul (ZMod 2) V] :
    Module.finrank (ZMod 2) (continuousCohomology 0 (trivialRepS G V)) =
      Module.finrank (ZMod 2) V := by
  have e := (ContinuousCohomology.zeroIso (trivialRepS G V)).toContinuousLinearEquiv
  rw [e.toLinearEquiv.finrank_eq]
  have htop : (trivialRepS G V).ρ.invariants = ⊤ := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    rw [ContRepresentation.mem_invariants]
    intro g
    rfl
  change Module.finrank (ZMod 2) ((trivialRepS G V).ρ.invariants) = _
  rw [htop, finrank_top]

/-- The trivial representation on a discrete module is a discrete `G`-module: the action map
`G × V → V` is the second projection, hence continuous. PROVED. -/
theorem continuous_trivialRepS_action (G : Type) [Group G] [TopologicalSpace G]
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul (ZMod 2) V] :
    Continuous (fun x : G × trivialRepS G V => (trivialRepS G V).ρ x.1 x.2) :=
  continuous_snd

/-- An imaginary quadratic field (degree two, no real place) has exactly one complex place.
PROVED (`r₁ + 2 r₂ = [K : ℚ]`). Used at tex 4526 ("over the imaginary quadratic field `K`"). -/
theorem nrComplexPlaces_eq_one_of_imaginaryQuadratic (K : Type) [Field K] [NumberField K]
    (h2 : Module.finrank ℚ K = 2) (hK : IsTotallyComplex K) :
    InfinitePlace.nrComplexPlaces K = 1 := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [NumberField.nrRealPlaces_eq_zero_iff.mpr hK, h2] at h
  omega

/-- **The global counts of tex 4521–4531, from the prints.** PROVED from
`MilneADT_I_4_10_totallyComplex` and `MilneADT_I_5_1_totallyComplex`.

For an imaginary quadratic field `K`, a finite set `S` of primes of `K` containing those above `2`
(for instance `S₀`, the places above `2N`, the moving prime and the derivative primes, tex 4468),
and the trivial module `W = 𝔽₂²` (`W = E[2]`, tex 4479–4480), with
`h_i = dim_{𝔽₂} H^i(G_{K,S}, W)`:

* `h⁰ = 2` (tex 4522) — RC6's field `h0_eq : h0 = 2`;
* `h⁰ − h¹ + h² = −2` (tex 4528) — RC6's field `euler : (h0 : ℤ) - h1 + h2 = -2`
  (`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`, structure `ResidualRankCounts`);
* `H^n = 0` for `n > 2` (tex 4529, `H^{>2} = 0`);
* `H⁰, H¹, H²` are finite-dimensional.

The weaker count `h² = h¹ − 4` (tex 4529) and the totals `8s − 2`, `8s + 2` are RC6's PROVED
`global_estimate`/`global_estimate_weak` from these two fields. -/
def GlobalCountsImagQuad : Prop :=
  MilneADT_I_4_10_totallyComplex → MilneADT_I_5_1_totallyComplex →
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
      (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V]
        [IsTopologicalAddGroup V] [ContinuousSMul (ZMod 2) V], Finite V → DiscreteTopology V →
        Module.finrank (ZMod 2) V = 2 →
        let W := trivialRepS (GaloisGroupS K S) V
        Module.finrank (ZMod 2) (continuousCohomology 0 W) = 2 ∧
        ((Module.finrank (ZMod 2) (continuousCohomology 0 W) : ℤ) -
            Module.finrank (ZMod 2) (continuousCohomology 1 W) +
            Module.finrank (ZMod 2) (continuousCohomology 2 W) = -2) ∧
        (∀ n, 2 < n → Subsingleton (continuousCohomology n W)) ∧
        Module.Finite (ZMod 2) (continuousCohomology 0 W) ∧
        Module.Finite (ZMod 2) (continuousCohomology 1 W) ∧
        Module.Finite (ZMod 2) (continuousCohomology 2 W)

theorem globalCountsImagQuad_proof : GlobalCountsImagQuad := by
  intro h410 h51 K _ _ h2 hK S hS hS2 V _ _ _ _ _ hVfin hVdisc hV W
  have hfinW : Finite W := hVfin
  have hdiscW : DiscreteTopology W := hVdisc
  have hcont := continuous_trivialRepS_action (GaloisGroupS K S) V
  obtain ⟨f0, f1, f2, he⟩ := h51 K hK S hS hS2 W hfinW hdiscW hcont
  have hr2 := nrComplexPlaces_eq_one_of_imaginaryQuadratic K h2 hK
  have h0 : Module.finrank (ZMod 2) (continuousCohomology 0 W) = 2 := by
    rw [finrank_H0_trivialRepS]; exact hV
  refine ⟨h0, ?_, h410 K hK S hS hS2 W hfinW hdiscW hcont, f0, f1, f2⟩
  rw [he, hr2]
  have hW : Module.finrank (ZMod 2) W = 2 := hV
  rw [hW]
  norm_num

/-- Non-vacuity of the hypotheses on `S` in the prints and in `GlobalCountsImagQuad`: the set of
primes of `K` above `2` is finite (and trivially contains the primes above `2`), so it is an
admissible `S`; so is any finite superset such as `S₀`. PROVED (`Ideal.finite_factors`). -/
theorem primesAboveTwo_finite (K : Type) [Field K] [NumberField K] :
    {v : HeightOneSpectrum (𝓞 K) | (2 : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(2 : 𝓞 K)} ≠ 0 := by simp
  refine (Ideal.finite_factors h).subset ?_
  intro v hv
  simpa [Ideal.span_singleton_le_iff_mem] using hv

end ZInQ.Contrib.CloudB3RC53.RankCounts
