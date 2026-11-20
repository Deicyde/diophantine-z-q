import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Model

/-!
# The shape inputs of the starting models of the genuine `C_∅`

Manuscript `diophantine_zq.tex`, tex 4385–4451 (finite free models and the inner limit),
4520–4550 (the global Euler characteristic).

Lane RC32's starting models (`exists_genuine_st0_eventually`) take, for the genuine `C_∅` at the
stages: finite residual cohomology (`hfin`), residual ranks bounded by one `B` (`hB`), vanishing
outside degrees `[0, 3]` (`hout`), and at `U`-many stages Euler characteristic zero (`heul`) and
`h⁰ < h¹` (`hpos`). **`st0Shape_of_inputs`** (PROVED) produces all five from:

* a reference family of residual ranks `Rk` with the contributor's producer bounds (`hRef`: one
  `B`, vanishing outside `[0, 3]`; PROVED for the standard-old stage Selmer family by
  `standardOld_producerBounds`, with finiteness from `stageSelmer_residualCohomologyFinite`);
* **`GenCxResidualIso Rk`** (named): the genuine `C_∅` has finite residual cohomology with the
  reference ranks;
* **`StageEulerZero U Rk`** (PRINT) and **`StageH0LtH1 U Rk`** (named).

**`exists_genuine_st0_of_inputs`** (PROVED) then gives the starting models.

Kinds: definitions, PRINT and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.St0Shape

open Filter IsLocalRing NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
  ZInQ.Contrib.CloudB3RC53.RankCounts

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  [∀ s, TopologicalSpace (StageRing s)]
  (M : ℕ → Type) [∀ s, AddCommGroup (M s)] [∀ s, Module (StageRing s) (M s)]
  [∀ s, DistribMulAction (GKS K S) (M s)] [∀ s, SMulCommClass (GKS K S) (StageRing s) (M s)]
  [∀ s, TopologicalSpace (M s)] [∀ s, DiscreteTopology (M s)]
  [∀ s, ContinuousSMul (GKS K S) (M s)]
  (Δ : ∀ s, LocalConditions (StageRing s) (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) (M s))
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : ∀ s, (j : ι × Bool) → TopRep.{0} (StageRing s) (GUr K (place j).1))
  (EU : ∀ s j, SplitInclusion (genuineUq K S (StageRing s) (place j) (X s j))
    (genuineLq K S (StageRing s) (M s) (place j)))

/-- **The genuine `C_∅` against a reference family of residual ranks** (named input; tex
4385–4414): at every stage `s ≠ 0` the residual cohomology of the genuine `C_∅` is finite and
has the reference ranks `Rk s n`.

Reason for naming: the reference family is the standard-old stage Selmer family
`selCx (actualSelData … standardOldAt …)` of the contributor's residual results, indexed by all
places of `S` with Galois local conditions; the genuine `C_∅ = suppCxS ∅` is indexed by
`Places K S₀ ⊕ (ι × Bool)`. The comparison is a mechanical reindexing isomorphism of the
residual complexes (`S = S₀ ∪ range place`, `place` injective, the old conditions `Δ ↔ c`, the
unramified Frobenius complexes `frobCx ↔ urAt`), estimated at about three hours; doing it would
remove this input, with finiteness from `stageSelmer_residualCohomologyFinite` and the ranks
from the reference family. Kind: definition (named input). -/
structure GenCxResidualIso (Rk : ℕ → ℤ → ℕ) : Prop where
  /-- the residual cohomology of the genuine `C_∅` is finite -/
  finite : ∀ s [NeZero s] n, Module.Finite (ResidueField (StageRing s))
    (residualCohomologyAt (genCx K S₀ S M Δ place X EU s ∅) n)
  /-- its residual ranks are the reference ranks -/
  rank_eq : ∀ s [NeZero s] n, genResRank K S₀ S M Δ place X EU s n = Rk s n

/-- **The Euler characteristic of the residual Selmer cone is zero at `U`-many stages** (GLUE,
derived from printed results; used at tex 4520–4550 for the global term). As a statement about a
free rank function `Rk` it is not a reading of a print: it is the Euler characteristic of the
residual Selmer cone, derived at the actual ranks from J. S. Milne, *Arithmetic Duality Theorems*,
2nd ed., 2006, together with the Euler characteristics of the local conditions and the long exact
sequence of the cone:
* I, Theorem 5.1, p. 67 (setting p. 66): "THEOREM 5.1 With the above definition,
  χ(G_S, M) = ∏_{v arch} [H⁰(G_v, M)] / |[M]|_v." For the residual module `W = E[2]` over the
  imaginary quadratic `K` (one complex place, `|[W]|_v = 4² = 16`) it gives `χ = 1/4`, i.e.
  `h⁰ − h¹ + h² = −2` (tex 4525–4529);
* I, Theorem 4.10, pp. 56–57: "(c) For r ≥ 3, β^r is a bijection H^r(G_S, M) → ∏_{v real}
  H^r(K_v, M)" (so the global cohomology vanishes in degrees `≥ 3` for totally imaginary `K`);
* I, Theorem 2.8, p. 31: "Let M be a finite G-module of order m relatively prime to char(K).
  Then χ(G, M) = (R: mR)^{-1}" (the local terms, tex 4546–4549).
Kind: definition (the statement; GLUE derived from the printed results, at the actual ranks). -/
def StageEulerZero (U : Ultrafilter ℕ) (Rk : ℕ → ℤ → ℕ) : Prop :=
  ∀ᶠ s in (U : Filter ℕ), Rk s 0 + Rk s 2 = Rk s 1 + Rk s 3

/-- **`h⁰ < h¹` at `U`-many stages** (named input; tex 4391–4406): the residual `H¹` of the
reference family exceeds its `H⁰`. Kind: definition (named input). -/
def StageH0LtH1 (U : Ultrafilter ℕ) (Rk : ℕ → ℤ → ℕ) : Prop :=
  ∀ᶠ s in (U : Filter ℕ), Rk s 0 < Rk s 1

variable {K S₀ S M Δ place X EU}

/-- `genResRank'` is the reference rank at the stages `s ≠ 0` (PROVED). -/
theorem genResRank'_eq {Rk : ℕ → ℤ → ℕ} (hI : GenCxResidualIso K S₀ S M Δ place X EU Rk) {s : ℕ}
    (hs : s ≠ 0) (n : ℤ) : genResRank' K S₀ S M Δ place X EU s n = Rk s n := by
  have : NeZero s := ⟨hs⟩
  unfold genResRank'
  rw [dite_eq_right hs]
  exact hI.rank_eq s n

/-- **The shape inputs of the starting models** (PROVED from the named inputs): the
hypotheses `hfin`, `hB`, `hout`, `heul`, `hpos` of `exists_genuine_st0_eventually`. -/
theorem st0Shape_of_inputs (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    {Rk : ℕ → ℤ → ℕ}
    (hRef : ∃ B : ℕ, (∀ s [NeZero s] (n : ℤ), n < 0 ∨ 3 < n → Rk s n = 0) ∧
      (∀ s [NeZero s] (n : ℤ), Rk s n ≤ B))
    (hI : GenCxResidualIso K S₀ S M Δ place X EU Rk) (hE : StageEulerZero U Rk)
    (hP : StageH0LtH1 U Rk) :
    (∀ s [NeZero s] n, Module.Finite (ResidueField (StageRing s))
      (residualCohomologyAt (genCx K S₀ S M Δ place X EU s ∅) n)) ∧
    ∃ B : ℕ, (∀ s n, genResRank' K S₀ S M Δ place X EU s n ≤ B) ∧
      (∀ s n, n < 0 ∨ 3 < n → genResRank' K S₀ S M Δ place X EU s n = 0) ∧
      (∀ᶠ s in (U : Filter ℕ), genResRank' K S₀ S M Δ place X EU s 0 +
        genResRank' K S₀ S M Δ place X EU s 2 =
          genResRank' K S₀ S M Δ place X EU s 1 + genResRank' K S₀ S M Δ place X EU s 3) ∧
      (∀ᶠ s in (U : Filter ℕ),
        genResRank' K S₀ S M Δ place X EU s 0 < genResRank' K S₀ S M Δ place X EU s 1) := by
  obtain ⟨B, hout, hB⟩ := hRef
  have hne : ∀ᶠ s in (U : Filter ℕ), s ≠ 0 :=
    hU (Set.Finite.compl_mem_cofinite (Set.finite_singleton 0))
  refine ⟨hI.finite, B, fun s n => ?_, fun s n hn => ?_, ?_, ?_⟩
  · by_cases hs : s = 0
    · unfold genResRank'
      simp [hs]
    · have : NeZero s := ⟨hs⟩
      rw [genResRank'_eq hI hs]
      exact hB s n
  · by_cases hs : s = 0
    · unfold genResRank'
      simp [hs]
    · have : NeZero s := ⟨hs⟩
      rw [genResRank'_eq hI hs]
      exact hout s n hn
  · filter_upwards [hE, hne] with s h hs
    rw [genResRank'_eq hI hs, genResRank'_eq hI hs, genResRank'_eq hI hs, genResRank'_eq hI hs]
    exact h
  · filter_upwards [hP, hne] with s h hs
    rw [genResRank'_eq hI hs, genResRank'_eq hI hs]
    exact h

/-- **The starting models of the genuine chains from the named inputs** (PROVED;
tex 4391–4414). -/
theorem exists_genuine_st0_of_inputs (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (hflat : ∀ s [NeZero s] n, Module.Flat (StageRing s) ((genCx K S₀ S M Δ place X EU s ∅).X n))
    {Rk : ℕ → ℤ → ℕ}
    (hRef : ∃ B : ℕ, (∀ s [NeZero s] (n : ℤ), n < 0 ∨ 3 < n → Rk s n = 0) ∧
      (∀ s [NeZero s] (n : ℤ), Rk s n ≤ B))
    (hI : GenCxResidualIso K S₀ S M Δ place X EU Rk) (hE : StageEulerZero U Rk)
    (hP : StageH0LtH1 U Rk)
    (z : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).X 1)
    (hz : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl (z s) = 0)
    (lam : ∀ s, (genCx K S₀ S M Δ place X EU s ∅).X 2 →ₗ[StageRing s] StageRing s)
    (hlam : ∀ s, lam s ∘ₗ (genCx K S₀ S M Δ place X EU s ∅).d 1 2 rfl = 0) :
    ∃ m0 m1 m2 : ℕ, ∀ᶠ s in (U : Filter ℕ),
      Nonempty (CMState m0 m1 m2 (genCx K S₀ S M Δ place X EU s ∅) 0) := by
  obtain ⟨hfin, B, hB, hout, heul, hpos⟩ := st0Shape_of_inputs U hU hRef hI hE hP
  exact exists_genuine_st0_eventually K S₀ S M Δ place X EU U hU hflat hfin hB hout heul hpos
    z hz lam hlam

end ZInQ.Contrib.CloudB3E2.St0Shape
