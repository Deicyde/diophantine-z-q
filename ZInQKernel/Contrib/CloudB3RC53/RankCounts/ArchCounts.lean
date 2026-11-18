import ZInQKernel.Contrib.OneProof.RC.Limits.LocalPrints
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ClassFormation

/-!
# RankCounts: the archimedean allowance of (5.1) (`arch_le`)

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4584–4591:

> There are no real places of `K`. Its one complex place has full cohomology `W` in degree zero
> only. … even retaining both an ordinary full term and a full local condition costs at most four
> additional generators.

For a complex place `w` of `K` with completion `K_w`, `archTotal K w` is the total residual
dimension of the archimedean terms retained in the Selmer cone: the full local complex
`RΓ(K_w, W)` and the full local condition, each with residual dimensions
`h^i(K_w, W) = dim H^i(G_{K_w}, W)` (`i = 0, 1, 2`), `W = 𝔽₂²` trivial, over Mathlib's continuous
cohomology of the genuine absolute Galois group of `K_w`. Since `G_{K_w}` is trivial (Tau Ceti's
`subsingleton_fieldAbsoluteGaloisGroup_of_isComplex`), `H¹ = H² = 0` (Tau Ceti's explicit low-degree
cohomology and its comparison with Mathlib's) and `H⁰ = W`; so `archTotal K w = 2 + 2 = 4` and RC6's
field `arch_le : archTot ≤ 4` holds (`archLe_proof`, from `archTotal_eq_four`). Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open CategoryTheory TauCeti.ContCohomology ZInQ.Manuscript.RC.Limits NumberField

section TrivialGroup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Subsingleton G]
  (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul (ZMod 2) V] [DiscreteTopology V]

/-- The trivial representation of `G` on `V`. -/
abbrev trivRepG : TopRep (ZMod 2) G := TopRep.of (ContRepresentation.trivial (ZMod 2) G V)

/-- `H¹` of a trivial group vanishes. PROVED (Tau Ceti). -/
theorem subsingleton_H1_trivialGroup : Subsingleton (continuousCohomology 1 (trivRepG (G := G) V)) :=
  letI := TopRep.distribMulAction (trivRepG (G := G) V)
  haveI : DiscreteTopology (trivRepG (G := G) V).V := by assumption
  haveI : ContinuousSMul G (trivRepG (G := G) V).V := ⟨continuous_snd⟩
  (trivRepG (G := G) V).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.toEquiv.subsingleton

/-- `H²` of a trivial group vanishes. PROVED (Tau Ceti). -/
theorem subsingleton_H2_trivialGroup [LocallyCompactSpace G] :
    Subsingleton (continuousCohomology 2 (trivRepG (G := G) V)) :=
  letI := TopRep.distribMulAction (trivRepG (G := G) V)
  haveI : DiscreteTopology (trivRepG (G := G) V).V := by assumption
  haveI : ContinuousSMul G (trivRepG (G := G) V).V := ⟨continuous_snd⟩
  (trivRepG (G := G) V).explicitH2AddEquivContinuousCohomologyOfDiscrete.symm.toEquiv.subsingleton

end TrivialGroup

variable (K : Type) [Field K] [NumberField K]

/-- The total residual dimension of the archimedean terms at the complex place `w`: the full local
complex and the full local condition, `2 · Σ_{i ≤ 2} dim H^i(G_{K_w}, 𝔽₂²)` (tex 4584–4591). -/
def archTotal (w : InfinitePlace K) : ℕ :=
  2 * ∑ i ∈ Finset.range 3, Module.finrank (ZMod 2)
    (continuousCohomology i (trivialGaloisRep w.Completion (Fin 2 → ZMod 2)))

omit [NumberField K] in
/-- **The archimedean allowance (tex 4584–4591): at a complex place, `archTotal = 4`.** PROVED. -/
theorem archTotal_eq_four (w : InfinitePlace K) (hw : w.IsComplex) : archTotal K w = 4 := by
  have := TauCeti.ClassFieldTheory.subsingleton_fieldAbsoluteGaloisGroup_of_isComplex w hw
  have h0 := finrank_H0_trivialGaloisRep w.Completion (Fin 2 → ZMod 2)
  have h1 : Module.finrank (ZMod 2)
      (continuousCohomology 1 (trivialGaloisRep w.Completion (Fin 2 → ZMod 2))) = 0 := by
    have := subsingleton_H1_trivialGroup (G := Field.absoluteGaloisGroup w.Completion)
      (Fin 2 → ZMod 2)
    exact Module.finrank_zero_of_subsingleton
  have h2 : Module.finrank (ZMod 2)
      (continuousCohomology 2 (trivialGaloisRep w.Completion (Fin 2 → ZMod 2))) = 0 := by
    have := subsingleton_H2_trivialGroup (G := Field.absoluteGaloisGroup w.Completion)
      (Fin 2 → ZMod 2)
    exact Module.finrank_zero_of_subsingleton
  simp only [archTotal, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, h2]
  simp

/-- **RC6's field `arch_le : archTot ≤ 4`** for `archTot = archTotal K w`, `w` the complex place of
the imaginary quadratic `K` (tex 4584–4591). PROVED. -/
def ArchLe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : InfinitePlace K), w.IsComplex → archTotal K w ≤ 4

theorem archLe_proof : ArchLe := fun K _ _ w hw => (archTotal_eq_four K w hw).le

end ZInQ.Contrib.CloudB3RC53.RankCounts
