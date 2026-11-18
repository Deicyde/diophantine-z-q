import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Inverse
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Cochains

/-!
# Continuous cochains, Route A: (A6) the other team's `contCochains` and `C(Gⁿ, X)`

Connects RC26's continuous inhomogeneous cochains `contCochains k G M` (RC/SelmerComplex/: the
continuous functions `(Fin n → G) → M` inside Mathlib's inhomogeneous cochains of
`Rep.ofDistribMulAction k G M`) with the continuous maps `C(Fin n → G, X)` of `Inverse.lean`, for
the topological representation `X = topRepOf k G M`. All `PROVED`:

* `contRep`, `topRepOf`: the continuous representation of `G` on a topological `G`-module `M`
  (each `g • ·` continuous) and the corresponding `TopRep`;
* `hcont_topRepOf`: the hypothesis `hcont` of `Inverse.lean` for `topRepOf M` is the joint
  continuity of the action, `ContinuousSMul G M`. This is exactly the standing hypothesis of
  `contCochains`; for a discrete `M` it is the continuity of the action in the sense of profinite
  cohomology (open stabilizers). For a discrete `M` over a discrete ring the remaining `TopRep`
  hypotheses hold too (`isTopologicalAddGroup_of_discrete`, `continuousSMul_of_discrete`);
* `contCochainEquiv n : contCochain k G M n ≃ₗ[k] C(Fin n → G, X)`, degreewise;
* `contCochainEquiv_d`: it carries the differential of `contCochains` to the inhomogeneous
  coboundary `inhomD`, `(dc)(g₀,…,gₙ) = g₀ • c(g₁,…,gₙ) + ∑_j (−1)^{j+1} c(…, g_j g_{j+1}, …)`;
* `contToHomogeneous n`: for a locally compact `G`, continuous inhomogeneous `n`-cochains of `M`
  are homogeneous continuous `n`-cochains of `topRepOf M` (`contCochainEquiv` then `cochainEquiv`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ContBridge.Inv

open CategoryTheory ContRepresentation TopRep ZInQ.Manuscript.RC.SelmerComplex

universe u

variable (k : Type u) [CommRing k] [TopologicalSpace k] (G : Type u) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M] [ContinuousSMul G M]

/-- The action of `g` as a `k`-linear map. -/
def actLin (g : G) : M →ₗ[k] M where
  toFun m := g • m
  map_add' := smul_add g
  map_smul' c m := smul_comm g c m

/-- The continuous representation of `G` on the topological `G`-module `M`. -/
def contRep : ContRepresentation k G M :=
  .ofMonoidHom
    { toFun := fun g => ⟨actLin k G M g, continuous_const_smul g⟩
      map_one' := by ext m; exact one_smul G m
      map_mul' := fun g h => by ext m; exact mul_smul g h m }

theorem contRep_apply (g : G) (m : M) : contRep k G M g m = g • m := rfl

/-- The topological representation attached to `M`. -/
abbrev topRepOf : TopRep k G := TopRep.of (contRep k G M)

/-- **`hcont` for `M`** (`PROVED`): the action of `topRepOf M` is jointly continuous, because the
action `G × M → M` is (`ContinuousSMul G M`; for a discrete `M` this is the continuity of the
action in the sense of profinite group cohomology). -/
theorem hcont_topRepOf :
    Continuous fun p : G × (topRepOf k G M).V => (topRepOf k G M).ρ p.1 p.2 := by
  show Continuous fun p : G × M => p.1 • p.2
  exact continuous_smul

/-- **Degreewise**: continuous inhomogeneous `n`-cochains are the continuous maps `Gⁿ → M`. -/
def contCochainEquiv (n : ℕ) : contCochain k G M n ≃ₗ[k] C(Fin n → G, (topRepOf k G M).V) where
  toFun f := ⟨asFun k G M (f : (groupCohomology.inhomogeneousCochains (rep k G M)).X n), f.2⟩
  invFun c := ⟨(c : (Fin n → G) → M), c.continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem contCochainEquiv_apply (n : ℕ) (f : contCochain k G M n) (g : Fin n → G) :
    contCochainEquiv k G M n f g =
      asFun k G M (f : (groupCohomology.inhomogeneousCochains (rep k G M)).X n) g := rfl

/-- The inhomogeneous coboundary on continuous maps `Gⁿ → X`:
`(dc)(g₀,…,gₙ) = g₀ • c(g₁,…,gₙ) + ∑_j (−1)^{j+1} c(…, g_j g_{j+1}, …)`. -/
def inhomD (n : ℕ) (c : C(Fin n → G, (topRepOf k G M).V)) :
    C(Fin (n + 1) → G, (topRepOf k G M).V) where
  toFun g := g 0 • c (fun i => g i.succ) +
    ∑ j : Fin (n + 1), (-1 : k) ^ ((j : ℕ) + 1) • c (Fin.contractNth j (· * ·) g)
  continuous_toFun := by
    refine Continuous.add ?_ ?_
    · exact (continuous_apply 0).smul (c.continuous.comp (continuous_pi fun i => continuous_apply i.succ))
    · exact continuous_finsetSum _ fun j _ =>
        (c.continuous.comp (continuous_contractNth j)).const_smul _

/-- **Compatibility with the coboundary** (`PROVED`): the degreewise identification carries the
differential of `C^•_cont(G, M)` to the inhomogeneous coboundary `inhomD`. -/
theorem contCochainEquiv_d (n : ℕ) (f : (contCochains k G M).X n) :
    contCochainEquiv k G M (n + 1)
        ((contSubCx k G M).el (((contCochains k G M).d n (n + 1)).hom f)) =
      inhomD k G M n (contCochainEquiv k G M n ((contSubCx k G M).el f)) := by
  ext g
  exact contCochains_d_apply n f g

variable [LocallyCompactSpace G]

/-- **Continuous inhomogeneous cochains of `M` ≅ homogeneous continuous cochains of `topRepOf M`**,
degreewise (`PROVED`: `contCochainEquiv` followed by `cochainEquiv`). -/
def contToHomogeneous (n : ℕ) :
    contCochain k G M n ≃ₗ[k] (resolutionX (topRepOf k G M) (n + 1)).ρ.invariants :=
  (contCochainEquiv k G M n).trans (cochainEquiv (hcont_topRepOf k G M) n)

/-! ### Discrete modules -/

section Discrete

variable (k M : Type u) [CommRing k] [TopologicalSpace k] [AddCommGroup M] [Module k M]
  [TopologicalSpace M]

/-- A discrete abelian group is a topological group (`PROVED`). -/
theorem isTopologicalAddGroup_of_discrete [DiscreteTopology M] : IsTopologicalAddGroup M where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- Over a discrete ring, scalar multiplication on a discrete module is continuous (`PROVED`). -/
theorem continuousSMul_of_discrete [DiscreteTopology k] [DiscreteTopology M] :
    ContinuousSMul k M := ⟨continuous_of_discreteTopology⟩

end Discrete


end ZInQ.Contrib.CloudB3RC53.ContBridge.Inv
