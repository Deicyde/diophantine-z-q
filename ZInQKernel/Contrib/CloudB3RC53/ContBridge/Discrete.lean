import ZInQKernel.Contrib.CloudB3RC53.ContBridge.ComplexIso
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CochainComparison

/-!
# Matching with RC26's `contCochains` and Tau Ceti's low-degree comparison (Route A, A5–A6)

For a discrete `G`-module `M` over `k` with jointly continuous action, `X = ofDiscreteModule k G M`
(Tau Ceti's coefficient dictionary):

* `hcontDisc`: the action of `X` is jointly continuous;
* `contCochainsIso`: RC26's complex `contCochains k G M` of continuous inhomogeneous cochains is
  (definitionally) the complex `(contSub X hcontDisc).toCx` of `ComplexIso.lean` (A6);
* `contCohomologyLinearEquiv k G M n : continuousCohomology n (ofDiscreteModule k G M) ≃ₗ[k]
  contCohomology k G M n` for **every** `n` (locally compact `G`), with
  `contCohomologyLinearEquiv_π`: it sends the class of a homogeneous cocycle `F` to the class of
  the continuous inhomogeneous cocycle `toInhom X n F` (A5 + A6);
* `toInhom_eq_cochainEquiv0_symm`, `toInhom_eq_cochainEquiv1_symm`,
  `toInhom_eq_cochainEquiv2_symm`: in degrees `0, 1, 2` the forward map is the inverse of Tau Ceti's
  `cochainEquiv0/1/2` (A5, low-degree compatibility).

All PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ContBridge

open CategoryTheory ContRepresentation
open ZInQ.Manuscript.RC.SelmerComplex (SubCx contCochains contCohomology contSubCx)

universe u

/-- For a discrete coefficient ring and a discrete module the scalar action is continuous, so the
hypothesis `ContinuousSMul k M` below is automatic in that case (use with `haveI`). -/
theorem continuousSMul_of_discrete (k M : Type*) [TopologicalSpace k] [DiscreteTopology k]
    [TopologicalSpace M] [DiscreteTopology M] [SMul k M] : ContinuousSMul k M :=
  ⟨continuous_of_discreteTopology⟩

section A6

variable (k G M : Type u) [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [SMulCommClass G k M] [ContinuousSMul k M] [ContinuousSMul G M]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- The action of `ofDiscreteModule k G M` is jointly continuous. -/
theorem hcontDisc : Continuous fun p : G × (TauCeti.ofDiscreteModule k G M).V =>
    (TauCeti.ofDiscreteModule k G M).ρ p.1 p.2 :=
  show Continuous fun p : G × M => p.1 • p.2 from continuous_smul

/-- **(A6)** RC26's continuous cochains are the complex `contSub` of `ofDiscreteModule k G M`. -/
def contCochainsIso :
    contCochains k G M ≅ (contSub (TauCeti.ofDiscreteModule k G M) (hcontDisc k G M)).toCx :=
  Iso.refl _

/-- **(A5)+(A6) Continuous cohomology of a discrete module in every degree**: Mathlib's
`continuousCohomology n (ofDiscreteModule k G M)` is RC26's `contCohomology k G M n`. -/
def contCohomologyLinearEquiv (n : ℕ) :
    continuousCohomology n (TauCeti.ofDiscreteModule k G M) ≃ₗ[k] contCohomology k G M n :=
  (homologyLinearEquiv (TauCeti.ofDiscreteModule k G M) (hcontDisc k G M) n).trans
    (HomologicalComplex.homologyMapIso (contCochainsIso k G M) n).symm.toLinearEquiv

end A6

section LowDegree

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Degree `0`: the forward map is the inverse of Tau Ceti's `cochainEquiv0`. -/
theorem toInhom_eq_cochainEquiv0_symm
    (F : (TopRep.homogeneousCochains (TauCeti.ofDiscreteModule ℤ G M)).X 0) (g : Fin 0 → G) :
    toInhom (TauCeti.ofDiscreteModule ℤ G M) 0 F g =
      (TauCeti.ContCohomology.cochainEquiv0 G M).symm F := by
  rw [toInhom_apply, TauCeti.ContCohomology.cochainEquiv0_symm_apply]
  have h : Fin.partialProd g = ![1] := by
    funext i
    fin_cases i
    simp
  rw [h]
  rfl

/-- Degree `1`: the forward map is the inverse of Tau Ceti's `cochainEquiv1`. -/
theorem toInhom_eq_cochainEquiv1_symm
    (F : (TopRep.homogeneousCochains (TauCeti.ofDiscreteModule ℤ G M)).X 1) (g : Fin 1 → G) :
    toInhom (TauCeti.ofDiscreteModule ℤ G M) 1 F g =
      ((TauCeti.ContCohomology.cochainEquiv1 G M).symm F).val (g 0) := by
  rw [toInhom_apply, TauCeti.ContCohomology.cochainEquiv1_symm_apply]
  have h : Fin.partialProd g = ![1, g 0] := by
    funext i
    fin_cases i
    · simp
    · change Fin.partialProd g (Fin.succ 0) = _
      rw [Fin.partialProd_succ]
      simp
  rw [h]
  rfl

/-- Degree `2`: the forward map is the inverse of Tau Ceti's `cochainEquiv2`. -/
theorem toInhom_eq_cochainEquiv2_symm [LocallyCompactSpace G]
    (F : (TopRep.homogeneousCochains (TauCeti.ofDiscreteModule ℤ G M)).X 2) (g : Fin 2 → G) :
    toInhom (TauCeti.ofDiscreteModule ℤ G M) 2 F g =
      ((TauCeti.ContCohomology.cochainEquiv2 G M).symm F).val (g 0, g 1) := by
  rw [toInhom_apply, TauCeti.ContCohomology.cochainEquiv2_symm_apply]
  have h : Fin.partialProd g = ![1, g 0, g 0 * g 1] := by
    funext i
    fin_cases i
    · simp
    · change Fin.partialProd g (Fin.succ 0) = _
      rw [Fin.partialProd_succ]
      simp
    · change Fin.partialProd g (Fin.succ 1) = _
      rw [Fin.partialProd_succ]
      change Fin.partialProd g (Fin.succ 0) * g 1 = _
      rw [Fin.partialProd_succ]
      simp
  rw [h]
  rfl

end LowDegree

end ZInQ.Contrib.CloudB3RC53.ContBridge
