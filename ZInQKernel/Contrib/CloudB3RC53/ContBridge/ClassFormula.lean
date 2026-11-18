import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Discrete
import ZInQKernel.Contrib.TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# The class formula for the all-degree comparison (Route A)

`homologyLinearEquiv X hcont n` (`ComplexIso.lean`) sends the class of a homogeneous cocycle `z` to
the class of the continuous inhomogeneous cocycle whose underlying cochain is `degEquiv` of the
underlying cochain of `z`, i.e. `toInhom X n z` (`homologyLinearEquiv_π`, PROVED); for a discrete
module the same holds for `contCohomologyLinearEquiv` into RC26's `contCohomology k G M n`
(`contCohomologyLinearEquiv_π`, PROVED).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ContBridge

open CategoryTheory ContRepresentation

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  (X : TopRep.{u} k G) (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2)

theorem homologyIso_hom_π (n : ℕ) (z : (TopRep.homogeneousCochains X).cycles n) :
    (homologyIso X hcont n).hom.hom ((TopRep.homogeneousCochains X).homologyπ n z) =
      ((contSub X hcont).toCx.homologyπ n).hom
        ((HomologicalComplex.cyclesMap (cxIso X hcont).hom n).hom
          ((((TopRep.homogeneousCochains X).sc n).mapCyclesIso
            (forget₂ (TopModuleCat k) (ModuleCat k))).inv.hom z)) := by
  set e := ((TopRep.homogeneousCochains X).sc n).mapCyclesIso
    (forget₂ (TopModuleCat k) (ModuleCat k)) with he
  set h := ((TopRep.homogeneousCochains X).sc n).mapHomologyIso
    (forget₂ (TopModuleCat k) (ModuleCat k)) with hh
  have e1 : h.hom.hom ((((TopRep.homogeneousCochains X).sc n).map
      (forget₂ (TopModuleCat k) (ModuleCat k))).homologyπ.hom (e.inv.hom z)) =
      ((forget₂ (TopModuleCat k) (ModuleCat k)).map
        ((TopRep.homogeneousCochains X).sc n).homologyπ).hom (e.hom.hom (e.inv.hom z)) :=
    congrArg (fun f => f.hom (e.inv.hom z))
      (ShortComplex.homologyπ_comp_mapHomologyIso_hom ((TopRep.homogeneousCochains X).sc n)
        (forget₂ (TopModuleCat k) (ModuleCat k)))
  have e2 : (HomologicalComplex.homologyMap (cxIso X hcont).hom n).hom
      ((((forget₂ (TopModuleCat k) (ModuleCat k)).mapHomologicalComplex _).obj
        (TopRep.homogeneousCochains X)).homologyπ n |>.hom (e.inv.hom z)) =
      ((contSub X hcont).toCx.homologyπ n).hom
        ((HomologicalComplex.cyclesMap (cxIso X hcont).hom n).hom (e.inv.hom z)) :=
    congrArg (fun f => f.hom (e.inv.hom z))
      (HomologicalComplex.homologyπ_naturality (cxIso X hcont).hom n)
  have hz : e.hom.hom (e.inv.hom z) = z := Iso.inv_hom_id_apply e z
  have hhi : ∀ y, h.inv.hom (h.hom.hom y) = y := fun y => Iso.hom_inv_id_apply h y
  rw [hz] at e1
  rw [← e2]
  change (HomologicalComplex.homologyMap (cxIso X hcont).hom n).hom
    (h.inv.hom (((forget₂ (TopModuleCat k) (ModuleCat k)).map
        ((TopRep.homogeneousCochains X).sc n).homologyπ).hom z)) = _
  rw [← e1, hhi]
  rfl

/-- **The class formula**: `homologyLinearEquiv` sends the class of a homogeneous cocycle `z` to
the class of the continuous inhomogeneous cocycle `w` whose underlying cochain is
`degEquiv X hcont n z` (on functions: `toInhom X n z`, `degEquiv_coe`). -/
theorem homologyLinearEquiv_π (n : ℕ) (z : (TopRep.homogeneousCochains X).cycles n)
    (w : (contSub X hcont).toCx.cycles n)
    (hw : ((contSub X hcont).toCx.iCycles n).hom w =
      degEquiv X hcont n (((TopRep.homogeneousCochains X).iCycles n).hom z)) :
    homologyLinearEquiv X hcont n ((TopRep.homogeneousCochains X).homologyπ n z) =
      ((contSub X hcont).toCx.homologyπ n).hom w := by
  set e := ((TopRep.homogeneousCochains X).sc n).mapCyclesIso
    (forget₂ (TopModuleCat k) (ModuleCat k)) with he
  have c1 : ((contSub X hcont).toCx.iCycles n).hom
      ((HomologicalComplex.cyclesMap (cxIso X hcont).hom n).hom (e.inv.hom z)) =
      ((cxIso X hcont).hom.f n).hom
        (((((forget₂ (TopModuleCat k) (ModuleCat k)).mapHomologicalComplex _).obj
          (TopRep.homogeneousCochains X)).iCycles n).hom (e.inv.hom z)) :=
    congrArg (fun f => f.hom (e.inv.hom z)) (HomologicalComplex.cyclesMap_i (cxIso X hcont).hom n)
  have c2 : (((TopRep.homogeneousCochains X).sc n).map
      (forget₂ (TopModuleCat k) (ModuleCat k))).iCycles.hom (e.inv.hom z) =
      ((forget₂ (TopModuleCat k) (ModuleCat k)).map
        ((TopRep.homogeneousCochains X).sc n).iCycles).hom z :=
    congrArg (fun f => f.hom z)
      (ShortComplex.mapCyclesIso_inv_comp_iCycles ((TopRep.homogeneousCochains X).sc n)
        (forget₂ (TopModuleCat k) (ModuleCat k)))
  have hw' : (HomologicalComplex.cyclesMap (cxIso X hcont).hom n).hom (e.inv.hom z) = w := by
    apply (ModuleCat.mono_iff_injective ((contSub X hcont).toCx.iCycles n)).1 inferInstance
    rw [c1, hw]
    change ((cxIso X hcont).hom.f n).hom
      ((((TopRep.homogeneousCochains X).sc n).map
        (forget₂ (TopModuleCat k) (ModuleCat k))).iCycles.hom (e.inv.hom z)) = _
    rw [c2]
    rfl
  exact (homologyIso_hom_π X hcont n z).trans (congrArg _ hw')

section Discrete

open ZInQ.Manuscript.RC.SelmerComplex (contCochains contCohomology)

variable (k G M : Type u) [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
  [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [SMulCommClass G k M] [ContinuousSMul k M] [ContinuousSMul G M]

/-- **The class formula for discrete modules**: `contCohomologyLinearEquiv` sends the class of a
homogeneous cocycle `z` of `ofDiscreteModule k G M` to the class in RC26's `contCohomology k G M n`
of the continuous inhomogeneous cocycle with underlying cochain `toInhom _ n z`. -/
theorem contCohomologyLinearEquiv_π (n : ℕ)
    (z : (TopRep.homogeneousCochains (TauCeti.ofDiscreteModule k G M)).cycles n)
    (w : (contCochains k G M).cycles n)
    (hw : ((contCochains k G M).iCycles n).hom w =
      degEquiv (TauCeti.ofDiscreteModule k G M) (hcontDisc k G M) n
        (((TopRep.homogeneousCochains (TauCeti.ofDiscreteModule k G M)).iCycles n).hom z)) :
    contCohomologyLinearEquiv k G M n
        ((TopRep.homogeneousCochains (TauCeti.ofDiscreteModule k G M)).homologyπ n z) =
      ((contCochains k G M).homologyπ n).hom w := by
  rw [contCohomologyLinearEquiv, LinearEquiv.trans_apply,
    homologyLinearEquiv_π (TauCeti.ofDiscreteModule k G M) (hcontDisc k G M) n z w hw]
  change (HomologicalComplex.homologyMap (𝟙 (contCochains k G M)) n).hom _ = _
  rw [HomologicalComplex.homologyMap_id]
  rfl

end Discrete

end ZInQ.Contrib.CloudB3RC53.ContBridge
