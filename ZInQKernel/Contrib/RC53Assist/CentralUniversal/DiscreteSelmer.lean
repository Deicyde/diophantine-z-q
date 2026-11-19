import ZInQKernel.Contrib.RC53Assist.CentralSelmer.QuadraticDescent
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TauCetiComparison
import ZInQKernel.Contrib.OneProof.RC.CoefModules.CocycleCondition

/-!
# The genuine discrete Selmer cocycle complex

The cocycle realization of a cohomology subgroup retains all zero-cochains and
has its prescribed continuous cocycles in degree one. In the arithmetic
application the subgroup is fixed to the genuine full two-primary Selmer group
over the specified quadratic field, with its condition at every place.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Manuscript.RC53Assist.CentralUniversal

open CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open TauCeti TauCeti.ContCohomology

section ContinuousCocycles

variable {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul G M]

/-- A continuous crossed homomorphism as an inhomogeneous one-cochain. -/
def cocycleCochain (c : Z1 G M) : contCochain ℤ G M 1 :=
  mkCochain1 (k := ℤ) (c : G → M) (mem_Z1_iff.mp c.2).1

/-- Its cochain differential vanishes. -/
theorem cocycleCochain_d_zero (c : Z1 G M) : contD ℤ G M 1 (cocycleCochain c) = 0 := by
  apply Subtype.ext
  funext g
  have h := contCochains_d_apply (k := ℤ) (G := G) (M := M) 1 (cocycleCochain c) g
  refine h.trans ?_
  rw [Fin.sum_univ_two]
  change g 0 • (c : G → M) (g 1) +
    ((-1 : ℤ) ^ ((0 : ℕ) + 1) • (c : G → M) (g 0 * g 1) +
      (-1 : ℤ) ^ ((1 : ℕ) + 1) • (c : G → M) (g 0)) = 0
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow,
    one_pow, one_smul]
  rw [(mem_Z1_iff.mp c.2).2 (g 0) (g 1)]
  abel

/-- Its class is the original continuous cohomology class. -/
theorem cocycleCochain_class (c : Z1 G M) :
    kerToH1 (k := ℤ) ⟨cocycleCochain c, cocycleCochain_d_zero c⟩ = H1pi G M c := by
  rfl

variable (L : AddSubgroup (H1 G M))

/-- Continuous cocycles representing classes of the prescribed subgroup. -/
def subgroupCocycleGenerators : Set (contCochain ℤ G M 1) :=
  cocycleCochain '' {c : Z1 G M | H1pi G M c ∈ L}

/-- Their integral span in the continuous one-cochains. -/
def subgroupCocycleSub : Submodule ℤ (contCochain ℤ G M 1) :=
  Submodule.span ℤ (subgroupCocycleGenerators L)

/-- This span consists of cocycles. -/
theorem subgroupCocycleSub_d_zero : ∀ z ∈ subgroupCocycleSub L, contD ℤ G M 1 z = 0 :=
  cochainSpan_cocycle _ (by
    rintro _ ⟨c, hc, rfl⟩
    exact cocycleCochain_d_zero c)

/-- The span still represents only classes of the prescribed subgroup. -/
theorem subgroupCocycleSub_class_mem (z : contCochain ℤ G M 1)
    (hz : z ∈ subgroupCocycleSub L) (hd : contD ℤ G M 1 z = 0) :
    kerToH1 (k := ℤ) ⟨z, hd⟩ ∈ L := by
  revert hd
  induction hz using Submodule.span_induction with
  | mem x hx =>
    intro hd
    obtain ⟨c, hc, rfl⟩ := hx
    change H1pi G M c ∈ L
    exact hc
  | zero =>
    intro hd
    change kerToH1 (k := ℤ) (0 : LinearMap.ker (contD ℤ G M 1)) ∈ L
    rw [map_zero]
    exact L.zero_mem
  | add x y hx hy ihx ihy =>
    intro hd
    have hdx := subgroupCocycleSub_d_zero L x hx
    have hdy := subgroupCocycleSub_d_zero L y hy
    change kerToH1 (k := ℤ)
      ((⟨x, hdx⟩ : LinearMap.ker (contD ℤ G M 1)) + ⟨y, hdy⟩) ∈ L
    rw [map_add]
    exact L.add_mem (ihx hdx) (ihy hdy)
  | smul a x hx ihx =>
    intro hd
    have hdx := subgroupCocycleSub_d_zero L x hx
    change kerToH1 (k := ℤ) (a • (⟨x, hdx⟩ : LinearMap.ker (contD ℤ G M 1))) ∈ L
    rw [map_zsmul]
    exact L.zsmul_mem (ihx hdx) a

/-- The cocycle complex of that subgroup, including all zero-cochains. -/
abbrev subgroupCocycleComplex : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (cocycleCondition (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)).toCC

/-- A degree-one cochain of this complex is a continuous global cocycle. -/
def subgroupCycle (x : (subgroupCocycleComplex L).X 1) : LinearMap.ker (contD ℤ G M 1) :=
  ⟨(condOne (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) x).1, by
    have h := condP_d_mem (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) 1
      ((condOne (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) x).1)
      ((condOne (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) x).2)
    exact (Submodule.mem_bot ℤ).mp h⟩

/-- Its class in the ambient continuous cohomology group. -/
def subgroupAmbientClass : (subgroupCocycleComplex L).X 1 →+ H1 G M :=
  (kerToH1 (k := ℤ)).comp
    { toFun := subgroupCycle L
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }

/-- The class satisfies the prescribed subgroup condition. -/
theorem subgroupAmbientClass_mem (x : (subgroupCocycleComplex L).X 1) :
    subgroupAmbientClass L x ∈ L := by
  obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.mp
    (condOne (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) x).2
  obtain ⟨c, rfl⟩ := (mem_contB1_iff b).mp hb
  have hdz := subgroupCocycleSub_d_zero L z hz
  have hclass : subgroupAmbientClass L x =
      kerToH1 (k := ℤ) ⟨z, hdz⟩ + kerToH1 (k := ℤ) ⟨contD ℤ G M 0 c, contD_contD 0 c⟩ := by
    change kerToH1 (k := ℤ) (subgroupCycle L x) = _
    rw [← map_add]
    congr 1
    exact Subtype.ext hzb.symm
  have hb0 : kerToH1 (k := ℤ) ⟨contD ℤ G M 0 c, contD_contD 0 c⟩ = 0 :=
    (kerToH1_eq_zero_iff _).mpr ⟨c, rfl⟩
  rw [hclass, hb0, add_zero]
  exact subgroupCocycleSub_class_mem L z hz hdz

/-- The class map into the prescribed subgroup. -/
def subgroupClass : (subgroupCocycleComplex L).X 1 →+ L :=
  (subgroupAmbientClass L).codRestrict L (subgroupAmbientClass_mem L)

/-- Every class of the subgroup has a cocycle representative. -/
theorem subgroupClass_surjective : Function.Surjective (subgroupClass L) := by
  intro s
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (s : H1 G M)
  have hmem : H1pi G M c ∈ L := by
    change QuotientAddGroup.mk c ∈ L
    rw [hc]
    exact s.2
  let x : (subgroupCocycleComplex L).X 1 :=
    ofCondOne (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)
      ⟨cocycleCochain c, Submodule.mem_sup_left (Submodule.subset_span ⟨c, hmem, rfl⟩)⟩
  refine ⟨x, Subtype.ext ?_⟩
  change kerToH1 (k := ℤ) ⟨cocycleCochain c, cocycleCochain_d_zero c⟩ = (s : H1 G M)
  rw [cocycleCochain_class]
  exact hc

/-- The kernel is exactly the ordinary continuous coboundaries. -/
theorem subgroupClass_zero_iff (x : (subgroupCocycleComplex L).X 1) :
    subgroupClass L x = 0 ↔ x ∈ condB1 (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) := by
  constructor
  · intro hx
    have hx' := congrArg Subtype.val hx
    change kerToH1 (k := ℤ) (subgroupCycle L x) = 0 at hx'
    obtain ⟨c, hc⟩ := (kerToH1_eq_zero_iff _).mp hx'
    change (condOne (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) x).1 ∈ contB1 ℤ G M
    exact ⟨c, hc⟩
  · intro hx
    apply Subtype.ext
    change kerToH1 (k := ℤ) (subgroupCycle L x) = 0
    apply (kerToH1_eq_zero_iff _).mpr
    exact (mem_contB1_iff _).mp hx

/-- Cohomology recognizes this particular subgroup, through the actual cocycle-class map. -/
def subgroupCocycleHomologyEquiv : (subgroupCocycleComplex L).homology 1 ≃+ L :=
  (cocycleConditionH1Iso (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)).toLinearEquiv.toAddEquiv.trans
    (QuotientAddGroup.liftEquiv
      (condB1 (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)).toAddSubgroup
      (subgroupClass_surjective L) (by
        ext x
        change x ∈ condB1 (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) ↔ subgroupClass L x = 0
        exact (subgroupClass_zero_iff L x).symm))

end ContinuousCocycles

/-- The cocycle complex for the fixed genuine quadratic Selmer group, not a free group. -/
abbrev discreteSelmerComplex (ℓ : ℕ) (k : ℤ) : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  subgroupCocycleComplex (SelK ℓ k)

/-- Its first cohomology is the genuine full Selmer group over the specified field. -/
def discreteSelmerHomologyEquiv (ℓ : ℕ) (k : ℤ) :
    (discreteSelmerComplex ℓ k).homology 1 ≃+ SelK ℓ k :=
  subgroupCocycleHomologyEquiv (SelK ℓ k)

/-- Zeroth cohomology is the global two-primary coefficient invariants, including point torsion. -/
def discreteSelmerH0Iso (ℓ : ℕ) (k : ℤ) : (discreteSelmerComplex ℓ k).homology 0 ≅
    ModuleCat.of ℤ (invariantsSub ℤ (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ))) :=
  cocycleConditionH0IsoInvariants _ _

end ZInQ.Manuscript.RC53Assist.CentralUniversal
