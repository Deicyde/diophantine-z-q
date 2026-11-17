import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudR2Poincare.L2.RelativeFibreTriviality

/-!
# The actual global reduced normalized stabilizer locus

The GLOBAL closed residue-fibre locus of the normalized Mumford self-family
on A×A is given its native radical scheme structure K→A. Its field-valued
points are exactly the actual translation stabilizer, proved using native
closed-point/residue-field isomorphisms and actual reduced-test factorization.
Nothing here assumes global seesaw or claims whole-family class triviality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Exact field-point specialization, with no represented Picard scheme. -/
theorem normalizedFamily_rationalPoint_eq_one_iff
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]
    (L : A.left.Pic) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    L1.normalizedPolarizationFamily A L a = 1 ↔ a ∈ L1.translationStabilizer A L := by
  letI : Subsingleton (𝟙_ (Over (Spec (.of k)))).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of k)).Pic)
  rw [L1.normalizedPolarizationFamily_eq_of_subsingletonPic]
  have hsection : lift (𝟙 A) (toUnit A) = (ρ_ A).inv := by ext <;> simp
  letI : IsIso (lift (𝟙 A) (toUnit A)).left := by rw [hsection]; infer_instance
  have hc := L1.polarizationFamily_rationalPoint A L a
  change L1.polarizationFamily A L a = 1 ↔
    Scheme.Pic.map (L1.translate A a).left L = L
  rw [← L1.translationClass_eq_one_iff A L a, ← hc]
  constructor
  · intro ha
    rw [ha, Scheme.Pic.map_one]
  · intro ha
    apply L1.pic_map_injective_of_isIso (lift (𝟙 A) (toUnit A)).left
    simpa only [Scheme.Pic.map_one] using ha

/-- The global closed normalized residue-fibre locus in the ORIGINAL A. -/
def globalNormalizedKernelClosed {k : Type u} [Field k]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) : Closeds A.X.left :=
  letI : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  globalFibreTrivialityClosed (pullback.snd A.X.hom A.X.hom)
    (L1.normalizedPolarizationFamily A.X L (𝟙 A.X))

/-- The actual reduced closed scheme K, with its original-field structural morphism. -/
def globalNormalizedKernel {k : Type u} [Field k]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) : Over (Spec (.of k)) :=
  Over.mk (L1.reducedClosedSupportι A.X.left (globalNormalizedKernelClosed A L) ≫ A.X.hom)

/-- Actual closed inclusion K→A. No K group structure or Cartier Fact is installed. -/
def globalNormalizedKernelι {k : Type u} [Field k]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) : globalNormalizedKernel A L ⟶ A.X :=
  Over.homMk (L1.reducedClosedSupportι A.X.left (globalNormalizedKernelClosed A L))

instance globalNormalizedKernel_closed {k : Type u} [Field k]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) :
    IsClosedImmersion (globalNormalizedKernelι A L).left :=
  L1.reducedClosedSupport_closed _ _

instance globalNormalizedKernel_reduced {k : Type u} [Field k]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) :
    AlgebraicGeometry.IsReduced (globalNormalizedKernel A L).left :=
  L1.reducedClosedSupport_reduced _ _

/-- The actual closed inclusion has precisely the original global fibre-triviality support. -/
theorem range_globalNormalizedKernelι {k : Type u} [Field k]
    (A : PkgI3.AbVar k) (L : A.X.left.Pic) :
    Set.range (globalNormalizedKernelι A L).left = globalNormalizedKernelClosed A L :=
  L1.range_reducedClosedSupportι _ _

/-- On actual algebraically closed field points, membership in the global closed
locus is EXACTLY invariance of the original line-bundle class under translation. -/
theorem mem_globalNormalizedKernelClosed_rationalPoint_iff
    {k : Type u} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A.X) :
    a.left (IsLocalRing.closedPoint k) ∈ globalNormalizedKernelClosed A L ↔
      a ∈ L1.translationStabilizer A.X L := by
  let x : A.X.left := a.left (IsLocalRing.closedPoint k)
  have hx : IsClosed ({x} : Set A.X.left) :=
    (pointEquivClosedPoint A.X.hom ⟨a.left, Over.w a⟩).property
  let e := residueFieldIsoBase A.X.hom x hx
  have hpoint : pointOfClosedPoint A.X.hom x hx = a.left :=
    ext_of_apply_closedPoint_eq A.X.hom (pointOfClosedPoint_comp _ _ _) (Over.w a)
      (pointOfClosedPoint_apply _ _ _ _)
  let d : 𝟙_ (Over (Spec (.of k))) ⟶ residueParameter A.X x :=
    Over.homMk (Spec.map e.hom) (by
      change Spec.map e.hom ≫ (A.X.left.fromSpecResidueField x ≫ A.X.hom) = 𝟙 _
      simpa only [pointOfClosedPoint, Category.assoc] using pointOfClosedPoint_comp A.X.hom x hx)
  have hd : d ≫ residueParameterMap A.X x = a := by
    apply Over.OverMorphism.ext
    change Spec.map e.hom ≫ A.X.left.fromSpecResidueField x = a.left
    exact hpoint
  letI : IsIso d.left := by change IsIso (Spec.map e.hom); infer_instance
  letI : IsIso (JacobianChallenge.baseChangeMap A.X.hom d) :=
    (isPullback_baseChangeMap A.X.hom d).isIso_fst_of_isIso
  have hn := L1.normalizedPolarizationFamily_parameter A.X L (residueParameterMap A.X x) d
  rw [hd] at hn
  have heq : L1.normalizedPolarizationFamily A.X L (residueParameterMap A.X x) = 1 ↔
      L1.normalizedPolarizationFamily A.X L a = 1 := by
    rw [← hn]
    constructor
    · intro h; rw [h, Scheme.Pic.map_one]
    · intro h
      apply L1.pic_map_injective_of_isIso (JacobianChallenge.baseChangeMap A.X.hom d)
      simpa only [Scheme.Pic.map_one] using h
  change Scheme.Pic.map ((pullback.snd A.X.hom A.X.hom).fiberι x)
    (L1.normalizedPolarizationFamily A.X L (𝟙 A.X)) = 1 ↔ _
  rw [normalizedSelfFamily_residueFibre_eq_one_iff, heq, normalizedFamily_rationalPoint_eq_one_iff]

/-- Actual scheme factorization of every stabilizer field point into K, and conversely.
Reduced points are not identified with whole-family Picard triviality on arbitrary tests. -/
theorem globalNormalizedKernel_rationalPoint_factor_iff
    {k : Type u} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A.X) :
    (∃ z : 𝟙_ (Over (Spec (.of k))) ⟶ globalNormalizedKernel A L,
      z ≫ globalNormalizedKernelι A L = a) ↔ a ∈ L1.translationStabilizer A.X L := by
  letI : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  letI : AlgebraicGeometry.IsReduced (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of k)))
  constructor
  · rintro ⟨z, hz⟩
    apply (mem_globalNormalizedKernelClosed_rationalPoint_iff A L a).mp
    rw [← hz, Over.comp_left, Scheme.Hom.comp_apply]
    have hmem : (globalNormalizedKernelι A L).left (z.left (IsLocalRing.closedPoint k)) ∈
        Set.range (globalNormalizedKernelι A L).left := ⟨_, rfl⟩
    change (globalNormalizedKernelι A L).left (z.left (IsLocalRing.closedPoint k)) ∈
      (globalNormalizedKernelClosed A L : Set A.X.left)
    simpa only [range_globalNormalizedKernelι] using hmem
  · intro ha
    have hx := (mem_globalNormalizedKernelClosed_rationalPoint_iff A L a).mpr ha
    change a.left (IsLocalRing.closedPoint k) ∈ (globalNormalizedKernelClosed A L : Set A.X.left) at hx
    have hRange : Set.range a.left ⊆ globalNormalizedKernelClosed A L := by
      rintro y ⟨t, rfl⟩
      simpa only [Subsingleton.elim t (IsLocalRing.closedPoint k)] using hx
    obtain ⟨b, hb⟩ := L1.exists_factor_reducedClosedSupport (globalNormalizedKernelClosed A L)
      a.left hRange
    let z : 𝟙_ (Over (Spec (.of k))) ⟶ globalNormalizedKernel A L := Over.homMk b (by
      change b ≫ (L1.reducedClosedSupportι A.X.left (globalNormalizedKernelClosed A L) ≫ A.X.hom) = 𝟙 _
      rw [← Category.assoc, hb]
      exact Over.w a)
    refine ⟨z, ?_⟩
    apply Over.OverMorphism.ext
    exact hb

end ZInQ.Contrib.CloudR2Poincare.L2
