import ZInQKernel.Contrib.CloudR2Poincare.L2.GraphProjectionCriterion
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Actual topological/radicial part of the normal graph criterion

Geometric field-point injectivity makes the ORIGINAL diagonal surjective:
every point of the fibre product lifts to an algebraic-closure field test.
This proves universal injectivity, not a false claim that field points form
a sheaf cover. Properness then gives finite fibres/ZMT, and field-point
surjectivity gives actual scheme-space surjectivity. Source irreducibility
comes from the resulting homeomorphism, not from the B→Γ inclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Every original scheme point lies in the image of an actual algebraically
closed field-valued test over k, with its genuine structural equation. -/
theorem exists_algClosed_fieldPoint_through
    {k : Type u} [Field k] [CharZero k] (X : Over (Spec (.of k))) (x : X.left) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharZero Ω) (_ : Algebra k Ω)
      (a : L1.fieldTest k Ω ⟶ X), a.left (IsLocalRing.closedPoint Ω) = x := by
  let Ω := AlgebraicClosure (X.left.residueField x)
  let z : Spec (.of Ω) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) Ω)) ≫ X.left.fromSpecResidueField x
  let c : CommRingCat.of k ⟶ CommRingCat.of Ω := Spec.preimage (z ≫ X.hom)
  letI : Algebra k Ω := c.hom.toAlgebra
  letI : CharZero Ω := charZero_of_injective_ringHom c.hom.injective
  let a : L1.fieldTest k Ω ⟶ X := Over.homMk z (by
    change z ≫ X.hom = Spec.map c
    exact (Spec.map_preimage _).symm)
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, inferInstance, a, ?_⟩
  let pt : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  change z pt = x
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply (X := X.left) x _

/-- All algebraically closed field-test injectivity implies ORIGINAL universal
injectivity, by actual diagonal surjectivity (native Stacks01S4). -/
theorem universallyInjective_of_geometricFieldPoints
    {k : Type u} [Field k] [CharZero k] {X Y : Over (Spec (.of k))} (p : X ⟶ Y)
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Injective (fun a : L1.fieldTest k Ω ⟶ X => a ≫ p)) :
    UniversallyInjective p.left := by
  apply (UniversallyInjective.iff_diagonal p.left).mpr
  let P : Over (Spec (.of k)) := Over.mk (pullback.fst p.left p.left ≫ X.hom)
  let f₁ : P ⟶ X := Over.homMk (pullback.fst p.left p.left)
  let f₂ : P ⟶ X := Over.homMk (pullback.snd p.left p.left) (by
    change pullback.snd p.left p.left ≫ X.hom = pullback.fst p.left p.left ≫ X.hom
    simpa only [Category.assoc, p.w] using
      congrArg (fun m => m ≫ Y.hom) (pullback.condition (f := p.left) (g := p.left)).symm)
  refine ⟨fun z => ?_⟩
  obtain ⟨Ω, hΩ, hclosed, hchar, halg, a, ha⟩ := exists_algClosed_fieldPoint_through P z
  letI : Field Ω := hΩ
  letI : IsAlgClosed Ω := hclosed
  letI : CharZero Ω := hchar
  letI : Algebra k Ω := halg
  have hpoint : a ≫ f₁ = a ≫ f₂ := by
    apply hp Ω
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, f₁, f₂, Over.homMk_left, Category.assoc] using
      congrArg (fun m => a.left ≫ m) (pullback.condition (f := p.left) (g := p.left))
  have hs : a.left ≫ pullback.fst p.left p.left = a.left ≫ pullback.snd p.left p.left :=
    congrArg Over.Hom.left hpoint
  have hd : (a.left ≫ pullback.fst p.left p.left) ≫ pullback.diagonal p.left = a.left := by
    apply pullback.hom_ext
    · simp
    · simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id] using hs
  refine ⟨pullback.fst p.left p.left z, ?_⟩
  let pt : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have hval := congrArg (fun m => m pt) hd
  change pullback.diagonal p.left (pullback.fst p.left p.left (a.left pt)) = a.left pt at hval
  change a.left pt = z at ha
  rw [ha] at hval
  exact hval

/-- Actual scheme-space surjectivity follows from all algebraically closed
field-point surjectivity, using the residue field of each ORIGINAL target point. -/
theorem surjective_of_geometricFieldPoints
    {k : Type u} [Field k] [CharZero k] {X Y : Over (Spec (.of k))} (p : X ⟶ Y)
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Surjective (fun a : L1.fieldTest k Ω ⟶ X => a ≫ p)) : Surjective p.left := by
  refine ⟨fun y => ?_⟩
  obtain ⟨Ω, hΩ, hclosed, hchar, halg, a, ha⟩ := exists_algClosed_fieldPoint_through Y y
  letI : Field Ω := hΩ
  letI : IsAlgClosed Ω := hclosed
  letI : CharZero Ω := hchar
  letI : Algebra k Ω := halg
  obtain ⟨b, hb⟩ := hp Ω a
  refine ⟨b.left (IsLocalRing.closedPoint Ω), ?_⟩
  have h := congrArg Over.Hom.left hb
  change b.left ≫ p.left = a.left at h
  let pt : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have hval := congrArg (fun m => m pt) h
  change p.left (b.left pt) = a.left pt at hval
  change a.left pt = y at ha
  rw [ha] at hval
  exact hval

/-- Original-field proper p is finite once it is injective on every geometric
field-test type. No source-group structure or algebraically closed k is added. -/
theorem isFinite_of_geometricFieldPoint_injective
    {k : Type u} [Field k] [CharZero k] {X Y : Over (Spec (.of k))}
    (p : X ⟶ Y) [IsProper p.left]
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Injective (fun a : L1.fieldTest k Ω ⟶ X => a ≫ p)) : IsFinite p.left := by
  letI : UniversallyInjective p.left := universallyInjective_of_geometricFieldPoints p hp
  apply isFinite_of_finite_fibres p.left
  intro y
  have hs : Set.Subsingleton (p.left ⁻¹' {y}) := by
    intro a ha b hb
    change p.left a = y at ha
    change p.left b = y at hb
    exact p.left.injective (ha.trans hb.symm)
  exact hs.finite

/-- Proper geometric point bijectivity gives an ACTUAL topological
homeomorphism of the original scheme spaces. -/
theorem isHomeomorph_of_geometricFieldPoint_bijective
    {k : Type u} [Field k] [CharZero k] {X Y : Over (Spec (.of k))}
    (p : X ⟶ Y) [IsProper p.left]
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Bijective (fun a : L1.fieldTest k Ω ⟶ X => a ≫ p)) : IsHomeomorph p.left := by
  have hinj : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Injective (fun a : L1.fieldTest k Ω ⟶ X => a ≫ p) := by
    intro Ω _ _ _ _ a b h
    exact (hp Ω).1 h
  have hsurj : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Surjective (fun a : L1.fieldTest k Ω ⟶ X => a ≫ p) := by
    intro Ω _ _ _ _ y
    exact (hp Ω).2 y
  letI : UniversallyInjective p.left := universallyInjective_of_geometricFieldPoints p hinj
  letI : Surjective p.left := surjective_of_geometricFieldPoints p hsurj
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨p.left.continuous, p.left.isClosedMap, p.left.injective, Surjective.surj⟩

/-- Source integrality comes from the ACTUAL projection homeomorphism onto
integral J and the given reducedness, not from a possibly proper B→Γ inclusion. -/
theorem isIntegral_source_of_geometricFieldPoint_bijective
    {k : Type u} [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (G : Over (Spec (.of k))) [AlgebraicGeometry.IsReduced G.left]
    (p : G ⟶ J.X) [IsProper p.left]
    (hp : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Bijective (fun a : L1.fieldTest k Ω ⟶ G => a ≫ p)) : IsIntegral G.left := by
  letI : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  have h := isHomeomorph_of_geometricFieldPoint_bijective p hp
  letI : IrreducibleSpace G.left := (h.homeomorph p.left).irreducibleSpace_iff.mpr inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced G.left

/-- Native radicial residue extensions are trivial in characteristic zero.
This proves the residue-field degree-one statement without counting Ω-points. -/
theorem isIso_residueFieldMap_of_universallyInjective_charZero
    {k : Type u} [Field k] [CharZero k] {X Y : Over (Spec (.of k))}
    (p : X ⟶ Y) [UniversallyInjective p.left] (x : X.left) :
    IsIso (p.left.residueFieldMap x) := by
  have hpi := ((tfae_universallyInjective p.left).out 1 3).mp
    (inferInstance : UniversallyInjective p.left)
  let c : CommRingCat.of k ⟶ Y.left.residueField (p.left x) :=
    Spec.preimage (Y.left.fromSpecResidueField (p.left x) ≫ Y.hom)
  letI : CharZero (Y.left.residueField (p.left x)) := charZero_of_injective_ringHom c.hom.injective
  letI : Algebra (Y.left.residueField (p.left x)) (X.left.residueField x) :=
    (p.left.residueFieldMap x).hom.toAlgebra
  letI : IsPurelyInseparable (Y.left.residueField (p.left x)) (X.left.residueField x) := hpi.2 x
  letI : Algebra.IsSeparable (Y.left.residueField (p.left x)) (X.left.residueField x) := inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    (Y.left.residueField (p.left x)) (X.left.residueField x)

end ZInQ.Contrib.CloudR2Poincare.L2
