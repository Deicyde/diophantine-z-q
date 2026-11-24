import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.FieldTheory.FunctionField.Elliptic.Basic
import TauCeti.FieldTheory.FunctionField.Place.Adic

/-!
# Function fields of one-dimensional group schemes

The geometric hypotheses below are exactly those of `PkgI3.AbVar.X`:
a group object over the spectrum of a field, with a proper, smooth,
geometrically integral structure morphism. The definition is in
`ZInQKernel/HDecomp/Objects.lean`, lines 162–181. In particular, geometric
integrality is already part of that definition, not an additional conclusion.

The function-field and constant-field proofs apply to arbitrary integral
schemes locally of finite type, respectively geometrically integral schemes.
No existence of a Weierstrass equation or a genus-one curve is assumed here.

The dimension argument follows the proved results in
`ZInQKernel/Contrib/Dim/FunctionField.lean` and `Dim/Trdeg.lean`.
The exact-constants argument follows
`TauCeti/AlgebraicGeometry/Geometrically/FunctionField.lean`.
The needed proofs are given directly, with individual Mathlib imports.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory Limits Order TopologicalSpace Topology
open scoped TensorProduct

/-- DEFINITION. The algebra of rational functions induced by the structure morphism.
Locator: `ZInQKernel/Contrib/Dim/FunctionField.lean`, `functionFieldAlgebra`;
`TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`,
    `Scheme.baseRingToFunctionField`. -/
@[instance_reducible]
def functionFieldAlgebra {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) : Algebra k X.functionField :=
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom).toAlgebra

/-- DEFINITION. The constants act on sections over an open through the structure morphism.
Locator: `ZInQKernel/Contrib/Dim/FunctionField.lean`, `sectionsAlgebra`. -/
@[instance_reducible]
def sectionsAlgebra {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom).toAlgebra

/-- THEOREM (proved). The constant, section, and rational-function actions form a scalar tower.
Locator: `ZInQKernel/Contrib/Dim/FunctionField.lean`,
`topologicalKrullDim_affineOpen_eq_trdeg_functionField`, scalar-tower subproof. -/
theorem sections_functionField_tower {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (U : X.Opens) [Nonempty U] :
    letI := functionFieldAlgebra f
    letI := sectionsAlgebra f U
    IsScalarTower k Γ(X, U) X.functionField := by
  letI := functionFieldAlgebra f
  letI := sectionsAlgebra f U
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom c =
    (X.germToFunctionField U).hom
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom c)
  rw [← CommRingCat.comp_apply]
  congr 2
  simp only [Category.assoc, Scheme.Hom.appLE, Scheme.Hom.appTop]
  congr 2
  exact (X.presheaf.germ_res (homOfLE le_top) _ _).symm

/-- THEOREM (proved). Locally finite-type schemes have finite-type affine coordinate rings.
Locator: Mathlib, `LocallyOfFiniteType.finiteType_appLE`;
`ZInQKernel/Contrib/Dim/FunctionField.lean`, affine coordinate-ring subproof. -/
theorem finiteType_sections {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    Algebra.FiniteType k Γ(X, U) := by
  letI := sectionsAlgebra f U
  have h₁ : (f.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
  exact h₁.comp h₂

/-- THEOREM (proved). An integral injective ring extension preserves Krull dimension.
Locator: `ZInQKernel/Contrib/Dim/IntegralHom.lean`,
`ringKrullDim_eq_of_isIntegral_of_injective`; Mathlib's going-up and incomparability. -/
private theorem integral_dimension_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) (show P.asIdeal < Q.asIdeal from hPQ)
  · refine iSup_le fun l => ?_
    obtain ⟨P, _, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have hx₀ : algebraMap A B x = 0 := by simpa using hx
        have hx' : x = 0 := hinj (by simpa using hx₀)
        simp [hx'])
    haveI : P.IsPrime := hP
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

/-- THEOREM (proved). Noether normalization identifies dimension and transcendence degree.
Locator: `ZInQKernel/Contrib/Dim/Trdeg.lean`,
`exists_ringKrullDim_eq_and_trdeg_eq`; Mathlib, `exists_finite_inj_algHom_of_fg`. -/
private theorem normalization_dimension {k R : Type} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    ∃ n : ℕ, ringKrullDim R = n ∧ Algebra.trdeg k R = n := by
  obtain ⟨n, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg k R
  letI := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin n) k) R := ⟨gfin.to_isIntegral⟩
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin n) k) R :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin n) k) x).isAlgebraic⟩
  haveI : IsScalarTower k (MvPolynomial (Fin n) k) R :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  haveI : FaithfulSMul (MvPolynomial (Fin n) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ginj
  refine ⟨n, ?_, ?_⟩
  · rw [integral_dimension_eq ginj,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  · have h := lift_trdeg_add_eq k (MvPolynomial (Fin n) k) R
    rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial (Fin n) k) (A := R)] at h
    simpa using h.symm

/-- THEOREM (proved). Localization to a fraction field does not change transcendence degree.
Locator: `ZInQKernel/Contrib/Dim/Trdeg.lean`, `trdeg_eq_of_isFractionRing`. -/
private theorem fractionField_trdeg {k R F : Type} [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Field F] [Algebra R F] [Algebra k F] [IsScalarTower k R F]
    [IsFractionRing R F] : Algebra.trdeg k F = Algebra.trdeg k R := by
  haveI : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F (nonZeroDivisors R)
  haveI : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (IsFractionRing.injective R F)
  rw [← trdeg_add_eq k R (A := F), trdeg_eq_zero (R := R) (A := F), add_zero]

/-- THEOREM (proved). Every nonempty affine open has dimension equal to the transcendence
 degree of the function field. Locator: `ZInQKernel/Contrib/Dim/FunctionField.lean`,
`topologicalKrullDim_affineOpen_eq_trdeg_functionField`. -/
theorem affine_dimension_eq_trdeg {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    letI := functionFieldAlgebra f
    topologicalKrullDim U = ((Algebra.trdeg k X.functionField).toENat : WithBot ℕ∞) := by
  letI := functionFieldAlgebra f
  letI := sectionsAlgebra f U
  haveI := finiteType_sections f hU
  haveI := sections_functionField_tower f U
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨n, hn, htr⟩ := normalization_dimension (k := k) (R := Γ(X, U))
  rw [fractionField_trdeg (R := Γ(X, U)), htr, Cardinal.toENat_nat,
    show topologicalKrullDim U = topologicalKrullDim U.toScheme from rfl]
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hU.isoSpec).isHomeomorph]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)).trans hn

/-- THEOREM (proved). Dimension can be computed on an open cover.
Locator: `ZInQKernel/Contrib/Dim/Basic.lean`,
`topologicalKrullDim_eq_iSup_of_isOpenEmbedding`. -/
private theorem dimension_open_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : TopologicalSpace.IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ Order.krullDim {V : TopologicalSpace.IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
        q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

/-- THEOREM (proved). The dimension of an integral scheme locally of finite type over a field
is the transcendence degree of its actual generic stalk.
Locator: `ZInQKernel/Contrib/Dim/FunctionField.lean`,
`topologicalKrullDim_eq_trdeg_functionField`. -/
theorem dimension_eq_trdeg {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    letI := functionFieldAlgebra f
    topologicalKrullDim X = ((Algebra.trdeg k X.functionField).toENat : WithBot ℕ∞) := by
  letI := functionFieldAlgebra f
  let ι := {U : X.Opens // IsAffineOpen U ∧ (U : Set X).Nonempty}
  have hcov : ∀ x : X, ∃ i : ι, x ∈ Set.range (fun y : (i.1 : Set X) => (y : X)) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV, ⟨x, hxV⟩⟩, ⟨x, hxV⟩, rfl⟩
  rw [dimension_open_cover (Y := fun i : ι => (i.1 : Set X))
    (fun i y => (y : X)) (fun i => i.1.isOpen.isOpenEmbedding_subtypeVal) hcov]
  haveI : Nonempty ι := by
    obtain ⟨i, _⟩ := hcov (genericPoint X)
    exact ⟨i⟩
  have hdim : ∀ i : ι, topologicalKrullDim (i.1 : Set X) =
      ((Algebra.trdeg k X.functionField).toENat : WithBot ℕ∞) := by
    intro i
    haveI : Nonempty i.1 := i.2.2.to_subtype
    exact affine_dimension_eq_trdeg f i.1 i.2.1
  simp only [hdim, ciSup_const]

/-- THEOREM (proved). The function field is finitely generated as a field extension.
Locator: Mathlib, `Algebra.EssFiniteType.of_isLocalization` and
`Algebra.EssFiniteType.comp`; the affine-open fraction-field description. -/
theorem functionField_essFiniteType {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    letI := functionFieldAlgebra f
    Algebra.EssFiniteType k X.functionField := by
  letI := functionFieldAlgebra f
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  haveI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  letI := sectionsAlgebra f U
  haveI := finiteType_sections f hU
  haveI := sections_functionField_tower f U
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  haveI : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp k Γ(X, U) X.functionField

/-- THEOREM (proved, the one-variable part of S2a). A one-dimensional integral scheme
locally of finite type over a field has a one-variable function field in Tau Ceti's intrinsic
sense. Locator: `TauCeti.isFunctionField_iff_trdeg_eq_one`; `dimension_eq_trdeg` above. -/
theorem isFunctionField_of_dimension_one {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    TauCeti.IsFunctionField k X.functionField := by
  letI := functionFieldAlgebra f
  haveI := functionField_essFiniteType f
  rw [TauCeti.isFunctionField_iff_trdeg_eq_one]
  have h := dimension_eq_trdeg f
  rw [hdim] at h
  exact Cardinal.toENat_eq_one.mp (by exact_mod_cast h.symm)

/-- THEOREM (proved). A tensor product which is a domain remains a domain after localization
at nonzero divisors on one factor. Locator:
`TauCeti/RingTheory/TensorProduct/IsDomain.lean`,
`isDomain_tensorProduct_of_isLocalization`. -/
private theorem tensor_domain_of_localization {k A B L : Type} [Field k] [CommRing A]
    [Algebra k A] (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) [CommRing B] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] [IsLocalization M B] [CommRing L] [Algebra k L]
    [IsDomain (A ⊗[k] L)] : IsDomain (B ⊗[k] L) := by
  haveI : Nontrivial A :=
    (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := L)).domain_nontrivial
  haveI : Nontrivial L :=
    (Algebra.TensorProduct.includeRight (R := k) (A := A)).domain_nontrivial
  let φ : A ⊗[k] L →ₐ[k] B ⊗[k] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k L)
  algebraize [φ.toRingHom]
  haveI : IsScalarTower A (A ⊗[k] L) (B ⊗[k] L) := .of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra, φ]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] L) M) (B ⊗[k] L) :=
    IsLocalization.tensorProduct_tensorProduct k L M B
      (by ext; simp [RingHom.algebraMap_toAlgebra, φ])
  have hinj : Function.Injective (algebraMap A (A ⊗[k] L)) :=
    Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k L).injective
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := Algebra.algebraMapSubmonoid (A ⊗[k] L) M)
    (map_le_nonZeroDivisors_of_injective _ hinj hM)

/-- THEOREM (proved, geometric integrality in the function field). The rational functions of
 a geometrically integral scheme remain a domain after any extension of constants.
Locator: `TauCeti/AlgebraicGeometry/Geometrically/FunctionField.lean`,
`isDomain_functionField_tensorProduct_of_geometricallyIntegral`. -/
theorem functionField_tensor_domain {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] (L : Type) [Field L] [Algebra k L] :
    letI := functionFieldAlgebra f
    IsDomain (X.functionField ⊗[k] L) := by
  letI := functionFieldAlgebra f
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  haveI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  letI := sectionsAlgebra f U
  haveI := sections_functionField_tower f U
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have hw : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_top _) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  let s := Spec.map (CommRingCat.ofHom (algebraMap k L))
  haveI : IsIntegral (pullback f s) :=
    pullback_of_geometrically GeometricallyIntegral.geometrically_isIntegral L s
  haveI : Nontrivial (Γ(X, U) ⊗[k] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k _ _
      (algebraMap k Γ(X, U)).injective (algebraMap k L).injective
  let e : Spec (.of (Γ(X, U) ⊗[k] L)) ≅ pullback hU.fromSpec (pullback.fst f s) :=
    (pullbackSpecIso k Γ(X, U) L).symm ≪≫ pullback.congrHom hw.symm rfl ≪≫
      (pullbackRightPullbackFstIso _ _ _).symm
  haveI : IsIntegral (Spec (.of (Γ(X, U) ⊗[k] L))) :=
    isIntegral_of_isOpenImmersion (e.hom ≫ pullback.snd _ _)
  haveI : IsDomain (Γ(X, U) ⊗[k] L) :=
    (affine_isIntegral_iff (.of (Γ(X, U) ⊗[k] L))).mp inferInstance
  exact tensor_domain_of_localization (nonZeroDivisors Γ(X, U)) le_rfl

/-- THEOREM (proved). A field remaining integral over an algebraic closure has exact constants.
Locator: `TauCeti/FieldTheory/AlgebraicClosure.lean`,
`algebraicClosure_eq_bot_of_isDomain_tensorProduct`. -/
private theorem exact_constants_of_tensor_domain {k K : Type} [Field k] [Field K] [Algebra k K]
    [IsDomain (K ⊗[k] AlgebraicClosure k)] : algebraicClosure k K = ⊥ := by
  let L := AlgebraicClosure k
  let E := algebraicClosure k K
  let φ : L ⊗[k] E →ₐ[L] L ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom k E K)
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L)
      (IsScalarTower.toAlgHom k E K).toLinearMap Subtype.val_injective
  haveI : IsDomain (L ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K L).toMulEquiv.isDomain_iff.mp inferInstance
  haveI : IsDomain (L ⊗[k] E) := hφ.isDomain φ.toRingHom
  have hrank := (LinearEquiv.ofBijective (Algebra.linearMap L (L ⊗[k] E))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := L ⊗[k] E))).lift_rank_eq
  rw [Module.rank_self, Module.rank_baseChange, Cardinal.lift_one, Cardinal.lift_lift,
    eq_comm, Cardinal.lift_eq_one] at hrank
  exact IntermediateField.rank_eq_one_iff.mp hrank

/-- THEOREM (proved, exact constants in S2a). The ground field is integrally closed in the
actual function field of a geometrically integral scheme.
Locator: `TauCeti/AlgebraicGeometry/Geometrically/FunctionField.lean`,
`isIntegrallyClosedIn_functionField_of_geometricallyIntegral`. -/
theorem functionField_exact_constants {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] :
    letI := functionFieldAlgebra f
    IsIntegrallyClosedIn k X.functionField := by
  letI := functionFieldAlgebra f
  haveI := functionField_tensor_domain f (AlgebraicClosure k)
  exact TauCeti.algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp exact_constants_of_tensor_domain

/-- THEOREM (proved). The underlying scheme in the project's abelian-variety definition is
integral. Locator: `ZInQKernel/HDecomp/Objects.lean`, fields of `PkgI3.AbVar`;
Mathlib, `GeometricallyIntegral.isIntegral_of_subsingleton`. -/
theorem abelian_scheme_integral {k : Type} [Field k] (G : Over (Spec (.of k)))
    [GeometricallyIntegral G.hom] : IsIntegral G.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton G.hom

/-- THEOREM (proved, S2a part 1). For an actual one-dimensional proper smooth geometrically
integral group scheme over the rationals, its generic stalk is a one-variable function field
with exact rational constants. Locator: `ZInQKernel/HDecomp/Objects.lean`, `PkgI3.AbVar`;
`isFunctionField_of_dimension_one` and `functionField_exact_constants` above. -/
theorem abelian_functionField (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G]
    [IsProper G.hom] [Smooth G.hom] [GeometricallyIntegral G.hom]
    [IsIntegral G.left] (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsFunctionField ℚ G.left.functionField ∧
      IsIntegrallyClosedIn ℚ G.left.functionField :=
  ⟨isFunctionField_of_dimension_one G.hom hdim, functionField_exact_constants G.hom⟩

end ZInQ.Contrib.RC53Assist.AbelianCurve
