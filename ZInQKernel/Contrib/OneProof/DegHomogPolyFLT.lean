import ZInQKernel.Contrib.OneProof.DegEqDetTate.Reduction
import ZInQKernel.Contrib.OneProof.CharPolyPort.FinrankGeneric
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Flatness
import ZInQKernel.Contrib.CloudB3W16Torsion.RelativeBridges
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle

/-!
# charpoly-port: deg-det's `DegHomogPoly` in every characteristic, from Anthropic's FLT library

Task charpoly-port (2026-11-17), report `docs/research/charpoly-port.md`, scratch `scratch/charpoly-port/`.

`DegDet.DegHomogPoly` (deg-det, `DegEqDetTate/Reduction.lean`): over an algebraically closed field
`k` of any characteristic, `x ↦ deg(∑ xᵢ eᵢ)` is a homogeneous rational polynomial of degree `2 dim A`,
with `deg = CharPolyEll.degEnd` the function-field degree.

The polynomiality is Anthropic's (Apache-2.0) theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle`,
vendored with its whole proof under `CharPolyPort/Vendor/AnthropicFLT` (59 new modules over the
`CloudB3W16Torsion` vendor). Its degree is `RelativeGroupLaw.endDegree`, the rank of the kernel group
scheme. This file

* transports the theorem to `PkgI3.AbVar` through `CloudB3W16Torsion/RelativeBridges.lean`
  (`degHomogPolyEndDegree`, no hypothesis);
* compares `endDegree` with `degEnd` (`degEnd_eq_endDegree`) from two glue statements
  (`FinrankGenericEqDegEnd`, `FiniteEndSurjective`), the vendored FLT lemmas
  `isFinite_of_isFinite_endKerStr` and `surjective_and_endDegree_eq_finrank_of_isFinite_of_flat`;
* proves both glue statements: `finiteEndSurjective` (a finite endomorphism is flat by FLT's
  miracle-flatness argument, `flat_of_isFinite`, hence surjective) and `finrankGenericPoint` (the rank
  at the generic point is the function-field degree, `CharPolyPort/FinrankGeneric.lean`);
* concludes **`degHomogPoly : DegDet.DegHomogPoly`, with no hypothesis, in every characteristic**.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj

noncomputable section

namespace ZInQ.Contrib.OneProof.DegPolyFLT

open ZInQ.Contrib.OneProof.CharPolyEll

variable {k : Type} [Field k]

/-! ## 1. From `PkgI3.AbVar` to a relative group law -/

/-- The underlying group object of `A`. -/
abbrev grp (A : PkgI3.AbVar k) : Grp (Over (Spec (CommRingCat.of k))) := Grp.mk A.X

instance (A : PkgI3.AbVar k) : PkgI2.IsAbelianVariety (grp A) :=
  ⟨A.proper, A.smooth, A.geomInt⟩

/-- Anthropic's relative group law of `A` (the genuine law of `A.grp`). -/
abbrev law (A : PkgI3.AbVar k) : RelativeGroupLaw k A.X.hom :=
  ZInQ.Contrib.CloudB3W16Torsion.relativeLaw (grp A)

theorem law_comm (A : PkgI3.AbVar k) : (law A).IsCommutative :=
  ZInQ.Contrib.CloudB3W16Torsion.relativeLaw_commutative (grp A)

/-- Endomorphisms of `A` over `Spec k`, as FLT's `SchemeHomOver`. -/
abbrev EndPt (A : PkgI3.AbVar k) : Type := SchemeHomOver A.X.hom A.X.hom

/-- The commutative group of `EndPt A` used in FLT's statement (`pointCommGroup`). -/
abbrev endPtGroup (A : PkgI3.AbVar k) : CommGroup (EndPt A) :=
  (law A).pointCommGroup (law_comm A) A.X.hom

/-- An endomorphism as a `SchemeHomOver`. -/
def toPt {A : PkgI3.AbVar k} (ψ : PkgI3.AbVar.End A) : EndPt A := ⟨ψ.hom.left, Over.w ψ.hom⟩

@[simp] theorem toPt_coe {A : PkgI3.AbVar k} (ψ : PkgI3.AbVar.End A) : (toPt ψ).1 = ψ.hom.left := rfl

theorem toPt_add {A : PkgI3.AbVar k} (ψ χ : PkgI3.AbVar.End A) :
    toPt (ψ + χ) = (law A).mul A.X.hom (toPt ψ) (toPt χ) := by
  apply Subtype.ext
  rfl

theorem toPt_zero (A : PkgI3.AbVar k) : toPt (0 : PkgI3.AbVar.End A) = (law A).one A.X.hom := by
  apply Subtype.ext
  rfl

/-- `toPt` as a homomorphism `End A → Additive (EndPt A)`. -/
def toPtHom (A : PkgI3.AbVar k) :
    letI := endPtGroup A
    PkgI3.AbVar.End A →+ Additive (EndPt A) :=
  letI := endPtGroup A
  { toFun := fun ψ => Additive.ofMul (toPt ψ)
    map_zero' := by
      change Additive.ofMul (toPt (0 : PkgI3.AbVar.End A)) = Additive.ofMul ((law A).one A.X.hom)
      rw [toPt_zero]
    map_add' := fun ψ χ => by
      change Additive.ofMul (toPt (ψ + χ)) = Additive.ofMul ((law A).mul A.X.hom (toPt ψ) (toPt χ))
      rw [toPt_add] }

theorem toPt_sum (A : PkgI3.AbVar k) {r : ℕ} (e : Fin r → PkgI3.AbVar.End A) (x : Fin r → ℤ) :
    toPt (∑ i, x i • e i) = (letI := endPtGroup A; ∏ i, toPt (e i) ^ x i) := by
  letI := endPtGroup A
  have h := map_sum (toPtHom A) (fun i => x i • e i) Finset.univ
  simp only [map_zsmul] at h
  apply Additive.ofMul.injective
  rw [ofMul_prod]
  simp only [ofMul_zpow]
  exact h

/-- An endomorphism of `A` respects FLT's group law on points (FLT's hypothesis `hα`). -/
theorem toPt_hom {A : PkgI3.AbVar k} (ψ : PkgI3.AbVar.End A) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t A.X.hom) :
    NeronModelInfra.schemeHomOverComp ((law A).mul t x y) (toPt ψ) =
      (law A).mul t (NeronModelInfra.schemeHomOverComp x (toPt ψ))
        (NeronModelInfra.schemeHomOverComp y (toPt ψ)) := by
  apply Subtype.ext
  change ((ZInQ.Contrib.CloudB3W16Torsion.pointOverEquiv (grp A) t).symm x *
      (ZInQ.Contrib.CloudB3W16Torsion.pointOverEquiv (grp A) t).symm y).left ≫ ψ.hom.left =
    ((ZInQ.Contrib.CloudB3W16Torsion.pointOverEquiv (grp A) t).symm
        ⟨x.1 ≫ ψ.hom.left, _⟩ *
      (ZInQ.Contrib.CloudB3W16Torsion.pointOverEquiv (grp A) t).symm ⟨y.1 ≫ ψ.hom.left, _⟩).left
  rw [← Over.comp_left, MonObj.mul_comp]
  rfl

/-! ## 2. The degree polynomial for FLT's `endDegree` (no hypothesis) -/

/-- **Anthropic's degree polynomial on `PkgI3.AbVar`, every characteristic (proved).** For `k`
algebraically closed, `A` an abelian variety of dimension `g` and `e₁, …, e_r ∈ End(A)`,
`x ↦ endDegree(∑ xᵢ eᵢ)` is a homogeneous rational polynomial of degree `2g`, where `endDegree` is
the rank of the kernel group scheme (`0` if the kernel is not finite). -/
theorem degHomogPolyEndDegree (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (r : ℕ)
    (e : Fin r → PkgI3.AbVar.End A) :
    ∃ (g : ℕ) (N : MvPolynomial (Fin r) ℚ), A.dim = (g : WithBot ℕ∞) ∧ N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin r → ℤ, (((law A).endDegree (toPt (∑ i, x i • e i)) : ℕ) : ℚ) =
        MvPolynomial.eval (fun i => (x i : ℚ)) N := by
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  haveI := ZInQ.Contrib.CloudB3W16Torsion.smoothOfRelativeDimension (grp A) g hg
  obtain ⟨P, hP, hev⟩ :=
    RelativeGroupLaw.exists_isHomogeneous_eval_eq_endDegree_of_abelianSchemePropertyBundle k A.X.hom
      (law A) (law_comm A) (ZInQ.Contrib.CloudB3W16Torsion.abelianSchemePropertyBundle (grp A)) g
      (fun i => toPt (e i)) (fun i T t x y => toPt_hom (e i) t x y)
  refine ⟨g, P, hg, hP, fun x => ?_⟩
  rw [toPt_sum]
  exact hev x

/-! ## 3. `endDegree = degEnd`, from two glue statements -/

attribute [local instance] isIntegral_left

/-- **GLUE (proved below): the rank of an isogeny at the generic point is its function-field degree.** For an
isogeny `ψ` of an abelian variety (finite, surjective, hence flat), Mathlib's rank
`Scheme.Hom.finrank ψ (ψ η)` of the finite flat morphism at the generic point `ψ η = η` equals
`degEnd ψ = [K(A) : ψ^*K(A)]`. Locally: for `Spec S → Spec R` finite flat with `R ⊆ S` domains,
`rank_{R_(0)} S_(0) = [Frac S : Frac R]` (EGA IV 2.? / Stacks 02KA; standard commutative algebra). -/
def FinrankGenericEqDegEnd : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A),
    PkgI3.AbVar.IsIsogenyMor ψ.hom →
      Scheme.Hom.finrank ψ.hom.left (ψ.hom.left (genericPoint A.X.left)) = degEnd ψ

/-- **GLUE (proved below, `finiteEndSurjective`): a finite endomorphism of an abelian variety is surjective.** A finite morphism
preserves dimension, and a proper closed subset of the irreducible `A` has smaller dimension
(Mumford, *Abelian varieties*, §4 Application 1 setting; dimension theory, Hartshorne II Ex. 3.22). -/
def FiniteEndSurjective : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A),
    IsFinite ψ.hom.left → Surjective ψ.hom.left

/-- **A finite endomorphism of an abelian variety is flat (proved).** Miracle flatness at each
stalk: regular local rings of equal dimension with zero-dimensional fibre. This is the argument of
the vendored FLT proof `flat_schemeNsmul_of_isFinite_of_field` (written there for `[n]`), run for an
arbitrary finite endomorphism over `k`. -/
theorem flat_of_isFinite {k : Type} [Field k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A)
    [IsFinite ψ.hom.left] : Flat ψ.hom.left := by
  haveI : LocallyOfFiniteType A.X.hom := inferInstance
  haveI : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x
  algebraize [(ψ.hom.left.stalkMap x).hom]
  haveI : IsRegularLocalRing (A.X.left.presheaf.stalk x) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalkFLT (f := A.X.hom) x
  haveI : IsRegularLocalRing (A.X.left.presheaf.stalk (ψ.hom.left.base x)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalkFLT (f := A.X.hom) (ψ.hom.left.base x)
  haveI : IsNoetherianRing (A.X.left.presheaf.stalk x) := inferInstance
  haveI : IsLocalHom (algebraMap
      ↑(A.X.left.presheaf.stalk (ψ.hom.left.base x)) ↑(A.X.left.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (ψ.hom.left.stalkMap x).hom)
  have hfib : ringKrullDim (↑(A.X.left.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal ↑(A.X.left.presheaf.stalk (ψ.hom.left.base x))).map
        (algebraMap ↑(A.X.left.presheaf.stalk (ψ.hom.left.base x)) ↑(A.X.left.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero ψ.hom.left x
  have hdim : ringKrullDim (A.X.left.presheaf.stalk x) =
      ringKrullDim (A.X.left.presheaf.stalk (ψ.hom.left.base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism
      (f := A.X.hom) ψ.hom.left (Over.w ψ.hom) x
  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      ↑(A.X.left.presheaf.stalk (ψ.hom.left.base x)) ↑(A.X.left.presheaf.stalk x) hfib hdim

/-- **`FiniteEndSurjective` (proved)**: finite ⇒ flat (`flat_of_isFinite`) ⇒ surjective (vendored FLT
`surjective_and_endDegree_eq_finrank_of_isFinite_of_flat`). -/
theorem finiteEndSurjective : FiniteEndSurjective := by
  intro k _ _ A ψ hfin
  haveI : IsFinite ψ.hom.left := hfin
  haveI : IsFinite (toPt ψ).1 := hfin
  haveI : Flat (toPt ψ).1 := flat_of_isFinite A ψ
  exact ⟨(RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat k A.X.hom (law A)
    (toPt ψ)).1⟩

/-- **GLUE (proved below, `finrankGenericPoint`), general form: the rank of a finite flat surjective morphism of integral schemes at
the generic point is the degree of the function-field extension.** For `f : X ⟶ Y` finite, flat and
surjective with `X`, `Y` integral, Mathlib's `Scheme.Hom.finrank f` at `f(η_X) = η_Y` equals
`[K(X) : K(Y)]`, `K(Y) → K(X)` being the stalk map at the generic point. On an affine chart
`Spec S → Spec R` (`R ⊆ S` domains, `S` finite flat over `R`) it says
`rank_{R_(0)} S_(0) = [Frac S : Frac R]`, because `S ⊗_R Frac R` is a domain finite over the field
`Frac R`, hence equal to `Frac S` (standard commutative algebra; Stacks 02KA for the rank). No
abelian-variety input. -/
def FinrankGenericPoint : Prop :=
  ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] [Flat f],
    Function.Surjective f →
      letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
      Scheme.Hom.finrank f (f (genericPoint X)) =
        Module.finrank (Y.presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X))

/-- `FinrankGenericEqDegEnd` from the general `FinrankGenericPoint` (proved). -/
theorem finrankGenericEqDegEnd_of_finrankGenericPoint (h : FinrankGenericPoint) :
    FinrankGenericEqDegEnd := by
  intro k _ _ A ψ hiso
  classical
  haveI : IsFinite ψ.hom.left := hiso.1
  haveI : Flat ψ.hom.left := flat_of_isFinite A ψ
  unfold degEnd
  rw [if_pos hiso]
  exact h ψ.hom.left hiso.2.surj

/-- **`degEnd = endDegree`** (proved from the two glue statements). -/
theorem degEnd_eq_endDegree (h1 : FinrankGenericEqDegEnd) (h2 : FiniteEndSurjective)
    (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A) :
    degEnd ψ = (law A).endDegree (toPt ψ) := by
  classical
  by_cases hiso : PkgI3.AbVar.IsIsogenyMor ψ.hom
  · haveI : IsFinite ψ.hom.left := hiso.1
    haveI : Flat ψ.hom.left := ZInQ.Contrib.MilneQuasiInverse.finite_surjective_abVarHom_flat ψ hiso
    haveI : IsFinite (toPt ψ).1 := hiso.1
    haveI : Flat (toPt ψ).1 := ZInQ.Contrib.MilneQuasiInverse.finite_surjective_abVarHom_flat ψ hiso
    obtain ⟨-, -, h⟩ :=
      RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat k A.X.hom (law A) (toPt ψ)
    rw [h (ψ.hom.left (genericPoint A.X.left))]
    exact (h1 k A ψ hiso).symm
  · have h0 : degEnd ψ = 0 := by
      unfold degEnd
      rw [if_neg hiso]
    rw [h0, RelativeGroupLaw.endDegree_of_not_isFinite]
    intro hfin
    haveI := hfin
    have hf : IsFinite (toPt ψ).1 :=
      RelativeGroupLaw.isFinite_of_isFinite_endKerStr k A.X.hom (law A) (toPt ψ)
        (fun t x y => toPt_hom ψ t x y)
    exact hiso ⟨hf, h2 k A ψ hf⟩

/-- **GLUE (proved below, `degEndEqEndDegree`): deg-det's degree equals Anthropic's degree.** For every endomorphism `ψ` of an
abelian variety over an algebraically closed field, `degEnd ψ = [K(A) : ψ^*K(A)]` (`0` for a
non-isogeny) equals `endDegree ψ`, the rank of the kernel group scheme (`0` if the kernel is not
finite). Mumford, *Abelian varieties*, §4 (degree of an isogeny = order of its kernel scheme;
UNVERIFIED locator); reduced below to `FinrankGenericEqDegEnd` and `FiniteEndSurjective`. -/
def DegEndEqEndDegree : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A),
    degEnd ψ = (law A).endDegree (toPt ψ)

/-- `DegEndEqEndDegree` from the two glue statements (proved). -/
theorem degEndEqEndDegree_of_glue (h1 : FinrankGenericEqDegEnd) (h2 : FiniteEndSurjective) :
    DegEndEqEndDegree :=
  fun k _ _ A ψ => degEnd_eq_endDegree h1 h2 k A ψ

/-! ## 4. `DegHomogPoly` -/

/-- **deg-det's `DegHomogPoly`, every characteristic, from the degree comparison (proved).** -/
theorem degHomogPoly_of_degEndEq (h : DegEndEqEndDegree) : DegDet.DegHomogPoly := by
  intro k _ _ A r e
  obtain ⟨g, N, hg, hN, hev⟩ := degHomogPolyEndDegree k A r e
  refine ⟨g, N, hg, hN, fun x => ?_⟩
  rw [h k A]
  exact hev x

/-- **deg-det's `DegHomogPoly`, every characteristic, from the two glue statements (proved).** -/
theorem degHomogPoly_of_glue (h1 : FinrankGenericEqDegEnd) (h2 : FiniteEndSurjective) :
    DegDet.DegHomogPoly :=
  degHomogPoly_of_degEndEq (degEndEqEndDegree_of_glue h1 h2)

/-- **deg-det's `DegHomogPoly`, every characteristic, from `FinrankGenericEqDegEnd` alone (proved).** -/
theorem degHomogPoly_of_finrankGeneric (h1 : FinrankGenericEqDegEnd) : DegDet.DegHomogPoly :=
  degHomogPoly_of_glue h1 finiteEndSurjective

/-- **deg-det's `DegHomogPoly`, every characteristic, from the general `FinrankGenericPoint` (proved).** -/
theorem degHomogPoly_of_finrankGenericPoint (h : FinrankGenericPoint) : DegDet.DegHomogPoly :=
  degHomogPoly_of_finrankGeneric (finrankGenericEqDegEnd_of_finrankGenericPoint h)

/-! ## 5. Everything proved -/

/-- **`FinrankGenericPoint` (proved)**, from `CharPolyPort.finrank_genericPoint`. -/
theorem finrankGenericPoint : FinrankGenericPoint := by
  intro X Y _ _ f _ _ hf
  exact CharPolyPort.finrank_genericPoint f hf

/-- **`DegEndEqEndDegree` (proved).** -/
theorem degEndEqEndDegree : DegEndEqEndDegree :=
  degEndEqEndDegree_of_glue (finrankGenericEqDegEnd_of_finrankGenericPoint finrankGenericPoint)
    finiteEndSurjective

/-- **deg-det's `DegHomogPoly`, in every characteristic, with no hypothesis (proved).** Over an
algebraically closed field `k` of any characteristic, `x ↦ degEnd(∑ xᵢ eᵢ)` is a homogeneous rational
polynomial of degree `2 dim A` (Mumford §19), from Anthropic's FLT degree polynomial and the degree
comparison above. -/
theorem degHomogPoly : DegDet.DegHomogPoly :=
  degHomogPoly_of_degEndEq degEndEqEndDegree

end ZInQ.Contrib.OneProof.DegPolyFLT
