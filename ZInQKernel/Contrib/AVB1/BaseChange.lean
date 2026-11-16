import ZInQKernel.Contrib.AbVarBC.Tate

/-!
# av-b1, I: homomorphisms and Tate modules under base change to `K̄`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task av-b1, 2026-11-13).

For the kernel's abelian varieties (`PkgI3.AbVar`, `ZInQKernel/HDecomp/Objects.lean`) over a field
`K` and a field extension `L/K`:
* `bcHom A B : Hom_K(A, B) →+ Hom_L(A_L, B_L)` (`Over.pullback` on morphisms), **injective**
  (`bcHom_injective`: the projection `A_L → A` is flat and surjective, hence an epimorphism of
  schemes, Mathlib's `epi_of_flat_of_surjective`);
* naturality of g9-abvarbc's point and Tate maps: `ptBC_ptMap`, `tateBC_homT`;
* for `L = K̄ = AlgebraicClosure K` and `κ = algebraMap K̄ (AlgebraicClosure K̄)` (an isomorphism,
  `K̄` being algebraically closed): `tateBC A κ ℓ : T_ℓ(A) → T_ℓ(A_{K̄})` is **bijective**
  (`tateBC_bijective_closure`), with no hypothesis on `ℓ` or on the characteristic.

All names are in `ZInQ.Contrib.AVB1`; the kernel's objects are written `_root_.PkgI3.…` so that the
file can be copied over a renamed copy of the objects (`_root_.PkgI3 → _root_.HDec.PkgI3`, as in
leaf-fold3's `mk_abvarbc.py`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AVB1

open ZInQ.Contrib.AbVarBC

section BCHom

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- `Over.pullback (Spec L → Spec K)` on a homomorphism is a homomorphism. -/
noncomputable def bcHomFun {A B : _root_.PkgI3.AbVar K} (f : _root_.PkgI3.AbVar.Hom A B) :
    _root_.PkgI3.AbVar.Hom (A.baseChange L) (B.baseChange L) :=
  @_root_.PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (B.baseChange L)
    ((Over.pullback (sK K L)).map f.hom)
    (by exact Functor.map.instIsMonHom (F := Over.pullback (sK K L)) (f := f.hom))

theorem bcHomFun_hom {A B : _root_.PkgI3.AbVar K} (f : _root_.PkgI3.AbVar.Hom A B) :
    (bcHomFun (L := L) f).hom = (Over.pullback (sK K L)).map f.hom := rfl

variable (L) in
/-- **Base change of homomorphisms** `Hom_K(A, B) →+ Hom_L(A_L, B_L)`. -/
noncomputable def bcHom (A B : _root_.PkgI3.AbVar K) :
    _root_.PkgI3.AbVar.Hom A B →+ _root_.PkgI3.AbVar.Hom (A.baseChange L) (B.baseChange L) where
  toFun f := bcHomFun f
  map_zero' := by
    apply _root_.PkgI3.AbVar.Hom.ext'
    rw [bcHomFun_hom, _root_.PkgI3.AbVar.Hom.hom_zero, _root_.PkgI3.AbVar.Hom.hom_zero]
    exact Functor.map_one (Over.pullback (sK K L))
  map_add' f g := by
    apply _root_.PkgI3.AbVar.Hom.ext'
    rw [bcHomFun_hom, _root_.PkgI3.AbVar.Hom.hom_add, _root_.PkgI3.AbVar.Hom.hom_add,
      bcHomFun_hom, bcHomFun_hom]
    exact Functor.map_mul (Over.pullback (sK K L)) f.hom g.hom

theorem bcHom_hom {A B : _root_.PkgI3.AbVar K} (f : _root_.PkgI3.AbVar.Hom A B) :
    (bcHom L A B f).hom = (Over.pullback (sK K L)).map f.hom := rfl

/-- The projection `A_L → A` is an epimorphism of schemes (flat and surjective). -/
theorem epi_pullback_fst (X : Over (Spec (CommRingCat.of K))) :
    Epi (pullback.fst X.hom (sK K L)) := by
  haveI : Surjective (sK K L) := by
    constructor
    intro y
    exact ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  haveI : Flat (sK K L) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    rw [CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact Flat.epi_of_flat_of_surjective _

/-- **Base change of homomorphisms is injective.** -/
theorem bcHom_injective (A B : _root_.PkgI3.AbVar K) : Function.Injective (bcHom L A B) := by
  intro f g h
  apply _root_.PkgI3.AbVar.Hom.ext'
  have h1 : (Over.pullback (sK K L)).map f.hom = (Over.pullback (sK K L)).map g.hom := by
    rw [← bcHom_hom, ← bcHom_hom, h]
  have h2 : ((Over.pullback (sK K L)).map f.hom).left ≫ pullback.fst B.X.hom (sK K L) =
      ((Over.pullback (sK K L)).map g.hom).left ≫ pullback.fst B.X.hom (sK K L) := by
    rw [h1]
  simp only [Over.pullback_map_left, pullback.lift_fst] at h2
  haveI := epi_pullback_fst (L := L) A.X
  apply Over.OverMorphism.ext
  exact (cancel_epi _).1 h2

end BCHom

/-! ## Naturality of the point and Tate maps -/

section Nat

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem bcPt_ptMap {A B : _root_.PkgI3.AbVar K}
    (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (f : _root_.PkgI3.AbVar.Hom A B) (p : (A.baseChange L).Pt Ω) :
    bcPt B Ω (_root_.PkgI3.AbVar.ptMap (bcHom L A B f) p) =
      _root_.PkgI3.AbVar.ptMap f (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (p ≫ (Over.pullback (sK K L)).map f.hom) =
    ((ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p) ≫ f.hom
  have hnat := Adjunction.homEquiv_naturality_right_symm (Over.mapPullbackAdj (sK K L))
    (p : _root_.PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X) f.hom
  erw [hnat]
  rw [Category.assoc]

theorem bcPt_symm_ptMap {A B : _root_.PkgI3.AbVar K}
    (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (f : _root_.PkgI3.AbVar.Hom A B) (x : A.Pt Ω) :
    (bcPt B Ω).symm (_root_.PkgI3.AbVar.ptMap f x) =
      _root_.PkgI3.AbVar.ptMap (bcHom L A B f) ((bcPt A Ω).symm x) := by
  rw [MulEquiv.symm_apply_eq, bcPt_ptMap, MulEquiv.apply_symm_apply]

theorem extPt_ptMap {A B : _root_.PkgI3.AbVar K} {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂]
    [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) (f : _root_.PkgI3.AbVar.Hom A B) (p : A.Pt Ω) :
    extPt B κ (_root_.PkgI3.AbVar.ptMap f p) = _root_.PkgI3.AbVar.ptMap f (extPt A κ p) := by
  show extHom κ ≫ p ≫ f.hom = (extHom κ ≫ p) ≫ f.hom
  rw [Category.assoc]

theorem ptBC_ptMap {A B : _root_.PkgI3.AbVar K} (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (f : _root_.PkgI3.AbVar.Hom A B) (p : A.Pt (AlgebraicClosure K)) :
    ptBC B κ (_root_.PkgI3.AbVar.ptMap f p) =
      _root_.PkgI3.AbVar.ptMap (bcHom L A B f) (ptBC A κ p) := by
  change (bcPt B (AlgebraicClosure L)).symm (extPt B κ (_root_.PkgI3.AbVar.ptMap f p)) =
    _root_.PkgI3.AbVar.ptMap (bcHom L A B f) ((bcPt A (AlgebraicClosure L)).symm (extPt A κ p))
  rw [extPt_ptMap, bcPt_symm_ptMap]

theorem tateBC_homT {A B : _root_.PkgI3.AbVar K} (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (ℓ : ℕ) [Fact ℓ.Prime] (f : _root_.PkgI3.AbVar.Hom A B) (x : A.T ℓ) :
    tateBC B κ ℓ (_root_.PkgI3.AbVar.homT f x) =
      _root_.PkgI3.AbVar.homT (bcHom L A B f) (tateBC A κ ℓ x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (ptBC_ptMap κ f (Additive.toMul (x.1 n)))

end Nat

/-! ## Base change to the algebraic closure: `T_ℓ(A) ≅ T_ℓ(A_{K̄})` -/

section Closure

variable {K : Type} [Field K]

/-- `K̄ → \overline{K̄}`, a `K`-embedding. -/
noncomputable abbrev κbar (K : Type) [Field K] :
    AlgebraicClosure K →ₐ[K] AlgebraicClosure (AlgebraicClosure K) :=
  IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure (AlgebraicClosure K))

theorem κbar_bijective (K : Type) [Field K] : Function.Bijective (κbar K) :=
  ⟨(κbar K).toRingHom.injective,
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure K)).2⟩

/-- `κbar` as a `K`-isomorphism. -/
noncomputable def κbarEquiv (K : Type) [Field K] :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure (AlgebraicClosure K) :=
  AlgEquiv.ofBijective (κbar K) (κbar_bijective K)

theorem extPt_κbar_surjective (A : _root_.PkgI3.AbVar K) :
    Function.Surjective (extPt A (κbar K)) := by
  intro q
  refine ⟨trHom (κbarEquiv K).symm ≫ q, ?_⟩
  rw [extPt_apply, ← Category.assoc]
  have : extHom (κbar K) ≫ trHom (κbarEquiv K).symm = 𝟙 _ := by
    have h := trHom_comp_symm (K := K) (κbarEquiv K)
    have he : extHom (κbar K) = trHom (κbarEquiv K) := by
      apply Over.OverMorphism.ext
      rw [extHom_left, trHom_left]
      rfl
    rw [he, h]
  rw [this, Category.id_comp]

theorem ptBC_κbar_surjective (A : _root_.PkgI3.AbVar K) :
    Function.Surjective (ptBC A (κbar K)) :=
  (bcPt A (AlgebraicClosure (AlgebraicClosure K))).symm.surjective.comp
    (extPt_κbar_surjective A)

/-- **`T_ℓ(A) → T_ℓ(A_{K̄})` is bijective** (no hypothesis). -/
theorem tateBC_bijective_closure (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective (tateBC A (κbar K) ℓ) :=
  tateBC_bijective_of_torsionDescends A (κbar K) ℓ fun _ q _ => ptBC_κbar_surjective A q

end Closure

end ZInQ.Contrib.AVB1
