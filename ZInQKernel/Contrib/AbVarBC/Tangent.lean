import ZInQKernel.Contrib.AbVarBC.Torsion
import ZInQKernel.Contrib.AbVarBC.Mul

/-!
# Base change of abelian varieties, VIII: tangent vectors as dual-number points

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

§1 For an affine open `U` of a scheme `X` and a local ring `Λ`, a morphism `p : Spec Λ → X`
sending the closed point into `U` is the same as a ring map `ptRing p : Γ(X, U) → Λ`
(`eq_ofRing_ptRing`, `ptRing_ofRing`, `ptRing_specMap_comp`, `ptRing_comp`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.AbVarBC.Tangent

/-! ## §1. Points of an affine open -/

section Gen

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
  {Λ : CommRingCat.{0}} [IsLocalRing Λ]

/-- The ring map `Γ(X, U) → Λ` of a `Λ`-point whose closed point lies in `U`. -/
def ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) : Γ(X, U) ⟶ Λ :=
  p.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge ≫ (Scheme.ΓSpecIso Λ).hom

theorem ptRing_congr {p q : Spec Λ ⟶ X} (e : p = q) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) : ptRing p hp = ptRing q hq := by
  subst e; rfl

/-- The point attached to a ring map `Γ(X, U) → Λ`. -/
def ofRing (φ : Γ(X, U) ⟶ Λ) : Spec Λ ⟶ X := Spec.map φ ≫ hU.fromSpec

theorem ofRing_mem (φ : Γ(X, U) ⟶ Λ) : ofRing hU φ (IsLocalRing.closedPoint Λ) ∈ U := by
  change ofRing hU φ _ ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem eq_ofRing_ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) :
    p = ofRing hU (ptRing p hp) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top _)
    (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [ofRing, ptRing, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ptRing_ext (hU : IsAffineOpen U) {p q : Spec Λ ⟶ X} (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) (h : ptRing p hp = ptRing q hq) : p = q := by
  rw [eq_ofRing_ptRing hU p hp, eq_ofRing_ptRing hU q hq, h]

theorem ptRing_ofRing (φ : Γ(X, U) ⟶ Λ) : ptRing (ofRing hU φ) (ofRing_mem hU φ) = φ := by
  have h := eq_ofRing_ptRing hU (ofRing hU φ) (ofRing_mem hU φ)
  unfold ofRing at h
  rw [cancel_mono] at h
  exact (Spec.map_injective h).symm

/-- Naturality in the local ring. -/
theorem ptRing_specMap_comp (hU : IsAffineOpen U) {Λ' : CommRingCat.{0}} [IsLocalRing Λ'] (ρ : Λ ⟶ Λ')
    (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (Spec.map ρ ≫ p) (IsLocalRing.closedPoint Λ') ∈ U) :
    ptRing (Spec.map ρ ≫ p) hp' = ptRing p hp ≫ ρ := by
  have e : Spec.map ρ ≫ p = ofRing hU (ptRing p hp ≫ ρ) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU _), ptRing_ofRing]

/-- Naturality in the scheme. -/
theorem ptRing_comp (hU : IsAffineOpen U) {Y : Scheme.{0}} (f : X ⟶ Y) {U' : Y.Opens} (hU' : IsAffineOpen U')
    (hle : U ≤ f ⁻¹ᵁ U') (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (p ≫ f) (IsLocalRing.closedPoint Λ) ∈ U') :
    ptRing (p ≫ f) hp' = f.appLE U' U hle ≫ ptRing p hp := by
  have e : p ≫ f = ofRing hU' (f.appLE U' U hle ≫ ptRing p hp) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU' hU hle,
      ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU' _), ptRing_ofRing]

end Gen

/-! ## §2. Dual-number points of a `K`-scheme -/

section Dual

open TrivSqZeroExt

variable {K : Type} [Field K]

instance isLocalRing_tsze (V : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] : IsLocalRing (TrivSqZeroExt K V) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    have h1 : a.fst + b.fst = 1 := by simpa using congrArg TrivSqZeroExt.fst h
    rcases eq_or_ne a.fst 0 with ha | ha
    · right
      rw [isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
      rw [ha, zero_add] at h1
      rw [h1]
      exact one_ne_zero
    · left
      rw [isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
      exact ha

/-- `Spec Λ` as a `K`-scheme. -/
def ptR (Λ : Type) [CommRing Λ] [Algebra K Λ] : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Λ)))

/-- `Spec ρ` over `K` for a `K`-algebra map `ρ`. -/
def specHom {Λ Λ' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    (ρ : Λ →ₐ[K] Λ') : ptR (K := K) Λ' ⟶ ptR Λ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (ρ : Λ →+* Λ'))) (by
    simp only [ptR, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem specHom_left {Λ Λ' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    (ρ : Λ →ₐ[K] Λ') :
    (specHom ρ).left = Spec.map (CommRingCat.ofHom (ρ : Λ →+* Λ')) := rfl

theorem specHom_comp {Λ Λ' Λ'' : Type} [CommRing Λ] [Algebra K Λ] [CommRing Λ'] [Algebra K Λ']
    [CommRing Λ''] [Algebra K Λ''] (ρ : Λ →ₐ[K] Λ') (ρ' : Λ' →ₐ[K] Λ'') :
    specHom ρ' ≫ specHom ρ = specHom (ρ'.comp ρ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem specHom_id {Λ : Type} [CommRing Λ] [Algebra K Λ] :
    specHom (AlgHom.id K Λ) = 𝟙 (ptR Λ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id Λ)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

variable (A : PkgI3.AbVar K)

/-- The origin of `A` as a morphism `Spec K → A`. -/
def orig : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left

/-- The trivial point is `Spec Λ → Spec K → A` through the origin. -/
theorem one_left {Λ : Type} [CommRing Λ] [Algebra K Λ] :
    (1 : ptR (K := K) Λ ⟶ A.X).left =
      Spec.map (CommRingCat.ofHom (algebraMap K Λ)) ≫ orig A := by
  rw [Hom.one_def, Over.comp_left]
  rfl

end Dual

/-! ## §3. Tangent vectors of an abelian variety at the origin -/

section AbTan

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

instance isLocalHom_fstHom (V : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] : IsLocalHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K) where
  map_nonunit _ hx := isUnit_iff_isUnit_fst.mpr hx

/-- A `V`-valued tangent vector at the origin: a point `Spec (K ⊕ V) → A` over `K` reducing to the
origin. -/
def AtOrigin {V : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
    (a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X) : Prop :=
  specHom (fstHom K K V) ≫ a = 1

variable {V W : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
  [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem atOrigin_one : AtOrigin A (1 : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X) :=
  MonObj.comp_one _

theorem atOrigin_mul {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (hb : AtOrigin A b) : AtOrigin A (a * b) := by
  unfold AtOrigin at *
  rw [MonObj.comp_mul, ha, hb, _root_.mul_one]

theorem atOrigin_map (g : V →ₗ[K] W) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X}
    (ha : AtOrigin A a) : AtOrigin A (specHom (map g) ≫ a) := by
  unfold AtOrigin at *
  rw [← Category.assoc, specHom_comp, fstHom_comp_map, ha]

theorem closedPoint_eq :
    Spec.map (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K)) (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint (TrivSqZeroExt K V) := by
  haveI : IsLocalHom (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K)).hom := isLocalHom_fstHom V
  exact Spec_closedPoint (R := CommRingCat.of (TrivSqZeroExt K V)) (S := CommRingCat.of K)

/-- The closed point of a tangent vector at the origin is the origin. -/
theorem left_closedPoint {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    a.left (IsLocalRing.closedPoint (TrivSqZeroExt K V)) =
      orig A (IsLocalRing.closedPoint K) := by
  have h1 := congrArg (fun f => (f.left : Spec (CommRingCat.of K) ⟶ A.X.left)
    (IsLocalRing.closedPoint K)) ha
  simp only at h1
  rw [one_left, Over.comp_left] at h1
  erw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1
  rw [← closedPoint_eq]
  refine h1.trans ?_
  congr 1

end AbTan

/-! ## §4. The derivation of a tangent vector; additivity under the group law -/

section Deriv

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens} (hU : IsAffineOpen U)
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

variable {V W : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
  [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

theorem mem_of_atOrigin (ho : orig A (IsLocalRing.closedPoint K) ∈ U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    a.left (IsLocalRing.closedPoint (TrivSqZeroExt K V)) ∈ U := by
  rw [left_closedPoint A ha]
  exact ho

theorem comp_orig_mem (ho : orig A (IsLocalRing.closedPoint K) ∈ U) {Λ : CommRingCat.{0}} (p : Spec Λ ⟶ Spec (CommRingCat.of K)) (x : Spec Λ) :
    (p ≫ orig A) x ∈ U := by
  show orig A (p x) ∈ U
  rw [Subsingleton.elim (p x) (IsLocalRing.closedPoint K)]
  exact ho

/-- The evaluation `Γ(A, U) → K` at the origin. -/
def ev0 : Γ(A.X.left, U) ⟶ CommRingCat.of K := ptRing (orig A) ho

/-- The ring map `Γ(A, U) → K ⊕ V` of a tangent vector at the origin. -/
def tRing {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) :
    Γ(A.X.left, U) ⟶ CommRingCat.of (TrivSqZeroExt K V) :=
  ptRing (Λ := CommRingCat.of (TrivSqZeroExt K V)) a.left (mem_of_atOrigin A ho ha)

/-- The derivation `Γ(A, U) → V` of a tangent vector at the origin. -/
def D {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a) (x : Γ(A.X.left, U)) : V :=
  ((tRing A ho ha).hom x).snd

theorem tRing_specHom (hU : IsAffineOpen U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (g : V →ₗ[K] W) :
    tRing A ho (atOrigin_map A g ha) =
      tRing A ho ha ≫ CommRingCat.ofHom ((map g : TrivSqZeroExt K V →ₐ[K] _) :
        TrivSqZeroExt K V →+* TrivSqZeroExt K W) :=
  ptRing_specMap_comp hU _ _ _ _

theorem tRing_congr {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (e : a = b)
    (ha : AtOrigin A a) (hb : AtOrigin A b) : tRing A ho ha = tRing A ho hb := by
  subst e; rfl

theorem tRing_one (hU : IsAffineOpen U) :
    tRing A ho (atOrigin_one A (V := V)) =
      ev0 A ho ≫ CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K V)) := by
  unfold tRing ev0
  rw [← ptRing_specMap_comp hU _ _ ho (comp_orig_mem A ho _ _)]
  exact ptRing_congr (one_left A) _ _

theorem fst_tRing (hU : IsAffineOpen U) {a : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (x : Γ(A.X.left, U)) : ((tRing A ho ha).hom x).fst = (ev0 A ho).hom x := by
  have h1 : tRing A ho ha ≫ CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
      TrivSqZeroExt K V →+* K) = ev0 A ho ≫ CommRingCat.ofHom (algebraMap K K) := by
    unfold tRing ev0
    rw [← ptRing_specMap_comp hU _ _ (mem_of_atOrigin A ho ha) (by
        show a.left (Spec.map (CommRingCat.ofHom ((fstHom K K V : TrivSqZeroExt K V →ₐ[K] K) :
          TrivSqZeroExt K V →+* K)) (IsLocalRing.closedPoint K)) ∈ U
        rw [closedPoint_eq]
        exact mem_of_atOrigin A ho ha),
      ← ptRing_specMap_comp hU _ _ ho (comp_orig_mem A ho _ _)]
    refine ptRing_congr ?_ _ _
    have := congrArg (fun f => f.left) ha
    simp only [Over.comp_left, one_left] at this
    exact this
  have := congrArg (fun f => f.hom x) h1
  simpa using this

theorem D_one (hU : IsAffineOpen U) : D A ho (atOrigin_one A (V := V)) = 0 := by
  funext x
  unfold D
  rw [tRing_one A ho hU]
  simp [algebraMap_eq_inl]

/-- A tangent vector at the origin is determined by its derivation. -/
theorem eq_of_D_eq (hU : IsAffineOpen U) {a b : ptR (K := K) (TrivSqZeroExt K V) ⟶ A.X} (ha : AtOrigin A a)
    (hb : AtOrigin A b) (h : D A ho ha = D A ho hb) : a = b := by
  apply Over.OverMorphism.ext
  apply ptRing_ext hU (mem_of_atOrigin A ho ha) (mem_of_atOrigin A ho hb)
  ext x
  · exact (fst_tRing A ho hU ha x).trans (fst_tRing A ho hU hb x).symm
  · exact congrFun h x

end Deriv

/-! ## §5. Additivity: `D (v * w) = D v + D w` -/

section Mul

open TrivSqZeroExt

variable {K : Type} [Field K] (A : PkgI3.AbVar K) {U : A.X.left.Opens}
  (ho : orig A (IsLocalRing.closedPoint K) ∈ U)

theorem map_fst_inr :
    (map (LinearMap.fst K K K)).comp (map (LinearMap.inr K K K)) =
      (inlAlgHom K K K).comp (fstHom K K K) := by
  rw [← map_comp_map]
  apply algHom_ext
  intro x
  rw [map_inr, AlgHom.comp_apply, fstHom_apply, fst_inr]
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.snd_apply, inr_zero, map_zero]

theorem map_snd_inl :
    (map (LinearMap.snd K K K)).comp (map (LinearMap.inl K K K)) =
      (inlAlgHom K K K).comp (fstHom K K K) := by
  rw [← map_comp_map]
  apply algHom_ext
  intro x
  rw [map_inr, AlgHom.comp_apply, fstHom_apply, fst_inr]
  simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.inl_apply, LinearMap.snd_apply, inr_zero, map_zero]

theorem map_fst_inl :
    (map (LinearMap.fst K K K)).comp (map (LinearMap.inl K K K)) = AlgHom.id K _ := by
  rw [← map_comp_map, LinearMap.fst_comp_inl, map_id]

theorem map_snd_inr :
    (map (LinearMap.snd K K K)).comp (map (LinearMap.inr K K K)) = AlgHom.id K _ := by
  rw [← map_comp_map, LinearMap.snd_comp_inr, map_id]

theorem map_add_inl :
    (map (LinearMap.fst K K K + LinearMap.snd K K K)).comp (map (LinearMap.inl K K K)) =
      AlgHom.id K _ := by
  rw [← map_comp_map]
  convert map_id (R' := K) (M := K)
  ext
  simp

theorem map_add_inr :
    (map (LinearMap.fst K K K + LinearMap.snd K K K)).comp (map (LinearMap.inr K K K)) =
      AlgHom.id K _ := by
  rw [← map_comp_map]
  convert map_id (R' := K) (M := K)
  ext
  simp

theorem spec_inl_fst_comp {a : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X} (ha : AtOrigin A a) :
    specHom ((inlAlgHom K K K).comp (fstHom K K K)) ≫ a = 1 := by
  rw [← specHom_comp, Category.assoc]
  unfold AtOrigin at ha
  rw [ha, MonObj.comp_one]

/-- **Additivity of the derivation under the group law.** -/
theorem D_mul (hU : IsAffineOpen U) {v w : ptR (K := K) (TrivSqZeroExt K K) ⟶ A.X}
    (hv : AtOrigin A v) (hw : AtOrigin A w) :
    D A ho (atOrigin_mul A hv hw) = D A ho hv + D A ho hw := by
  set c := (specHom (map (LinearMap.inl K K K)) ≫ v) * (specHom (map (LinearMap.inr K K K)) ≫ w)
    with hcdef
  have hc : AtOrigin A c := atOrigin_mul A (atOrigin_map A _ hv) (atOrigin_map A _ hw)
  have e1 : specHom (map (LinearMap.fst K K K)) ≫ c = v := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_fst_inl, map_fst_inr, specHom_id, Category.id_comp, spec_inl_fst_comp A hw,
      _root_.mul_one]
  have e2 : specHom (map (LinearMap.snd K K K)) ≫ c = w := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_snd_inl, map_snd_inr, specHom_id, Category.id_comp, spec_inl_fst_comp A hv,
      _root_.one_mul]
  have e3 : specHom (map (LinearMap.fst K K K + LinearMap.snd K K K)) ≫ c = v * w := by
    rw [hcdef, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specHom_comp, specHom_comp,
      map_add_inl, map_add_inr, specHom_id, Category.id_comp, Category.id_comp]
  have h1 := (tRing_congr A ho e1 (atOrigin_map A _ hc) hv).symm.trans
    (tRing_specHom A ho hU hc _)
  have h2 := (tRing_congr A ho e2 (atOrigin_map A _ hc) hw).symm.trans
    (tRing_specHom A ho hU hc _)
  have h3 := (tRing_congr A ho e3 (atOrigin_map A _ hc) (atOrigin_mul A hv hw)).symm.trans
    (tRing_specHom A ho hU hc _)
  funext x
  simp only [D, Pi.add_apply, h1, h2, h3, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom, AlgHom.coe_toRingHom, snd_map, LinearMap.add_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]

end Mul

end ZInQ.Contrib.AbVarBC.Tangent
