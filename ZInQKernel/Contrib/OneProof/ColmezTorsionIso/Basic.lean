import ZInQKernel.Contrib.G9.Galois
import ZInQKernel.Contrib.AbVarBC.Main

/-!
# `A[N](F̄) ≅ A[N](ℂ_p)`, `G_F`-equivariantly

For a finite extension `F/ℚ_p` and an abelian variety `A` over `F` in the form of the tree
(`ZInQ.Contrib.G9.PkgI4.I3.AbVar F`, the object of the row `colmez1992DeRhamAbVar`), this file
proves that the natural map from the `F̄`-points of `A` to its `ℂ_p`-points is a bijection on
`N`-torsion for every `N ≠ 0`, a group isomorphism, and `G_F`-equivariant; hence the Tate module
built from the `F̄`-points (the row's `A.T p`, `G9/I4Layer.lean`) is isomorphic, as a
`ℤ_p[G_F]`-module, to the Tate module built from the `ℂ_p`-points (Colmez's `T_p(X)`, built from
`u_n ∈ X(C_p)`), and likewise for `V_p`.

## The model step, proposed for a ruling by Jack or the maintainer

* **Base field and variety.** Colmez's `K` is the row's `F` and his `X` is the row's `A` (an abelian
  variety over `F`, with no integral model). His identification `𝒳(O_{C_p}) = X(C_p)` for a proper
  model `𝒳` over `O_K` (p. 638, "Par construction") is a Lean theorem since #239
  (`ColmezProperModel.modelPtsEquiv`, `modelPtsEquiv_gal`). The model step reduces to the existence
  of such a model for every `A` (`ColmezProperModel.ProperModelExists`, `properModelPoints_iff`),
  which is in neither the tree nor Mathlib and is proposed for a ruling by Jack or the maintainer.
  The row's Lean form uses only `X(C_p)` and its Galois action, both read off `A`; as
  printed, 5.2(i) builds the limit from `F_ω(a_n)`, which goes through the model.
* **The embedding `F̄ → ℂ_p`.** The tree's `G_F → G_{ℚ_p}` (`gfToGqp`) is restriction along the
  isomorphism `embF : ℚ̄_p ≃ F̄` (`G9.embF_gfToGqp`, `G9.embF_bijective`). We use the same
  isomorphism: `ℂ_p` is an `F`-algebra through `F → ℚ̄_p ⊂ ℂ_p`, `y ↦ phiF y` (`algCp`; its image
  is the tree's `F' = fieldF p F`), and `F̄ → ℂ_p` is `x ↦ embF⁻¹ x` (`iotaFbar`), an `F`-algebra
  map.
* **The Galois action on `X(C_p)`.** `σ ∈ G_F` acts on `ℂ_p` by `cpAct (gfToGqp σ)`, the
  continuous extension of `σ` (`cpGal`), the action through which the row lets `G_F` act on
  `B_dR` (`bdrAct (gfToGqp σ)`); on points it acts on coordinates (`galAct`).

## Main results

* `exists_extPt_eq_of_pow`: over a field of characteristic `0`, an `N`-torsion `Ω₂`-point of a
  kernel abelian variety comes from `Ω` along any embedding `Ω → Ω₂` with `Ω` algebraically
  closed (from the tree's proved `AbVarBC.mulIsogeny`: `[N]` is finite).
* `torsCp`: `A[N](F̄) ≃+ A[N](ℂ_p)`, with `torsCp_apply` (it is the natural map) and
  `torsCp_galAct` (`G_F`-equivariance); `torsion_iso` packages the three properties.
* `tateCp : A.T p ≃ₗ[ℤ_p] TCp p A` and `vCp : A.V p ≃ₗ[ℚ_p] VCp p A`, with `tateCp_galT` and
  `vCp_galRep`: they intertwine the row's `A.galT`, `A.galRep p` with the actions `galTCp`,
  `galRepCp` on the Tate modules of the `ℂ_p`-points.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

noncomputable section

namespace ZInQ.Contrib.ColmezTorsionIso

/-! ## §1. Torsion points along an embedding of fields (characteristic `0`) -/

section Lift

variable {K : Type} [Field K] [CharZero K] (B : _root_.PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- **`N`-torsion points lift along `κ : Ω → Ω₂`**, `Ω` algebraically closed, `N ≠ 0`,
characteristic `0`: `[N]` is finite (`AbVarBC.mulIsogeny`), so the `Ω₂`-point lies on the finite
`K`-scheme `A[N]`, whose points over `Ω₂` come from `Ω` (`AbVarBC.exists_lift_of_isFinite`). -/
theorem exists_extPt_eq_of_pow (κ : Ω →ₐ[K] Ω₂) (N : ℕ) (hN : N ≠ 0) (q : B.Pt Ω₂)
    (hq : q ^ N = 1) : ∃ x : B.Pt Ω, AbVarBC.extPt B κ x = q := by
  have hfin : IsFinite ((((N : ℤ)) : _root_.PkgI3.AbVar.End B).hom.left) :=
    (AbVarBC.mulIsogeny K B (N : ℤ) (by exact_mod_cast hN)).1
  have h1 : q ≫ ((N : ℤ) : _root_.PkgI3.AbVar.End B).hom = 1 := by
    rw [AbVarBC.comp_natCast_hom, hq]
  let fN : B.X.left ⟶ B.X.left := ((N : ℤ) : _root_.PkgI3.AbVar.End B).hom.left
  let e : Spec (CommRingCat.of K) ⟶ B.X.left := η[B.X].left
  have hq0 : q.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂)) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  have hfN : IsFinite fN := hfin
  let z : Spec (CommRingCat.of Ω₂) ⟶ pullback fN e :=
    pullback.lift q.left (Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) hq0
  obtain ⟨p0, hp0, hp0g⟩ :=
    AbVarBC.exists_lift_of_isFinite κ (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ B.X.hom = pullback.snd fN e := by
    have hw : fN ≫ B.X.hom = B.X.hom := Over.w ((N : ℤ) : _root_.PkgI3.AbVar.End B).hom
    have he : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  let x : B.Pt Ω := Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ B.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl)
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ p0 ≫ pullback.fst fN e = q.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

end Lift

/-! ## §2. `ℂ_p` as an `F`-algebra, the embedding `F̄ → ℂ_p`, the action of `G_F` on `ℂ_p` -/

section Cp

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `ℂ_p` as an `F`-algebra: `F → ℚ̄_p ⊂ ℂ_p`, `y ↦ phiF y` (the tree's copy `F'` of `F`). -/
def algCp : Algebra F ℂ_[p] :=
  ((algebraMap (PadicAlgCl p) ℂ_[p]).comp (phiF p F).toRingHom).toAlgebra

attribute [local instance] algCp

theorem algebraMap_cp (y : F) :
    algebraMap F ℂ_[p] y = algebraMap (PadicAlgCl p) ℂ_[p] (phiF p F y) := rfl

/-- **The embedding `F̄ → ℂ_p`**: `F̄ ≃ ℚ̄_p ⊂ ℂ_p`, through the isomorphism `embF` behind
`gfToGqp`. -/
def iotaFbar : AlgebraicClosure F →ₐ[F] ℂ_[p] where
  toRingHom := (algebraMap (PadicAlgCl p) ℂ_[p]).comp (embFEquiv p F).symm.toRingHom
  commutes' _ := rfl

theorem iotaFbar_apply (x : AlgebraicClosure F) :
    iotaFbar p F x = algebraMap (PadicAlgCl p) ℂ_[p] ((embFEquiv p F).symm x) := rfl

theorem iotaFbar_injective : Function.Injective (iotaFbar p F) :=
  (iotaFbar p F : AlgebraicClosure F →+* ℂ_[p]).injective

theorem cpAct_one' (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe, AlgEquiv.one_apply]

theorem cpAct_mul' (σ τ : GQp p) (x : ℂ_[p]) :
    cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _)
      ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe, AlgEquiv.mul_apply]

/-- `G_F` fixes `F' = phiF(F)` pointwise (through `gfToGqp`). -/
theorem gfToGqp_phiF (σ : Field.absoluteGaloisGroup F) (y : F) :
    gfToGqp p F σ (phiF p F y) = phiF p F y := by
  apply (embF_bijective p F).injective
  rw [embF_gfToGqp, embF_phiF]
  exact (galF F σ).commutes y

/-- **`σ ∈ G_F` acting on `ℂ_p`**: `cpAct (gfToGqp σ)`, the continuous extension of `σ`, as an
`F`-algebra automorphism. -/
def cpGal (σ : Field.absoluteGaloisGroup F) : ℂ_[p] ≃ₐ[F] ℂ_[p] where
  toFun := cpAct p (gfToGqp p F σ)
  invFun := cpAct p (gfToGqp p F σ)⁻¹
  left_inv x := cpAct_inv_apply p _ x
  right_inv x := by simpa only [inv_inv] using cpAct_inv_apply p (gfToGqp p F σ)⁻¹ x
  map_mul' x y := map_mul _ x y
  map_add' x y := map_add _ x y
  commutes' y := by
    change cpAct p (gfToGqp p F σ) ((phiF p F y : PadicAlgCl p) : ℂ_[p]) =
      ((phiF p F y : PadicAlgCl p) : ℂ_[p])
    rw [cpAct_coe, gfToGqp_phiF]

theorem cpGal_apply (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p]) :
    cpGal p F σ x = cpAct p (gfToGqp p F σ) x := rfl

theorem cpGal_one : cpGal p F 1 = 1 := by
  ext x
  change cpAct p (gfToGqp p F 1) x = x
  rw [map_one, cpAct_one']

theorem cpGal_mul (σ τ : Field.absoluteGaloisGroup F) :
    cpGal p F (σ * τ) = cpGal p F σ * cpGal p F τ := by
  ext x
  change cpAct p (gfToGqp p F (σ * τ)) x = cpAct p (gfToGqp p F σ) (cpAct p (gfToGqp p F τ) x)
  rw [map_mul, cpAct_mul']

/-- **`F̄ → ℂ_p` is `G_F`-equivariant**: `ι(σ x) = σ(ι x)`. -/
theorem iotaFbar_galF (σ : Field.absoluteGaloisGroup F) (x : AlgebraicClosure F) :
    iotaFbar p F (galF F σ x) = cpGal p F σ (iotaFbar p F x) := by
  change (((embFEquiv p F).symm (galF F σ x) : PadicAlgCl p) : ℂ_[p]) =
    cpAct p (gfToGqp p F σ) (((embFEquiv p F).symm x : PadicAlgCl p) : ℂ_[p])
  rw [cpAct_coe]
  congr 1
  apply (embFEquiv p F).injective
  rw [RingEquiv.apply_symm_apply, embFEquiv_apply, embF_gfToGqp, ← embFEquiv_apply,
    RingEquiv.apply_symm_apply]

end Cp

/-! ## §3. Points: `A(F̄) → A(ℂ_p)` -/

section Points

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

attribute [local instance] algCp

/-- The row's abelian variety as a kernel `PkgI3.AbVar` (same fields). -/
def kerOf {K : Type} [Field K] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar K) : _root_.PkgI3.AbVar K :=
  @_root_.PkgI3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt

theorem charZero_F (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective

variable (p) in
/-- **The natural map `A(F̄) → A(ℂ_p)`**, `P ↦ P ∘ Spec(ι)`, `ι = iotaFbar`. -/
def extCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    A.Pt (AlgebraicClosure F) →* A.Pt ℂ_[p] :=
  AbVarBC.extPt (kerOf A) (iotaFbar p F)

theorem extCp_apply (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (x : A.Pt (AlgebraicClosure F)) :
    extCp p A x = AbVarBC.extHom (K := F) (iotaFbar p F) ≫ x := rfl

/-- **Injectivity** (any field extension). -/
theorem extCp_injective (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    Function.Injective (extCp p A) :=
  AbVarBC.extPt_injective (kerOf A) (iotaFbar p F)

/-- **Surjectivity on `N`-torsion**, `N ≠ 0`. -/
theorem extCp_surj_torsion (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ) (hN : N ≠ 0)
    (q : A.Pt ℂ_[p]) (hq : q ^ N = 1) : ∃ x, extCp p A x = q := by
  haveI := charZero_F p F
  exact exists_extPt_eq_of_pow (kerOf A) (iotaFbar p F) N hN q hq

/-- **`G_F`-equivariance** of `A(F̄) → A(ℂ_p)`. -/
theorem extCp_galAct (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F)
    (x : A.Pt (AlgebraicClosure F)) :
    extCp p A (A.galAct (galF F σ) x) = A.galAct (cpGal p F σ) (extCp p A x) :=
  AbVarBC.extPt_galAct (kerOf A) (iotaFbar p F) (galF F σ) (cpGal p F σ)
    (iotaFbar_galF p F σ) x

/-! ## §4. `A[N](F̄) ≃+ A[N](ℂ_p)` -/

/-- `M[N]`, the `N`-torsion subgroup of an abelian group. -/
def tors (M : Type*) [AddCommGroup M] (N : ℕ) : AddSubgroup M where
  carrier := {x | N • x = 0}
  add_mem' {a b} ha hb := by
    change N • (a + b) = 0
    rw [smul_add, show N • a = 0 from ha, show N • b = 0 from hb, add_zero]
  zero_mem' := smul_zero N
  neg_mem' {a} ha := by
    change N • -a = 0
    rw [smul_neg, show N • a = 0 from ha, neg_zero]

theorem mem_tors {M : Type*} [AddCommGroup M] {N : ℕ} {x : M} : x ∈ tors M N ↔ N • x = 0 :=
  Iff.rfl

variable (p) in
/-- The natural map on `N`-torsion, `A[N](F̄) → A[N](ℂ_p)`. -/
def torsMap (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ) :
    tors (Additive (A.Pt (AlgebraicClosure F))) N →+ tors (Additive (A.Pt ℂ_[p])) N :=
  ((MonoidHom.toAdditive (extCp p A)).comp (tors _ N).subtype).codRestrict (tors _ N)
    (fun x => by
      change N • (MonoidHom.toAdditive (extCp p A)) x.1 = 0
      rw [← map_nsmul, show N • x.1 = 0 from x.2, map_zero])

theorem torsMap_apply (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ)
    (x : tors (Additive (A.Pt (AlgebraicClosure F))) N) :
    (torsMap p A N x : Additive (A.Pt ℂ_[p])) =
      Additive.ofMul (extCp p A (Additive.toMul (x : Additive (A.Pt (AlgebraicClosure F))))) :=
  rfl

theorem torsMap_bijective (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ) (hN : N ≠ 0) :
    Function.Bijective (torsMap p A N) := by
  refine ⟨fun x y h => Subtype.ext
    (extCp_injective (p := p) A (congrArg (fun z => Additive.toMul z.1) h)), fun y => ?_⟩
  have hy : (Additive.toMul y.1) ^ N = 1 := congrArg Additive.toMul (show N • y.1 = 0 from y.2)
  obtain ⟨x, hx⟩ := extCp_surj_torsion (p := p) A N hN _ hy
  have hxN : N • Additive.ofMul x = 0 := by
    apply congrArg Additive.ofMul
    apply extCp_injective (p := p) A
    change extCp p A (x ^ N) = extCp p A 1
    rw [map_pow, hx, hy, map_one]
  exact ⟨⟨Additive.ofMul x, hxN⟩, Subtype.ext (congrArg Additive.ofMul hx)⟩

variable (p) in
/-- **`A[N](F̄) ≃+ A[N](ℂ_p)`** for `N ≠ 0`: the natural map (`torsCp_apply`), a group
isomorphism, `G_F`-equivariant (`torsCp_galAct`). -/
def torsCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ) (hN : N ≠ 0) :
    tors (Additive (A.Pt (AlgebraicClosure F))) N ≃+ tors (Additive (A.Pt ℂ_[p])) N :=
  AddEquiv.ofBijective (torsMap p A N) (torsMap_bijective A N hN)

theorem torsCp_apply (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ) (hN : N ≠ 0)
    (x : tors (Additive (A.Pt (AlgebraicClosure F))) N) :
    (torsCp p A N hN x : Additive (A.Pt ℂ_[p])) =
      Additive.ofMul (extCp p A (Additive.toMul (x : Additive (A.Pt (AlgebraicClosure F))))) :=
  rfl

theorem torsCp_galAct (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ) (hN : N ≠ 0)
    (σ : Field.absoluteGaloisGroup F) (x : tors (Additive (A.Pt (AlgebraicClosure F))) N)
    (hσx : Additive.ofMul (A.galAct (galF F σ) (Additive.toMul x.1)) ∈
      tors (Additive (A.Pt (AlgebraicClosure F))) N)
    (hσy : Additive.ofMul (A.galAct (cpGal p F σ) (Additive.toMul (torsCp p A N hN x).1)) ∈
      tors (Additive (A.Pt ℂ_[p])) N) :
    torsCp p A N hN ⟨_, hσx⟩ = ⟨_, hσy⟩ :=
  Subtype.ext (congrArg Additive.ofMul (extCp_galAct (p := p) A σ _))

/-- **The identification, in one statement.** For `N ≠ 0`, the natural map
`A[N](F̄) → A[N](ℂ_p)` is a bijection, it is additive, and it commutes with `G_F`. -/
theorem torsion_iso (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (N : ℕ) (hN : N ≠ 0) :
    Function.Bijective (torsMap p A N) ∧
      (∀ x y, torsMap p A N (x + y) = torsMap p A N x + torsMap p A N y) ∧
      ∀ (σ : Field.absoluteGaloisGroup F) (x : A.Pt (AlgebraicClosure F)),
        extCp p A (A.galAct (galF F σ) x) = A.galAct (cpGal p F σ) (extCp p A x) :=
  ⟨torsMap_bijective A N hN, fun x y => map_add _ x y, fun σ x => extCp_galAct (p := p) A σ x⟩

/-- `A[pⁿ](F̄) ≃+ A[pⁿ](ℂ_p)`. -/
theorem torsion_iso_pow (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (n : ℕ) :
    Function.Bijective (torsMap p A (p ^ n)) :=
  torsMap_bijective (p := p) A (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero)

end Points

/-! ## §5. Tate modules: `T_p` from `ℂ_p`-points, and the isomorphism with the row's `T_p` -/

section Tate

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

attribute [local instance] algCp

/-- If `φ` is injective and every `p`-power torsion element of `N` is in its image, `T_p(φ)` is
bijective (for the Tate modules of `G9/I4Layer.lean`). -/
theorem tate_map_bijective {M N : Type*} [AddCommGroup M] [AddCommGroup N] (φ : M →+ N)
    (hφ : Function.Injective φ) (htors : ∀ (n : ℕ) (q : N), (p ^ n) • q = 0 → ∃ x, φ x = q) :
    Function.Bijective (I3.Tate.map (ℓ := p) φ) := by
  refine ⟨fun x y h => Subtype.ext (funext fun n => hφ ?_), fun x => ?_⟩
  · have := congrArg (fun z => z.1 n) h
    simpa using this
  have hx : ∀ n, ∃ y, φ y = x.1 n := fun n =>
    htors n (x.1 n) (I3.Tate.pow_smul_eq_zero x.2 n)
  choose y hy using hx
  refine ⟨⟨y, ?_, fun n => ?_⟩, ?_⟩
  · apply hφ
    rw [hy, x.2.1, map_zero]
  · apply hφ
    rw [map_nsmul, hy, hy, x.2.2 n]
  · apply Subtype.ext
    funext n
    exact hy n

variable (p) in
/-- **Colmez's `T_p(X)`**: `lim A(ℂ_p)[pⁿ]`, a `ℤ_p`-module. -/
abbrev TCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : Type :=
  I3.Tate.T p (Additive (A.Pt ℂ_[p]))

variable (p) in
/-- `V_p = ℚ_p ⊗_{ℤ_p} T_p` of the `ℂ_p`-points. -/
abbrev VCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : Type :=
  TensorProduct ℤ_[p] ℚ_[p] (TCp p A)

variable (p) in
/-- `σ ∈ G_F` acting on `TCp`: through `cpGal σ` on coordinates. -/
def galTCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F) :
    TCp p A →ₗ[ℤ_[p]] TCp p A :=
  I3.Tate.map (MonoidHom.toAdditive (A.galAct (cpGal p F σ)))

variable (p) in
/-- **The Galois representation on `VCp`** (Colmez's `G_K`-action on `T_p(X)`, `X(C_p)`). -/
def galRepCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    Representation ℚ_[p] (Field.absoluteGaloisGroup F) (VCp p A) where
  toFun σ := (galTCp p A σ).baseChange ℚ_[p]
  map_one' := by
    have : galTCp p A 1 = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      change Additive.ofMul (I3.AbVar.galHom (cpGal p F 1) ≫ Additive.toMul (x.1 n)) = x.1 n
      rw [cpGal_one, I3.AbVar.galHom_one, Category.id_comp]; rfl
    change (galTCp p A 1).baseChange ℚ_[p] = LinearMap.id
    rw [this, LinearMap.baseChange_id]
  map_mul' σ τ := by
    have : galTCp p A (σ * τ) = galTCp p A σ ∘ₗ galTCp p A τ := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      change Additive.ofMul (I3.AbVar.galHom (cpGal p F (σ * τ)) ≫ Additive.toMul (x.1 n)) =
        Additive.ofMul (I3.AbVar.galHom (cpGal p F σ) ≫ I3.AbVar.galHom (cpGal p F τ) ≫
          Additive.toMul (x.1 n))
      rw [cpGal_mul, I3.AbVar.galHom_mul, Category.assoc]
    change (galTCp p A (σ * τ)).baseChange ℚ_[p] =
      (galTCp p A σ).baseChange ℚ_[p] ∘ₗ (galTCp p A τ).baseChange ℚ_[p]
    rw [this, LinearMap.baseChange_comp]

theorem galRepCp_apply (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F) :
    galRepCp p A σ = (galTCp p A σ).baseChange ℚ_[p] := rfl

variable (p) in
/-- `T_p(A)` (from `F̄`-points) `→ TCp` (from `ℂ_p`-points). -/
def tateMapCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : A.T p →ₗ[ℤ_[p]] TCp p A :=
  I3.Tate.map (MonoidHom.toAdditive (extCp p A))

theorem tateMapCp_bijective (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    Function.Bijective (tateMapCp p A) := by
  refine tate_map_bijective _ (extCp_injective (p := p) A) fun n q hq => ?_
  have hq' : (Additive.toMul q) ^ (p ^ n) = 1 := congrArg Additive.toMul hq
  obtain ⟨x, hx⟩ :=
    extCp_surj_torsion (p := p) A (p ^ n) (pow_ne_zero n (Fact.out : p.Prime).ne_zero) _ hq'
  exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩

variable (p) in
/-- **`T_p(A) ≃ₗ[ℤ_p] T_p` of the `ℂ_p`-points.** -/
def tateCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : A.T p ≃ₗ[ℤ_[p]] TCp p A :=
  LinearEquiv.ofBijective (tateMapCp p A) (tateMapCp_bijective A)

theorem tateCp_apply (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (x : A.T p) (n : ℕ) :
    (tateCp p A x).1 n = Additive.ofMul (extCp p A (Additive.toMul (x.1 n))) := rfl

/-- `tateCp` is `G_F`-equivariant. -/
theorem tateCp_galT (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F)
    (x : A.T p) : tateCp p A (A.galT σ x) = galTCp p A σ (tateCp p A x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (extCp_galAct (p := p) A σ (Additive.toMul (x.1 n)))

variable (p) in
/-- **`V_p(A) ≃ₗ[ℚ_p] V_p` of the `ℂ_p`-points.** -/
def vCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : A.V p ≃ₗ[ℚ_[p]] VCp p A :=
  (tateCp p A).baseChange ℤ_[p] ℚ_[p] _ _

/-- **`vCp` intertwines the row's `A.galRep p` with `galRepCp`.** -/
theorem vCp_galRep (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F)
    (v : A.V p) : vCp p A (A.galRep p σ v) = galRepCp p A σ (vCp p A v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a t =>
    change vCp p A ((A.galT σ).baseChange ℚ_[p] (a ⊗ₜ t)) =
      (galTCp p A σ).baseChange ℚ_[p] (vCp p A (a ⊗ₜ t))
    rw [LinearMap.baseChange_tmul]
    change (tateCp p A).baseChange ℤ_[p] ℚ_[p] _ _ (a ⊗ₜ A.galT σ t) =
      (galTCp p A σ).baseChange ℚ_[p] ((tateCp p A).baseChange ℤ_[p] ℚ_[p] _ _ (a ⊗ₜ t))
    rw [LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul,
      tateCp_galT]
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]

end Tate

end ZInQ.Contrib.ColmezTorsionIso
