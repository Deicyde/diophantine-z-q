import Mathlib

/-!
# bp-analytic: the analytic uniformization of an abelian variety, stated over genuine objects

`UniformizationLeaf A` is node AN3 of docs/research/bp-faltings.md (= N14 of bp-qmmoduli.md) in
"coordinate form": it needs **no analytification**. It quantifies over

* the group `A(ℂ)` of `ℂ`-points of the project's `AbVar` (copied from
  `ZInQKernel/HDecomp/Objects.lean`), a commutative group by Mathlib;
* regular functions `f ∈ Γ(U, 𝒪_A)` on Zariski opens `U`, evaluated at `ℂ`-points;
* the complex torus `ℂ^g ⧸ Λ` (built as a compact complex Lie group in `Torus.lean`; here only the
  quotient group is needed, so its two-line definition is repeated);
* analyticity of functions on open subsets of `ℂ^g` (Mathlib's `AnalyticOnNhd`, `HasFDerivAt`).

It says: there is a full lattice `Λ ⊂ ℂ^g` and a group isomorphism `φ : ℂ^g ⧸ Λ ≃ A(ℂ)` such that
(i) every regular function pulls back to a holomorphic function on an open set, and (ii) at every
point some `g` regular functions pull back to a local biholomorphism. (i)+(ii) say that `φ` is an
isomorphism of complex manifolds for the analytic structure of `A(ℂ)` (the unique one in which
regular functions are holomorphic and étale coordinates are charts), so the statement is a
consequence of Mumford, *Abelian varieties*, §1 (a compact connected complex Lie group is a torus)
applied to `A^an` (Serre, GAGA §2; SGA 1 XII §1); locators UNVERIFIED. It is not stronger than
the published statement.
-/

open CategoryTheory AlgebraicGeometry Limits MonObj

noncomputable section

namespace BPAnalytic.Uniformization

universe u

/-! ## Objects copied from `ZInQKernel/HDecomp/Objects.lean` (namespace `PkgI3`) -/

/-- (Objects.lean) An abelian variety over a field `K`: a group object in schemes over `Spec K`
whose structure morphism is proper, smooth and geometrically integral. -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- (Objects.lean) Commutativity is a Mathlib theorem. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

variable (L : Type u) [Field L] [Algebra K L]

/-- (Objects.lean) `Spec L` as a `K`-scheme. -/
def ptObj : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- (Objects.lean) The group `A(L)` of `L`-points: `K`-morphisms `Spec L → A`. -/
abbrev Pt (A : AbVar K) : Type u := ptObj (K := K) L ⟶ A.X

end AbVar

example (A : AbVar ℂ) : CommGroup (A.Pt ℂ) := inferInstance

/-! ## The complex torus (as a group; see `Torus.lean` for its Lie group structure) -/

/-- The complex torus `E ⧸ Λ` (same definition as `Torus.lean`). -/
abbrev Torus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Λ : Submodule ℤ E) :=
  E ⧸ Λ.toAddSubgroup

/-- The projection `E → E ⧸ Λ`. -/
abbrev proj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Λ : Submodule ℤ E) :
    E → Torus Λ := QuotientAddGroup.mk

/-! ## Regular functions evaluated at complex points -/

variable (A : AbVar ℂ)

/-- The `ℂ`-point `P` lies in the Zariski open `U`. -/
def PtIn (P : A.Pt ℂ) (U : A.X.left.Opens) : Prop := ⊤ ≤ P.left ⁻¹ᵁ U

open Classical in
/-- The value `f(P) ∈ ℂ` of a regular function `f ∈ Γ(U, 𝒪_A)` at a `ℂ`-point `P ∈ U`
(`0` if `P ∉ U`; only used on `U`). -/
def evalAt (U : A.X.left.Opens) (f : Γ(A.X.left, U)) (P : A.Pt ℂ) : ℂ :=
  if h : PtIn A P U then
    ((P.left.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom f
  else 0

/-- **LEAF (AN3, coordinate form).** Analytic uniformization of a complex abelian variety:
`A(ℂ) ≅ ℂ^g ⧸ Λ` as complex Lie groups, with `Λ` a full lattice. -/
def UniformizationLeaf : Prop :=
  ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
    (φ : Torus Λ ≃+ Additive (A.Pt ℂ)),
    -- (i) regular functions are holomorphic on open sets
    (∀ (U : A.X.left.Opens) (f : Γ(A.X.left, U)),
      IsOpen {v : Fin g → ℂ | PtIn A (Additive.toMul (φ (proj Λ v))) U} ∧
      AnalyticOnNhd ℂ (fun v => evalAt A U f (Additive.toMul (φ (proj Λ v))))
        {v | PtIn A (Additive.toMul (φ (proj Λ v))) U}) ∧
    -- (ii) at every point, `g` regular functions give local holomorphic coordinates
    (∀ v₀ : Fin g → ℂ, ∃ (U : A.X.left.Opens) (f : Fin g → Γ(A.X.left, U))
      (e : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)),
      PtIn A (Additive.toMul (φ (proj Λ v₀))) U ∧
      HasFDerivAt (fun v i => evalAt A U (f i) (Additive.toMul (φ (proj Λ v))))
        (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀)

/-- The leaf for every complex abelian variety. -/
def UniformizationLeafAll : Prop := ∀ A : AbVar ℂ, UniformizationLeaf A

end BPAnalytic.Uniformization
