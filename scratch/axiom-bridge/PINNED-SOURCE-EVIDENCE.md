# Pinned declarations and context for Fable F2

Presentation date: 2026-11-14 UTC. Full earlier evidence is preserved. This is
source availability, not new Lean code, an executable concatenation, proof replay
or review approval. Q-numbers bind exact source paths/commits/URLs/blobs/SHA/bytes
and byte slices in [SOURCE-EVIDENCE.json](SOURCE-EVIDENCE.json). A displayed final
newline may be added, as recorded. **Q… P** means only a theorem/lemma or Prop-valued-instance proof body
is omitted; its full telescope remains. Definition values and original
namespace/variable/instance context are quoted. Unneeded helper statements and
repeated prose/metadata are omitted; imports/source notices and repository
licenses stay unchanged. Collaborator acquisition was an ordinary permitted
pinned GitHub read; the original reviewer's failed fetch remains failed.

[F1/F2/F3 and their complete preserved report](https://github.com/elliotglazer/diophantine-z-q/pull/53#issuecomment-6873270408)
remain the original findings, not replaced by this source-availability packet.


## Variety parents

Q1
```lean
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
```
Q2
```lean
@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
```
Q3
```lean
/-- A scheme over a field is a variety when it is integral and its structure morphism is
separated and of finite type. -/
@[stacks 020D, stacks 03RE "the variety clause"]
class IsVariety (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop
    extends IsIntegral X, IsSeparated f, LocallyOfFiniteType f, QuasiCompact f

add_to_stacks 04L1 "affine_variety_2" AlgebraicGeometry.IsAffine
add_to_ega "I 1.7.1" AlgebraicGeometry.IsAffine

/-- A variety over a field is proper when its structure morphism to the spectrum of the field
is proper. -/
@[stacks 04L1 "proper_variety"]
class IsProperVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop
    extends IsVariety k f, IsProper f
```

## AlgebraicGeometry abelian variety and base change

Q4
```lean
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
```
Q5
```lean
@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 03RO.** A group scheme over a field is an abelian variety if its
structure morphism makes its underlying scheme a proper, geometrically integral variety. -/
@[stacks 03RO]
class IsAbelianVariety (k : Type u) [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] : Prop extends IsProperVariety k A.hom, GeometricallyIntegral A.hom
```
Q6
```lean
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The base change of a group scheme over `Spec k` along a field extension `K/k` is a group
scheme over `Spec K`. -/
noncomputable instance grpObjPullbackObj (A : Over (Spec (.of k))) [GrpObj A] :
    GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj (.mk A)).grp
```
Q7 P
```lean
@[stacks 0BFB]
instance isAbelianVariety_pullbackObj (A : Over (Spec (.of k))) [GrpObj A]
    [IsAbelianVariety k A] :
    IsAbelianVariety K
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A)
```

## Distinct Stacks predicate and natural dimension

Q8
```lean
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
import StacksCore.Tactic.EgaSgaAttribute
```
Q9
```lean
@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Groupoids
```
Q10
```lean
/-- A group scheme over a field is an abelian variety if its structure morphism makes its
underlying scheme a proper, geometrically integral variety. -/
@[stacks 03RO]
class IsAbelianVariety (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] : Prop
    extends IsProperVariety k A.hom, GeometricallyIntegral A.hom

/-- Being an abelian variety is being a proper variety and being geometrically integral. -/
theorem isAbelianVariety_iff (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    IsAbelianVariety k A ↔ IsProperVariety k A.hom ∧ GeometricallyIntegral A.hom :=
  ⟨fun h ↦ ⟨h.toIsProperVariety, h.toGeometricallyIntegral⟩, fun ⟨h₁, h₂⟩ ↦
    .mk (toIsProperVariety := h₁) (toGeometricallyIntegral := h₂)⟩

/-- The dimension of an abelian variety, as a natural number. -/
@[sga "7 IX 2.1.5" "α = dim B_o in (2.1.9)"]
noncomputable abbrev abelianVarietyDimension {k : Type u} [Field k]
    (A : Over (Spec (.of k))) : ℕ :=
  (topologicalKrullDim A.left).unbotD 0 |>.toNat
```
The distinct AV namespaces are not equated; natural dimension is unbotD 0 then toNat, justified by the local finite/nonempty witness below.

## Point commutativity instance

Q11
```lean
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Torsion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtaleCriterion
public import StacksFrontier.Topology.Dimension.DimensionLEOne
import StacksCore.Tactic.EgaSgaAttribute

```
Q12
```lean
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- An abelian variety is commutative (Tag 03RP, part (2)), as an instance. -/
instance isCommMonObj_of_isAbelianVariety [AlgebraicGeometry.IsAbelianVariety k A] :
    IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A
```

## Generic Tate construction and freeness hypotheses

Q13
```lean
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
```
Q14
```lean
@[expose] public noncomputable section

open PadicInt Pointwise

namespace Stacks.AbelianGroup

section Basic

variable (M : Type*) [AddCommGroup M] (ℓ : ℕ)

/-- The subgroup of `ℕ → M` of the sequences `x` with `x 0 = 0` and `ℓ • x (n + 1) = x n`. -/
def tateSubgroup : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    exact ⟨by simp [hx0, hy0], fun n => by simp [smul_add, hx, hy]⟩
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    exact ⟨by simp [hx0], fun n => by simp [hx]⟩
```
Q15
```lean
/-- The `ℓ`-adic Tate module `T_ℓ M = lim_n M[ℓ^n]` of an abelian group `M`: the sequences
`x : ℕ → M` with `x 0 = 0` and `ℓ • x (n + 1) = x n`. -/
@[sga "1 XI 2.1", sga "7 I 6.1" "partial"]
abbrev tateModule : Type _ :=
  tateSubgroup M ℓ

variable {M ℓ}
```
Q16
```lean
end Basic

section Module

variable {M : Type*} [AddCommGroup M] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- A power of a prime `ℓ` is nonzero. -/
instance (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero n hℓ.out.ne_zero⟩

```
Q17
```lean

/-- The action of `ℤ_[ℓ]` on `T_ℓ M`, `(a • x) n = (a mod ℓ^n) • x n`. -/
instance : SMul ℤ_[ℓ] (tateModule M ℓ) where
  smul a x := ⟨fun n => (toZModPow n a).val • (x : ℕ → M) n, mem_tateSubgroup.2
    ⟨by simp [seq_zero x], fun n => by
      rw [smul_comm, smul_seq_succ]
      exact nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x n)
        (by rw [natCast_val_toZModPow_of_le (Nat.le_succ n), ZMod.natCast_zmod_val])⟩⟩

/-- The `n`-th component of `a • x` is `(a mod ℓ^n) • x n`. -/
theorem smul_seq (a : ℤ_[ℓ]) (x : tateModule M ℓ) (n : ℕ) :
    ((a • x : tateModule M ℓ) : ℕ → M) n = (toZModPow n a).val • (x : ℕ → M) n :=
  rfl

/-- The Tate module `T_ℓ M` is a module over the `ℓ`-adic integers. -/
instance : Module ℤ_[ℓ] (tateModule M ℓ) where
  one_smul x := by
    ext n
    rw [smul_seq]
    exact (nsmul_eq_nsmul_of_natCast_eq (b := 1) (pow_smul_seq x n)
      (by rw [ZMod.natCast_zmod_val, map_one, Nat.cast_one])).trans (one_nsmul _)
  mul_smul a b x := by
    ext n
    rw [smul_seq, smul_seq, smul_seq, smul_smul]
    exact nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x n)
      (by rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        map_mul])
  smul_zero a := by
    ext n
    simp [smul_seq]
  smul_add a x y := by
    ext n
    simp [smul_seq]
  add_smul a b x := by
    ext n
    simp only [smul_seq, AddSubgroup.coe_add, Pi.add_apply, ← add_nsmul]
    exact nsmul_eq_nsmul_of_natCast_eq (pow_smul_seq x n)
      (by rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        map_add])
  zero_smul x := by
    ext n
    simp [smul_seq]

end Module
```
Q18
```lean
section Map

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] (ℓ : ℕ)
  [Fact ℓ.Prime]

/-- The `ℤ_[ℓ]`-linear map `T_ℓ M → T_ℓ N` induced by an additive map `f : M →+ N`. -/
@[sga "7 IX 1.0" "partial"]
def tateModuleMap (f : M →+ N) : tateModule M ℓ →ₗ[ℤ_[ℓ]] tateModule N ℓ where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), mem_tateSubgroup.2
    ⟨by simp [seq_zero x], fun n => by rw [← map_nsmul, smul_seq_succ]⟩⟩
  map_add' x y := by
    ext n
    simp
  map_smul' a x := by
    ext n
    simp [smul_seq]
```
Q19
```lean
end Reduction

section Free

variable {M : Type*} [AddCommGroup M] {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

```
Q20
```lean
variable {r : ℕ}

```
Q21 P
```lean
theorem module_free_tateModule (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.Free ℤ_[ℓ] (tateModule M ℓ)
```
Q22 P
```lean
theorem module_finite_tateModule (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.Finite ℤ_[ℓ] (tateModule M ℓ)
```
Q23 P
```lean
theorem finrank_tateModule (hdiv : ∀ x : M, ∃ y, ℓ • y = x)
    (htors : ∀ n, Nonempty (AddSubgroup.torsionBy M ((ℓ ^ n : ℕ) : ℤ) ≃+ (Fin r → ZMod (ℓ ^ n)))) :
    Module.finrank ℤ_[ℓ] (tateModule M ℓ) = r
```
Original sections are separate (Map ends 271, Reduction 447). Full M/ell/r and divisibility/torsion/prime hypotheses remain.

## Actual geometric Tate map/free/finite/rank

Q24
```lean
module

public import StacksFrontier.Algebra.Group.TateModule
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.IsogenyKernelCount
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
import StacksCore.Tactic.EgaSgaAttribute

```
Q25
```lean
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory PadicInt Pointwise
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k]

section Hom

variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj B]
```
Q26
```lean
end Hom

section Tate

variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The `ℓ`-adic Tate module `T_ℓ A = lim_n A(k)[ℓ^n]` of a commutative group scheme `A` over
`k`: the Tate module of its group of rational points `A(k)`, written additively. -/
@[sga "1 XI 2.1", sga "7 I 6.1" "partial"]
abbrev tateModule : Type u :=
  AbelianGroup.tateModule (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ℓ

variable {A ℓ}

variable {B C : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]

variable (ℓ) in
/-- The `ℤ_ℓ`-linear map `T_ℓ α : T_ℓ A → T_ℓ B` induced by a homomorphism `α : A ⟶ B` of
commutative group schemes over `k`: postcomposition with `α` on rational points. -/
def tateModuleMap (α : A ⟶ B) [IsMonHom α] : tateModule A ℓ →ₗ[ℤ_[ℓ]] tateModule B ℓ :=
  AbelianGroup.tateModuleMap ℓ (IsMonHom.monoidHom α (𝟙_ (Over (Spec (.of k))))).toAdditive

```
Q27
```lean
end Tate

section AbelianVariety

variable [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

```
Q28
```lean

omit hℓ in
/-- `A(k)[ℓ^n] ≅ (ℤ/ℓ^n)^(2g)` for `ℓ` invertible in `k` (Tag 03RP, part (7)). -/
```
Q29 P
```lean
theorem nonempty_torsionBy_pow_addEquiv (hℓk : IsUnit (ℓ : k)) (n : ℕ) :
    Nonempty (AddSubgroup.torsionBy (Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) ((ℓ ^ n : ℕ) : ℤ) ≃+
      (Fin (2 * abelianVarietyDimension A) → ZMod (ℓ ^ n)))
```
Q30 P
```lean
theorem module_free_tateModule (hℓk : IsUnit (ℓ : k)) : Module.Free ℤ_[ℓ] (tateModule A ℓ)
```
Q31 P
```lean
theorem module_finite_tateModule (hℓk : IsUnit (ℓ : k)) : Module.Finite ℤ_[ℓ] (tateModule A ℓ)
```
Q32 P
```lean
theorem finrank_tateModule (hℓk : IsUnit (ℓ : k)) :
    Module.finrank ℤ_[ℓ] (tateModule A ℓ) = 2 * abelianVarietyDimension A
```
The original omit hℓ preceding torsion equivalence is retained; free/finite/rank keep their prime/unit and algebraic-closure guards.

## Smooth projective curve

Q33
```lean
module
public import Mathlib
public import Mordell.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
```
Q34
```lean
open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- A scheme `C` with structure morphism `f : C ⟶ Spec k` over a field `k` is a
*(smooth projective) curve* when `f` is smooth of relative dimension one, `C` is a projective
variety over `k`, and `f` is geometrically integral. -/
@[faltings "def_nt_curve"]
public class IsSmoothProjectiveCurve (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) : Prop
    extends IsProjectiveVariety k f, GeometricallyIntegral f, SmoothOfRelativeDimension 1 f

end Faltings
```

## Degree-one divisor

Q35
```lean
module
public import Mordell.Curve.Basic
```
Q36
```lean
open CategoryTheory AlgebraicGeometry

universe u

namespace Faltings

/-- A *curve with a rational divisor of degree one* over a field `k`: a smooth projective
geometrically integral curve `C` over `k`, with structure morphism `f`, together with a divisor
`P`, a finite `ℤ`-combination of closed points of `C`, of degree
`∑ P x • [κ(x) : k] = 1`. -/
@[faltings "def_nt_curve_setup"]
public structure CurveWithDegreeOneDivisor (k : Type u) [Field k] where
  /-- The underlying scheme of the curve. -/
  C : Scheme.{u}
  /-- The structure morphism of the curve. -/
  f : C ⟶ Spec (.of k)
  /-- `C` is a smooth projective geometrically integral curve over `k`. -/
  [isSmoothProjectiveCurve : IsSmoothProjectiveCurve k f]
  /-- The divisor `P`, a finite `ℤ`-combination of closed points of `C`. -/
  P : {x : C // IsClosed ({x} : Set C)} →₀ ℤ
  /-- The divisor `P` has degree one: `∑ P x • [κ(x) : k] = 1`. -/
  degree_P : (P.sum fun x n => n * (f.residueDegree x.1 : ℤ)) = 1

attribute [instance] CurveWithDegreeOneDivisor.isSmoothProjectiveCurve

end Faltings
```

## Immediate relative degree-zero Picard functor

Q37
```lean
module
public import Mordell.Curve.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBridges
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBaseChangeDegree
```
Q38
```lean
open CategoryTheory AlgebraicGeometry Opposite Stacks.Picard Stacks.RigidifiedPicard

universe u

namespace Faltings

/-- **The relative Picard functor of degree zero `P⁰_C`** of a smooth projective curve
`f : C ⟶ Spec k`. Its value at a `k`-scheme `T` is the group of classes of invertible sheaves on
`C ×_k T` of degree zero on every fibre of the projection `q : C ×_k T ⟶ T`, modulo
`q^* Pic(T)`; a `k`-morphism `T' ⟶ T` acts by pull-back along `C ×_k T' ⟶ C ×_k T`. -/
@[expose, faltings "def_nt_relative_pic0_functor"]
public noncomputable def relativePicZeroFunctor (k : Type u) [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsSmoothProjectiveCurve k f] :
    (Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  have hdim : ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1 := fun s =>
    (topologicalKrullDim_fiber_spec f s).trans_le
      (topologicalKrullDim_le_one_of_smoothOfRelativeDimension f)
  let Z (T : Over (Spec (.of k))) := (degree f hdim T).ker
  let N (T : Over (Spec (.of k))) : AddSubgroup (Z T) :=
    (smallSchemePullbackClassHom (bcProj f T)).range.addSubgroupOf (Z T)
  let φ {T U : Over (Spec (.of k))} (g : T ⟶ U) : Z U →+ Z T :=
    ((smallSchemePullbackClassHom (bcMap f g)).comp (Z U).subtype).codRestrict _
      fun x => by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
          degree_smallSchemePullbackClassHom_bcMap, (AddMonoidHom.mem_ker.1 x.2)]
        rfl
  have hφ {T U : Over (Spec (.of k))} (g : T ⟶ U) : N U ≤ (N T).comap (φ g) := by
    rintro x ⟨y, hy⟩
    refine ⟨smallSchemePullbackClassHom g.left y, ?_⟩
    show _ = smallSchemePullbackClassHom (bcMap f g) (x : _)
    rw [show (x : smallOfScheme (bc f U)) = _ from hy.symm, smallSchemePullbackClassHom_comp,
      smallSchemePullbackClassHom_comp, bcMap_snd]
  { obj T := AddCommGrpCat.of (Z T.unop ⧸ N T.unop)
    map g := AddCommGrpCat.ofHom (QuotientAddGroup.map _ _ (φ g.unop) (hφ g.unop))
    map_id T := by
      ext x
      exact congrArg (QuotientAddGroup.mk' (N T.unop)) <| Subtype.ext <|
        show smallSchemePullbackClassHom (bcMap f (𝟙 T.unop)) (x : _) = x by
          rw [bcMap_id, smallSchemePullbackClassHom_id]
    map_comp g h := by
      ext x
      exact congrArg (QuotientAddGroup.mk' _) <| Subtype.ext <|
        show smallSchemePullbackClassHom (bcMap f (h.unop ≫ g.unop)) (x : _) =
          smallSchemePullbackClassHom (bcMap f h.unop)
            (smallSchemePullbackClassHom (bcMap f g.unop) (x : _)) by
          rw [bcMap_comp, smallSchemePullbackClassHom_comp] }

end Faltings
```

## Actual Jacobian structure

Q39
```lean
module
public import Mordell.Jacobian.PicZeroFunctor
```
Q40
```lean
open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Faltings

attribute [local instance] Hom.group

/-- A **Jacobian** of a smooth projective curve `f : C ⟶ Spec k` is a pair `(J, ι)` of an
abelian variety `J` over `k` and a morphism of group-valued functors `ι : P⁰_C ⟶ J(-)` from
the relative Picard functor of degree zero to the functor of points of `J`, such that
`ι(T) : P⁰_C(T) → J(T)` is bijective for every `k`-scheme `T` with `C(T) ≠ ∅`. -/
@[faltings "def_nt_jacobian"]
public structure Jacobian (k : Type u) [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsSmoothProjectiveCurve k f] where
  /-- The abelian variety `J` over `k`. -/
  J : Over (Spec (.of k))
  /-- The group law of `J`. -/
  [grpObj : GrpObj J]
  /-- `J` is an abelian variety over `k`. -/
  isAbelianVariety : IsAbelianVariety k J
  /-- The underlying morphism of set-valued functors of `ι : P⁰_C ⟶ J(-)`. -/
  ι : relativePicZeroFunctor k f ⋙ forget AddCommGrpCat ⟶ yoneda.obj J
  /-- `ι(T)` is a group homomorphism: it sends sums in `P⁰_C(T)` to products in `J(T)`. -/
  map_add : ∀ (T : (Over (Spec (.of k)))ᵒᵖ) (x y : (relativePicZeroFunctor k f).obj T),
    ι.app T (x + y) =
      @HMul.hMul (T.unop ⟶ J) (T.unop ⟶ J) (T.unop ⟶ J) _ (ι.app T x) (ι.app T y)
  /-- `ι(T)` is bijective whenever `C(T) ≠ ∅`. -/
  isIso_app : ∀ T : Over (Spec (.of k)), Nonempty (T ⟶ Over.mk f) → IsIso (ι.app (op T))

attribute [instance] Jacobian.grpObj

end Faltings
```

## Genus and scalar-valued structure-sheaf cohomology

Q41
```lean
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Tactic.StacksAttribute
```
Q42
```lean
@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The `i`-th cohomology of the structure sheaf of `X`, with scalars retained over the ring
defining the chosen affine base. -/
noncomputable abbrev structureSheafCohomology {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (i : ℕ) : ModuleCat.{u} R :=
  letI : (moduleSpecΓFunctor (R := .of R)).Additive := ⟨by intro M N φ ψ; ext x; rfl⟩
  ((((Scheme.Modules.pushforward f) ⋙ moduleSpecΓFunctor).rightDerived i).obj
    (SheafOfModules.unit X.ringCatSheaf))

/-- The genus of a scheme `X` over a field `k`, namely `dim_k H¹(X, 𝒪_X)`. -/
@[stacks 0BY7, stacks 0B9W "smooth projective geometrically irreducible curve over a field"]
noncomputable def genus {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : ℕ := Module.finrank k (structureSheafCohomology f 1)
```

## Existence and unique compatible scheme isomorphism

Q43
```lean
module
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.Jacobian.Basic
public import Mordell.Jacobian.PicZeroRigidified
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Proper
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
```
Q44
```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Faltings
```
Q45
```lean
end Existence
```
Q46 P
```lean
public theorem Jacobian.nonempty_and_existsUnique_iso (k : Type u) [Field k]
    (X : CurveWithDegreeOneDivisor k) :
    Nonempty (Jacobian k X.f) ∧
      ∀ A B : Jacobian k X.f, ∃! e : A.J ≅ B.J, A.ι ≫ yoneda.map e.hom = B.ι
```
The final theorem is outside Uniqueness (end 225) and Existence (end 2054); uniqueness is a compatible scheme isomorphism, not a new Grp-isomorphism theorem.

## Exact topological-dimension theorem

Q47
```lean
module
public import Mordell.Curve.DegreeOneDivisor
public import Mordell.Jacobian.PicZeroRigidified
public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.ProjHeightOne
public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelSurjective
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
```
Q48
```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
  CartesianMonoidalCategory

universe u

namespace Faltings
```
Q49
```lean
end Psi

section Dimension

variable {k : Type u} [Field k]

open Stacks.RigidifiedPicard relativePicZeroFunctor in
```
Q50 P
```lean
public theorem Jacobian.topologicalKrullDim_eq_genus (X : CurveWithDegreeOneDivisor k)
    (A : Jacobian k X.f) : topologicalKrullDim A.J.left = (genus X.f : WithBot ℕ∞)
```

## Actual good-reduction model

Q51
```lean
module

public import Mathlib
public import Mordell.Attr
public import Mordell.AbelianVariety.AbelianScheme.BaseChange
public import Mordell.AbelianVariety.SpreadingOut

```
Q52
```lean
@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain

namespace Faltings

/-- An abelian variety `A` over a number field `k` has *good reduction* at the finite place `𝔭`
if there are an abelian scheme `𝒜` over the localization `𝓞_{k,(𝔭)}` (a group scheme that is
flat, proper and locally of finite presentation, with all fibres `𝒜 ×_W Spec κ(w)` proper and
geometrically integral) and an isomorphism of group schemes over `k` between the generic fibre
`𝒜 ×_{𝓞_{k,(𝔭)}} Spec k` and `A`. -/
@[faltings "def_mw_good_reduction"]
def HasGoodReduction (k : Type u) [Field k] [NumberField k] (𝔭 : HeightOneSpectrum (𝓞 k))
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] : Prop :=
  ∃ 𝒜 : Grp (Over (Spec (CommRingCat.of
      (Localization.subalgebra k 𝔭.asIdeal.primeCompl
        𝔭.asIdeal.primeCompl_le_nonZeroDivisors)))),
    Flat 𝒜.X.hom ∧ IsProper 𝒜.X.hom ∧ LocallyOfFinitePresentation 𝒜.X.hom ∧
    (∀ w, IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom ∧
      GeometricallyIntegral ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj 𝒜.X).hom) ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap
        (Localization.subalgebra k 𝔭.asIdeal.primeCompl
          𝔭.asIdeal.primeCompl_le_nonZeroDivisors) k)))).mapGrp.obj 𝒜 ≅ Grp.mk A)

end Faltings
```

## Multiplicative base-change adjunction

Q53
```lean
module

public import Mathlib
public import Mordell.Attr
```
Q54
```lean
@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj

namespace Faltings
```
Q55
```lean
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped MonObj

namespace Faltings
```
Q56
```lean
/-- Base change along `f` identifies `T`-points of a group object `G` over `Y` with `T`-points
of its base change, as groups: the hom-equivalence of `Over.mapPullbackAdj f` is multiplicative. -/
noncomputable def mapPullbackAdjMulEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Grp (Over Y))
    (T : Over X) :
    ((Over.map f).obj T ⟶ G.X) ≃* (T ⟶ ((Over.pullback f).mapGrp.obj G).X) where
  __ := (Over.mapPullbackAdj f).homEquiv _ _
  map_mul' g h := by
    simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, Functor.map_mul]
    exact MonObj.comp_mul (M := ((Over.pullback f).mapGrp.obj G).X) _ _ _

```
Q57 P
```lean
@[simp]
lemma mapPullbackAdjMulEquiv_symm_left {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Grp (Over Y))
    (T : Over X) (P : T ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    ((mapPullbackAdjMulEquiv f G T).symm P).left = P.left ≫ pullback.fst G.X.hom f
```

## Frobenius characteristic, absolute, geometric and arithmetic operators

Q58
```lean
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Perfect
public import StacksCore.Tactic.StacksAttribute
```
Q59
```lean
@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace Stacks.Frobenius

/-- A scheme is **in characteristic `p`** when `p` vanishes in its ring of global sections. -/
abbrev IsInCharacteristic (X : Scheme.{u}) (p : ℕ) : Prop :=
  (p : Γ(X, ⊤)) = 0
```
Q60
```lean
/-- In a commutative ring in which a prime `p` vanishes, taking `p`-th powers is a ring
endomorphism. The zero ring, where `p` need not be the characteristic, is covered as well: the
`p`-th power map is the identity there. -/
@[ega "0 21.1.4"]
noncomputable def primePowerEndomorphism (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) : R →+* R := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    letI : CharP R p := by
      rw [← ringChar.eq_iff]
      exact ((Nat.dvd_prime Fact.out).mp (ringChar.dvd hp)).resolve_left
        CharP.ringChar_ne_one
    exact frobenius R p
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact RingHom.id R
```
Q61
```lean
/-- **Stacks Project, Tag 03SM.** The absolute Frobenius of a scheme in characteristic `p`: it
is the identity on points and the `p`-th power map on the structure sheaf. -/
@[stacks 03SM,
  implicit_reducible,
  sga "3 VIIA 4.1" "absolute Frobenius fr(X)",
  sga "5 XV 1.Definition2",
  sga "4½ Fonctions_L 3.4" "F_abs definition",
  sga "4½ Rapport 1.1" "q = p",
  sga "3 VIIB 4.1.1",
  sga "7 IX 4.3.2" "special case",
  sga "7 XXI 1.0",
  sga "7 XXII 6.2" "(6.2.1) F_q for q = p"]
noncomputable def absoluteFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) : X ⟶ X := by
  let α : X.presheaf ⟶ X.presheaf :=
    { app := fun U ↦ CommRingCat.ofHom <|
        primePowerEndomorphism _ p (cast_eq_zero_of_isInCharacteristic hX U.unop)
      naturality := by
        intro U V f
        ext g
        change primePowerEndomorphism _ p
            (cast_eq_zero_of_isInCharacteristic hX V.unop) ((X.presheaf.map f) g) =
          X.presheaf.map f (primePowerEndomorphism _ p
            (cast_eq_zero_of_isInCharacteristic hX U.unop) g)
        rw [primePowerEndomorphism_apply, primePowerEndomorphism_apply, map_pow] }
  let f : X.toPresheafedSpace ⟶ X.toPresheafedSpace := { base := 𝟙 _, c := α }
  refine Scheme.Hom.mk <| LocallyRingedSpace.homMk (InducedCategory.homMk f) ?_
  rw [InducedCategory.homMk_hom]
  dsimp only [f]
  intro x
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨U, hxU, g, rfl⟩ := X.presheaf.exists_germ_eq a
  change IsUnit (X.presheaf.germ U x hxU g)
  apply (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  change IsUnit (X.presheaf.germ U x hxU
    (primePowerEndomorphism _ p (cast_eq_zero_of_isInCharacteristic hX U) g)) at ha
  simpa only [primePowerEndomorphism_apply, map_pow] using ha
```
Q62 P
```lean
lemma absoluteFrobenius_base (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) :
    (absoluteFrobenius X p hX).base = 𝟙 (X : TopCat)
```
Q63 P
```lean
lemma absoluteFrobenius_app_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : X.Opens) (g : Γ(X, U)) :
    (absoluteFrobenius X p hX).app U g = g ^ p
```
Q64
```lean
noncomputable def geometricFrobenius {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) : X ⟶ X :=
  Over.homMk
    (End.asHom (End.of
      (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f))
    (absoluteFrobenius_pow_comp_hom X p f hcard)
```
Q65 P
```lean
lemma geometricFrobenius_left {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) :
    (geometricFrobenius X p f hcard).left =
      End.asHom (End.of
        (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f)
```
Q66
```lean
section ArithmeticFrobenius

variable (k : Type u) [Field k] [Fintype k] (K : Type v) [Field K] [Algebra k K] (p f : ℕ)
  [ExpChar K p] [PerfectRing K p]

/-- **Stacks Project, Tag 03SU.** The arithmetic Frobenius `x ↦ x ^ q` of a finite field `k`
with `q = p ^ f` elements, acting on a perfect extension field `K` of exponential
characteristic `p`. It is the `f`-fold Frobenius automorphism of `K`, and it fixes `k`
pointwise because every element of a field with `q` elements satisfies `x ^ q = x`. -/
@[stacks 03SU, sga "7 XXI 5.0"]
noncomputable def arithmeticFrobenius (hcard : Fintype.card k = p ^ f) : K ≃ₐ[k] K :=
  AlgEquiv.ofRingEquiv (f := iterateFrobeniusEquiv K p f) fun x ↦ by
    rw [iterateFrobeniusEquiv_def, ← hcard, ← map_pow, FiniteField.pow_card]
```
Q67 P
```lean
lemma arithmeticFrobenius_apply (hcard : Fintype.card k = p ^ f) (x : K) :
    arithmeticFrobenius k K p f hcard x = x ^ Fintype.card k
```
Q68
```lean
end ArithmeticFrobenius
```
Geometric/cardinality and arithmetic/ExpChar/PerfectRing telescopes are distinct; q-power is not replaced by an inverse or arbitrary-base p-linearity.

## Absolute iterate

Q69
```lean
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Endomorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
import StacksCore.Tactic.EgaSgaAttribute
```
Q70
```lean
@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

namespace AlgebraicGeometry

/-- The `n`-fold composite of the absolute Frobenius endomorphism. -/
public noncomputable abbrev absoluteFrobeniusPow (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (n : ℕ) : S ⟶ S :=
  End.asHom ((End.of (absoluteFrobenius S p hS)) ^ n)
```

## Relative twist, morphism and direction

Q71
```lean
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
import StacksCore.Tactic.EgaSgaAttribute
```
Q72
```lean
@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

namespace AlgebraicGeometry
```
Q73
```lean
public noncomputable def frobeniusTwist (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) : Over S ⥤ Over S :=
  Over.pullback (absoluteFrobenius S p hS)
```
Q74
```lean
public noncomputable def relativeFrobenius (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) : X ⟶ (frobeniusTwist S p hS).obj X :=
  Classical.choose (relativeFrobenius_existsUnique S p hS X)
```
Q75 P
```lean
public theorem relativeFrobenius_fst (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    (relativeFrobenius S p hS X).left ≫ pullback.fst X.hom (absoluteFrobenius S p hS) =
      absoluteFrobenius X.left p (isInCharacteristic_of_hom X.hom p hS)
```
Q76 P
```lean
public theorem relativeFrobenius_snd (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    (relativeFrobenius S p hS X).left ≫ pullback.snd X.hom (absoluteFrobenius S p hS) =
      X.hom
```
Q77 P
```lean
public lemma relativeFrobenius_naturality (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) {X Y : Over S} (f : X ⟶ Y) :
    relativeFrobenius S p hS X ≫ (frobeniusTwist S p hS).map f =
      f ≫ relativeFrobenius S p hS Y
```

## Iterated equations and actual factorization section

Q78
```lean
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated
```
Q79
```lean
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Frobenius

universe u
```
Q80
```lean
end Stacks.FieldTheory

namespace AlgebraicGeometry
```
Q81
```lean
def frobeniusBaseChangeSection {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (s : S ⟶ T)
    (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ)
    (hsg : s ≫ g = absoluteFrobeniusPow S p hS m) :
    X ⟶ pullback f g :=
  pullback.lift (absoluteFrobeniusPow X p (isInCharacteristic_of_hom f p hS) m) (f ≫ s) (by
    rw [absoluteFrobeniusPow_naturality f p (isInCharacteristic_of_hom f p hS) hS, ← hsg,
      Category.assoc])
```
Q82 P
```lean
@[simp]
theorem frobeniusBaseChangeSection_comp_fst {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (s : S ⟶ T) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ)
    (hsg : s ≫ g = absoluteFrobeniusPow S p hS m) :
    frobeniusBaseChangeSection f g s p hS m hsg ≫ pullback.fst f g =
      absoluteFrobeniusPow X p (isInCharacteristic_of_hom f p hS) m
```
Q83 P
```lean
theorem fst_comp_frobeniusBaseChangeSection {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (s : S ⟶ T) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (m : ℕ)
    (hsg : s ≫ g = absoluteFrobeniusPow S p hS m)
    (hgs : g ≫ s = absoluteFrobeniusPow T p (isInCharacteristic_of_hom g p hS) m) :
    pullback.fst f g ≫ frobeniusBaseChangeSection f g s p hS m hsg =
      absoluteFrobeniusPow (pullback f g) p
        (isInCharacteristic_of_hom (pullback.fst f g ≫ f) p hS) m
```
The omitted FieldTheory section 79–121 is closed before AlgebraicGeometry at 123. The section constructor needs hsg; its reverse-composite theorem additionally needs hgs.

## Unchanged local abelian-variety consumers

Q84
```lean
import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Group.Smooth
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety

/-! The extra smoothness in PkgI2 is a theorem, not an extra axiom.
The source predicate is Stacks Tag 03RO. Smoothness is Mathlib's
`AlgebraicGeometry.smooth_of_grpObj` (geometrically reduced + locally finite type).
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AxiomBridge

variable {k : Type u} [Field k]
```
Q85 P
```lean
theorem pkgI2_of_proper_geometricallyIntegral
    (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom] : PkgI2.IsAbelianVariety (Grp.mk A)
```
Q86 P
```lean
theorem pkgI2_of_axiom (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] :
    PkgI2.IsAbelianVariety (Grp.mk A)
```
Q87 P
```lean
theorem axiom_of_pkgI2 (A : Grp (Over (Spec (.of k))))
    (h : PkgI2.IsAbelianVariety A) : AlgebraicGeometry.IsAbelianVariety k A.X
```
Q88 P
```lean
theorem abelianVariety_iff (A : Grp (Over (Spec (.of k)))) :
    AlgebraicGeometry.IsAbelianVariety k A.X ↔ PkgI2.IsAbelianVariety A
```

## Unchanged local Jacobian consumers

Q89
```lean
import AxiomBridge.AbelianVariety
import Mordell.Jacobian.Existence
import Mordell.Jacobian.Dimension

open CategoryTheory AlgebraicGeometry

universe u

namespace AxiomBridge

variable {k : Type u} [Field k]
```
Q90 P
```lean
theorem jacobian_isAbelianVariety {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [Faltings.IsSmoothProjectiveCurve k f] (J : Faltings.Jacobian k f) :
    PkgI2.IsAbelianVariety (Grp.mk J.J)
```
Q91 P
```lean
theorem exists_pkgI2_jacobian (X : Faltings.CurveWithDegreeOneDivisor k) :
    (∃ J : Faltings.Jacobian k X.f,
      PkgI2.IsAbelianVariety (Grp.mk J.J) ∧
      topologicalKrullDim J.J.left = (genus X.f : WithBot ℕ∞)) ∧
    (∀ J J' : Faltings.Jacobian k X.f,
      ∃! e : J.J ≅ J'.J, J.ι ≫ yoneda.map e.hom = J'.ι)
```

## Unchanged local model consumers

Q92
```lean
import AxiomBridge.AbelianVariety
import Mordell.AbelianVariety.GoodReduction

/-! Faltings' flat, finitely presented model with geometrically integral group
fibres is already a PkgI2 abelian scheme. Smoothness follows fibrewise from
Mathlib's smooth group-scheme theorem, then from its flat smooth-fibre criterion.
The prime's valuation subring is identified with the localization inside k.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AxiomBridge
```
Q93 P
```lean
theorem geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}}
    (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f
```
Q94 P
```lean
theorem pkgI2_isAbelianScheme_of_fibres {O : Type u} [CommRing O]
    (G : Grp (Over (Spec (.of O))))
    (hF : Flat G.X.hom) (hP : IsProper G.X.hom)
    (hL : LocallyOfFinitePresentation G.X.hom)
    (hfib : ∀ w,
      IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj G.X).hom ∧
      GeometricallyIntegral
        ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj G.X).hom) :
    PkgI2.IsAbelianScheme G
```
Q95
```lean
-- With the focused `ZInQKernel.HDecomp.Objects` import (rather than a module importing all of
-- Mathlib), finding the monoidal structure of the pullback functor over the localized base in the
-- `change` below needs more than the default 20000 instance-search heartbeats (40000 suffice).
-- Only the search budget is raised; the theorem statement and tactic proof are unchanged.
set_option synthInstance.maxHeartbeats 80000 in
/-- Axiom's good reduction at a height-one prime implies PkgI2 good reduction
at its canonical adic valuation subring, with the same model and group isomorphism. -/
```
Q96 P
```lean
theorem pkgI2_hasGoodReduction_of_faltings
    (k : Type u) [Field k] [NumberField k]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom]
    (h : Faltings.HasGoodReduction k p A) :
    PkgI2.HasGoodReduction (Grp.mk A) (p.valuation k).valuationSubring
```
Proof omitted: original valuationSubringAtPrime_eq_valuationSubring/ofField_eq rewrites reuse the same model after fibrewise smoothness. The quoted synthInstance option is original; root/localization APIs remain imported, not a synthetic modelHyp constructor.

## Unchanged local point adjunction

Q97
```lean
import ZInQKernel.HDecomp.Objects
import Mordell.AbelianVariety.Reduction.Basic

/-! Actual point-group base change for the PkgI3 consumer.
No Tate freeness, dimension, semisimplicity or Galois comparison is assumed here. -/

namespace AxiomBridge

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {k : Type} [Field k] (A : PkgI3.AbVar k)
    (L : Type) [Field L] [Algebra k L]
```
Q98
```lean
/-- The original L-points are the rational points of the actual pullback group.
This is the multiplicative map/pullback adjunction, not a replacement object. -/
noncomputable def pointsBaseChangeMulEquiv :
    A.Pt L ≃* (𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ (A.baseChange L).X) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
  exact Faltings.mapPullbackAdjMulEquiv f (Grp.mk A.X)
    (𝟙_ (Over (Spec (CommRingCat.of L))))
```
Q99 P
```lean
theorem pointsBaseChangeMulEquiv_symm_left
    (x : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ (A.baseChange L).X) :
    ((pointsBaseChangeMulEquiv A L).symm x).left =
      x.left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))
```
Q100 P
```lean
theorem pointsBaseChangeMulEquiv_natural {B : PkgI3.AbVar k}
    (g : A.X ⟶ B.X) (x : A.Pt L) :
    pointsBaseChangeMulEquiv B L (x ≫ g) =
      pointsBaseChangeMulEquiv A L x ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map g
```

## Finite/nonempty dimension and base-change witness

Q101
```lean
import Mathlib

/- General scheme derivations reused verbatim from mirror83651ea scratch/g0-dim/Dim.lean.
Copied AbVar classes and copied HSyn predicates are intentionally excluded. -/
open Order TensorProduct

namespace G0Dim

```
Q102
```lean
open TopologicalSpace Topology
```
Q103
```lean
open AlgebraicGeometry CategoryTheory Limits

```
Q104 P
```lean
theorem dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X
```
Q105 P
```lean
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n
```
The full proof is omitted; Type0/finite-type/quasi-compact/nonempty guards remain. Original TateRank constructs nonemptiness from the unit section and consumes this witness, not a desired rank Fact.

## Exact available-result → consumer boundary

The unchanged local AV bridge supplies smoothness from the original proper/geometrically-integral group scheme. Jacobian existence/uniqueness and topological dimension feed the same local Jacobian type. Tate rank uses the actual algebraically-closed point group, prime-as-unit guard, base-change point adjunction and finite dimension witness. Good reduction reuses the same flat/proper/lfp/all-fibres model and generic-fibre group isomorphism after the localization/valuation-subring rewrite. Frobenius definitions preserve their exact direction and finite-field/perfect-extension assumptions.

This is targeted source-availability and full-telescope evidence, not proof-body replay. The immediate Picard functor body is supplied; its imported small Picard/degree/pullback helpers, projective/Mathlib geometry implementations, root Objects predicates and localization identities remain stated library-interface boundaries. Distinct similarly named AV classes are not silently equated. No automatic identification of relative twist with A, arbitrary field closure, global Tate/Galois/reduction square, integer polynomial or unconditional C10/H/Hilbert10 is claimed. Fresh compact-layout review and the unchanged trusted-gate budget measurement are required before publication; the earlier full-layout review is not relabeled as this version's acceptance.
