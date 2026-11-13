import Mathlib

/-!
# bp-faltings: the model layer, as Lean signatures over Mathlib (nodes AV1, AV5, M1)

Draft for `docs/research/bp-faltings.md` §3. Mathlib-only.

* `AbVar K` and `AbVar.baseChange` are copied verbatim from `ZInQKernel/HDecomp/Objects.lean`
  (adopted there from task obj-bridge / pkg-I3), so that this file is self-contained.
* `GroupModel A L`: a smooth, separated, quasi-compact group scheme over `𝓞_L` together with an
  isomorphism of group schemes from its generic fibre to `A_L`. These are the models over which
  the infimum definition of the stable Faltings height ranges (blueprint node M1). By the Néron
  mapping property every such `𝒢` maps to the Néron model, so Néron models are needed only for
  theorems about the definition, not for the definition.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.BPFaltings

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group
object in schemes over `Spec K` whose structure morphism is proper, smooth and geometrically
integral. -/
structure AbVar (K : Type) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

/-- Commutativity is a Mathlib theorem, not an assumption. -/
instance (K : Type) [Field K] (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) Base change `A_L` along `L/K`. -/
noncomputable def baseChange {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L]
    [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

end AbVar

open NumberField

/-- The generic fibre `𝒢_L` of a scheme `𝒢` over `𝓞_L`. -/
noncomputable def genericFibre (L : Type) [Field L] [NumberField L]
    (G : Over (Spec (CommRingCat.of (𝓞 L)))) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj G

/-- **Node M1. A smooth group-scheme model of `A_L` over `𝓞_L`.** A group object `𝒢` of
`Over (Spec 𝓞_L)` with smooth, separated, quasi-compact structure morphism (so of finite type),
with an isomorphism of group objects `𝒢_L ≅ A_L`. -/
structure GroupModel {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] where
  /-- the model -/
  G : Over (Spec (CommRingCat.of (𝓞 L)))
  [grp : GrpObj G]
  [smooth : Smooth G.hom]
  [separated : IsSeparated G.hom]
  [qc : QuasiCompact G.hom]
  /-- the identification of the generic fibre with `A_L` -/
  gen : genericFibre L G ≅ (A.baseChange L).X
  /-- ... as group schemes (the group structure on `𝒢_L` is transported by `Over.pullback`) -/
  gen_hom : letI : GrpObj (genericFibre L G) := Functor.grpObjObj
    IsMonHom gen.hom

attribute [instance] GroupModel.grp GroupModel.smooth GroupModel.separated GroupModel.qc

/-- Sanity check: the generic fibre of a model is smooth over `L` (Mathlib: smoothness is stable
under base change). -/
example {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : Smooth (genericFibre L 𝒢.G).hom := by
  dsimp [genericFibre]; infer_instance

/-- Sanity check: the generic fibre of a model is separated (stable under base change). -/
example {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) : IsSeparated (genericFibre L 𝒢.G).hom := by
  dsimp [genericFibre]; infer_instance

/-!
## The remaining signatures (not compiled; to be built by the nodes named)

```lean
-- AV2: relative dimension
def AbVar.dim (A : AbVar K) : ℕ
-- AV3/AV4: invariant differentials and their determinant line
def AbVar.omega (A : AbVar K) : Type        -- e*Ω¹_{A/K}, a K-vector space of dimension g
def AbVar.detOmega (A : AbVar K) : Type     -- ⋀[K]^g ω_A, a K-line
-- M2/M3: the lattice of a model
def GroupModel.detLattice (𝒢 : GroupModel A L) : Submodule (𝓞 L) (A.baseChange L).detOmega
-- AN3: the uniformization at σ : L →+* ℂ
def AbVar.periodData (A : AbVar ℂ) : (Submodule ℤ (Fin A.dim → ℂ)) × (A.detOmega →ₗ[ℂ] ℂ)
-- M4: assemble
def GroupModel.hodgeData (𝒢 : GroupModel A L) : HodgeData L A.dim (A.baseChange L).detOmega
-- H2, H3
def GroupModel.height (𝒢 : GroupModel A L) : ℝ := 𝒢.hodgeData.modelHeight
def AbVar.stableFaltingsHeight (A : AbVar K) : EReal :=
  ⨅ (L : FiniteExtension K) (𝒢 : GroupModel A L), (𝒢.height : EReal)
-- H5 (theorem, needs Néron models and semistable reduction): it is finite, and equals
-- 𝒩.height for the Néron model 𝒩 over any L where A has semistable reduction.
```
-/

end ZInQ.BPFaltings
