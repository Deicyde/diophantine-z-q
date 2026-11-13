/-! # lt-local, part 5: `ModelEndRank4` from `FibreSimple` and linked-tate's `QMEndRank`

Verbatim copies from `scratch/linked-tate/LinkedTate.lean` (with their namespace headers and opens):
* def-faltings' `ZInQ.DefFaltings.AbVar`, `AbVar.baseChange` (l.17119, l.18210-18236);
* leaf-adopt's `LeafAdopt.abVarEquiv` (l.19042-19045, l.19196-19201);
* g0-split's `HSyn.G0Split.FibreOver` and `FibreSimple` (l.33338-33340, l.33577-33590,
  l.33712-33722; `FibreSimple` is the existing `GluePieces` piece, supplied in `GluePieces3`
  through FS5);
* linked-tate's `HSyn.LinkedTate.QMEndRank` (l.42841-42844, l.43121-43135; GLUE, literature-backed:
  Mumford §19 Thm 3 and Albert's classification, §21, numbering UNVERIFIED).
New: `endDivision_of_fibreSimple` (linked-tate's proof, copied) and `modelEndRank4_of_qmEndRank`
(the argument of linked-tate's `linkedTateCore_of`). -/

noncomputable section

namespace ZInQ.DefFaltings

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group
object in schemes over `Spec K`, proper, smooth and geometrically integral. -/
structure AbVar (K : Type) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

/-- (copied) Base change `A_L`. -/
noncomputable def AbVar.baseChange {K : Type} [Field K] (A : AbVar K) (L : Type) [Field L]
    [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

end ModelsSec

end ZInQ.DefFaltings

namespace LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Bridge (proved)**: def-faltings' copy of the abelian-variety structure and this file's
`PkgI3.AbVar` (= the kernel's) are the same data (for `K : Type`), so R19-R21 and H5 transfer to
`PkgI3.AbVar` along this equivalence; unifying the two declarations is WP1 work. -/
def abVarEquiv (K : Type) [Field K] : ZInQ.DefFaltings.AbVar K ≃ PkgI3.AbVar K where
  toFun A := { X := A.X }
  invFun A := { X := A.X }

end LeafAdopt

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

/-- `A`, an abelian variety over the number field `K` (def-faltings' `AbVar`), is (up to
isomorphism of `ℚ̄`-schemes, after some embedding `K → ℚ̄`) the abelian surface of an object
`(A, ι, η)` of `Y₃` at a `ℚ̄`-point `y` of `Y₃` lying over `J(u)` (for the moduli data
`(Y, Φ, π)` that R1-R2 provide). -/
def FibreOver (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) : Prop :=
  ∃ (emb : K.K →+* Qbar) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) ∧
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X))

/-- **Missing piece 4 (glue G5-G6 on the actual `A`: QM dichotomy and NoCM).** For `u ∉ 𝒞`, the
fibre surface `A` (any number-field model of it) is simple over its field: every nonzero
endomorphism is an isogeny (because `End⁰(A_ℚ̄) = B` is a division algebra). Proved parts: T27 at
`B = (2,-3)` (`PkgI3.qmDichotomy_B6`), the Elkies identities and the free `W`-orbit
(`GlueRepo.PR.fibre_free`), `cm_of_val`. Missing: the instantiation on `A` and the counting with
R5 (h-decomposition G6). -/
def FibreSimple : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

end G0Split

end HSyn

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **Glue: the endomorphism ring of the QM model has rank 4** (linked-tate; G5-G6 + A9, N5
L564-577). For a `QML3` object `PK` over `K ⊆ ℚ̄` and a tower `K ≤ L ≤ L'` (`L'/ℚ` finite), if every
nonzero endomorphism of `A' = (PK.A)_{L,L'}` is an isogeny (`EndDivision`, which `FibreSimple`
supplies for the fibre), then `End_{L'}(A')` is a free `ℤ`-module of rank 4. Route (STANDARD,
UNVERIFIED numbering): `End(A')` is finitely generated and torsion-free (Mumford §19 Thm 3:
`End ⊗ ℤ_ℓ ↪ End T_ℓ`), so free; `End⁰(A')` is a division algebra containing `ι(B)`, `B = (2,−3)`
of dimension 4, and by Albert's classification for simple abelian surfaces in characteristic 0
(Mumford §21) it is `ℚ`, real quadratic, CM quartic or an indefinite quaternion algebra over `ℚ`;
only the last contains `B`, so `End⁰(A') = B`. GLUE (literature-backed). -/
def QMEndRank : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K),
    PkgI3.EndDivision (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) = 4

end HSyn.LinkedTate

namespace LTLocal

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- (copied from linked-tate; `Qbar` written `PkgI4.Qbar`) **`EndDivision` for every number-field model of the fibre, from the
glue piece `FibreSimple`** (proved). -/
theorem endDivision_of_fibreSimple (hFS : HSyn.G0Split.FibreSimple)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y} {π : LeafQM.AV.ToP1 Y.left} {u : ℚ}
    {P : LeafQM.AV.QML3 PkgI4.Qbar} (hctx : FibreCtx Y Φ π u P) (L' : IF)
    [FiniteDimensional ℚ L'] (A' : PkgI3.AbVar L') (hA' : IsModelOver L' A' P) :
    PkgI3.EndDivision A' := by
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  haveI : NumberField L' := numberField_of_fd L'
  exact hFS Y Φ π h1 h2 u hu ⟨L'⟩ ((LeafAdopt.abVarEquiv L').symm A')
    ⟨algebraMap L' PkgI4.Qbar, y, P, hy, hπ, hA'⟩

/-- **`ModelEndRank4` from `FibreSimple` and `QMEndRank` (proved;** the argument of linked-tate's
`linkedTateCore_of`): G7Data's `IsQMModel` writes `A = (PK.A)_L`, its last clause gives
`EndDivision A_{L'}` through `FibreSimple`, and `QMEndRank` gives the rank. -/
theorem modelEndRank4_of_qmEndRank (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) : ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  exact hR K L L' hKL hLL' PK (endDivision_of_fibreSimple hFS hctx L' _ hmod)

/-- **`LinkedTateLocalD` from `TateBridge35`, `FibreSimple` and `QMEndRank` (proved).** -/
theorem linkedTateLocalD_of_tateBridge35' (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) : LinkedTateLocalD :=
  linkedTateLocalD_of_tateBridge35 hR6 hTors hU5 hU3 hB (modelEndRank4_of_qmEndRank hFS hR)

end LTLocal

end
