/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.Contrib.CloudB3W13.OrderBridge
import ZInQKernel.Contrib.CloudB3W13.Source.Definitions.Def_CerednikDrinfeld_QMFineModuli
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

/-!
# W13 dictionary interfaces (UNPROVED obligations, stated as `Prop`s)

Kernel side: `PkgI3.AbVar`, `LeafQM.AV.{QMStr, Level3, QML3, QML3.Iso}` (`ZInQKernel/HDecomp/...`).
FLT side (W13 prefixed port of anthropics/fermats-last-theorem@6e837e75, namespace
`ZInQ.Contrib.CloudW03NeronSurj.FLT`): `CerednikDrinfeld.QM.FakeEllipticCurve`, `FullLevel`,
`WithFullLevel`, `RelativeGroupLaw.grpObjOverMk`.

Nothing here is a proof of D2–D5: the `def … : Prop` below are the exact obligations handed to the
dictionary lanes; the only definitions with content are the constructions `abVarOfFakeEC`,
`fltLevelPoint`, which take the D2 conclusion as an explicit hypothesis (no axiom, no `sorry`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj

/-- The FLT order lattice used throughout (`= LeafQM.O` as a `ℤ`-submodule; `order_bridge`). -/
abbrev Λ : Submodule ℤ ℍ[ℚ, 2, -3] := oLattice

/-- A kernel order element as an element of the FLT lattice (`order_bridge`, membership is `Iff.rfl`). -/
def toΛ (a : LeafQM.O) : ↥Λ := ⟨(a : ℍ[ℚ, 2, -3]), (order_bridge.2.2 _).mpr a.2⟩

abbrev FakeEC (K : Type) [Field K] := FLT.CerednikDrinfeld.QM.FakeEllipticCurve Λ 1 K
abbrev FLTL3 (K : Type) [Field K] := FLT.CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ 1 3 K

/-- The three geometric properties needed to view a fake elliptic curve over a field as a kernel
abelian variety. -/
def AbVarProps {K : Type} [Field K] (E : FakeEC K) : Prop :=
  IsProper E.f ∧ Smooth E.f ∧ GeometricallyIntegral E.f

/-- **Construction (no content beyond packaging):** the kernel abelian variety of `E`, with the
group object `RelativeGroupLaw.grpObjOverMk E.L` on `Over.mk E.f`. -/
def abVarOfFakeEC {K : Type} [Field K] (E : FakeEC K) (h : AbVarProps E) : PkgI3.AbVar K :=
  letI : GrpObj (Over.mk E.f) := E.L.grpObjOverMk
  haveI : IsProper (Over.mk E.f).hom := h.1
  haveI : Smooth (Over.mk E.f).hom := h.2.1
  haveI : GeometricallyIntegral (Over.mk E.f).hom := h.2.2
  { X := Over.mk E.f }

/-- **D2 (UNPROVED obligation; lane "D2 genuine AbVar/geometric integrality").** Over a field of
characteristic zero a fake elliptic curve (N = 1) is proper, smooth and geometrically integral, and
the resulting abelian variety is a surface. -/
def D2_Obligation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (E : FakeEC K),
    ∃ h : AbVarProps E, (abVarOfFakeEC E h).dim = 2

/-- The `K`-point `x · P` of the level datum (FLT side), as a morphism `Spec K ⟶ E.A`. -/
def fltLevelPoint {K : Type} [Field K] (u : FLTL3 K) (a : LeafQM.O) :
    Spec (CommRingCat.of K) ⟶ u.1.A :=
  (FLT.CerednikDrinfeld.QM.pushPt (u.1.act (toΛ a)) (u.1.act_over (toΛ a)) u.2.P).1

/-- **D3/D4 (UNPROVED obligation; lane "D3/D4 action-injectivity + Level bridge").** Over a field of
characteristic zero, the FLT action of `Λ = 𝒪` on a fake elliptic curve with full level-3 datum is an
(injective) kernel QM structure whose underlying endomorphisms are `act`, and `a ↦ a · P` is a
kernel level-3 structure. Stated for every `h : AbVarProps u.1` (it does not presuppose D2). -/
def D34_Obligation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (u : FLTL3 K) (h : AbVarProps u.1),
    ∃ q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h),
      (∀ a : LeafQM.O, (q.iota a).hom.left = u.1.act (toΛ a)) ∧
      ∃ e : LeafQM.AV.Level3 q, ∀ a : LeafQM.O, (Additive.toMul (e.eta a)).left = fltLevelPoint u a

/-- **D5 (UNPROVED obligation; lane "D5 tangent-reduced-trace converse").** Every kernel object over
`ℚ̄` is isomorphic (as a kernel `QML3`) to one coming from an FLT fake elliptic curve with full
level-3 datum through the packaging above, with the `QMStr`/`Level3` determined by `act` and `P`
exactly as in D3/D4. (Its proof must construct `act_trace`, the `N = 1` level datum and
`FullLevel.generates/annihilator`; it may use D2 and D3/D4 only through their statements.) -/
def D5_Obligation : Prop :=
  ∀ P : LeafQM.AV.QML3 LeafQM.AV.Qbar,
    ∃ (u : FLTL3 LeafQM.AV.Qbar) (h : AbVarProps u.1) (hs : (abVarOfFakeEC u.1 h).dim = 2)
      (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q),
      (∀ a : LeafQM.O, (q.iota a).hom.left = u.1.act (toΛ a)) ∧
      (∀ a : LeafQM.O, (Additive.toMul (e.eta a)).left = fltLevelPoint u a) ∧
      Nonempty (LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u.1 h, hs, q, e⟩ P)

end ZInQ.Contrib.CloudB2Shimura.Dictionary
