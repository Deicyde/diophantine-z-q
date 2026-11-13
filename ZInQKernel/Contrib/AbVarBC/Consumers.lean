import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.HDecomp.Faltings.HodgeLattice
import ZInQKernel.HDecomp.ModCurves.E1Sub

/-!
# Base change of abelian varieties, VII: consumers of `dim A_L = dim A`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

The kernel's hypotheses "dimension is invariant under base change" are discharged by
`PkgI3.AbVar.dim_baseChange` (`Contrib/AbVarBC/Dim.lean`, proved from Mathlib):
* hodge-lattice's `ZInQ.DefFaltings.HodgeLattice.DimBaseChange` (`dimBaseChange`), and the
  consumers `hodgeLatticeTheorem_of_tangent`, `…_of_abVarFacts`, `…_of_varieties`, `…_of_abVar`,
  `tangentDim_of_abVar`, `dimOrigin_of` without that hypothesis;
* e1-sub's `E1Sub.bcT_bijective` without its hypothesis `hdim`.
-/

namespace ZInQ.Contrib.AbVarBC

open ZInQ.DefFaltings.HodgeLattice

/-- **hodge-lattice's `DimBaseChange`, proved.** -/
theorem dimBaseChange : ZInQ.DefFaltings.HodgeLattice.DimBaseChange :=
  fun _ _ A L _ _ => A.dim_baseChange L

theorem dimOrigin_of' (h0 : OriginStalkIso) (h2 : DimAtOrigin) : DimOrigin :=
  dimOrigin_of h0 h2 dimBaseChange

theorem hodgeLatticeTheorem_of_abVar' (h0 : OriginStalkIso) (h1 : RegularAtOrigin)
    (h2 : DimAtOrigin) : ZInQ.DefFaltings.HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_abVar h0 h1 h2 dimBaseChange

theorem hodgeLatticeTheorem_of_varieties' (h0 : GenericFibreStalkIso) (h1 : RegularAtOrigin)
    (h2 : DimAtOrigin) : ZInQ.DefFaltings.HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_varieties h0 h1 h2 dimBaseChange

/-- `HodgeLatticeTheorem` from the two local facts `RegularAtOrigin`, `DimAtOrigin`. -/
theorem hodgeLatticeTheorem_of_abVarFacts' (h1 : RegularAtOrigin) (h2 : DimAtOrigin) :
    ZInQ.DefFaltings.HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_abVarFacts h1 h2 dimBaseChange

theorem tangentDim_of_abVar' (h1 : TangentDimAtOrigin) : TangentDim :=
  tangentDim_of_abVar h1 dimBaseChange

/-- **`HodgeLatticeTheorem` from the single fact `TangentDimAtOrigin`.** -/
theorem hodgeLatticeTheorem_of_tangent' (h1 : TangentDimAtOrigin) : ZInQ.DefFaltings.HodgeLatticeTheorem :=
  hodgeLatticeTheorem_of_tangent h1 dimBaseChange

/-- e1-sub's `bcT_bijective` without the hypothesis `hdim`. -/
theorem bcT_bijective' {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (ℓ : ℕ)
    [Fact ℓ.Prime] (hT : _root_.PkgI3.TateModuleFree) (J : _root_.PkgI3.AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) (hℓ : (ℓ : K) ≠ 0) :
    Function.Bijective (E1Sub.bcT ℓ J i) :=
  E1Sub.bcT_bijective ℓ hT J i hℓ (J.dim_baseChange L)

open CategoryTheory AlgebraicGeometry in
/-- `dim (A ×_{K, f} L) = dim A` for a field embedding `f : K → L`, stated for the object
`(Over.pullback (Spec f)).obj A.X` that g4-weilres's `bcAlong A f` (and so its conjugates
`(conjData K A).A e`) is built on. With it g4-weilres's hypothesis
`hdim : ∀ e, ((conjData K A).A e).dim = 2` follows from `A.dim = 2`:
`fun e => (dim_overPullback A (e : K →+* Qbar)).trans hA`. -/
theorem dim_overPullback {K L : Type} [Field K] [Field L] (A : _root_.PkgI3.AbVar K)
    (f : K →+* L) :
    topologicalKrullDim ((Over.pullback (Spec.map (CommRingCat.ofHom f))).obj A.X).left =
      A.dim := by
  letI : Algebra K L := f.toAlgebra
  exact dim_baseChange_scheme L A.X.left A.X.hom

end ZInQ.Contrib.AbVarBC
