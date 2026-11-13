import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.HDecomp.ModCurves.E1Sub

/-!
# Base change of abelian varieties, X: e1-sub's `bcT` is bijective with no hypothesis

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

e1-sub's point map `E1Sub.bcPhi J i : A(K̄) → A_L(L̄)` is the map `ptBC` of `Tate.lean`
(`bcPhi_eq_ptBC`), so `E1Sub.bcT ℓ J i = tateBC J i ℓ` and it is bijective in characteristic `0`
without `TateModuleFree` and without `hdim` (`bcT_bijective_charZero`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.AbVarBC

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- e1-sub's `bcPt` (points of `A` become points of `A_L`) is inverse to `bcPt` of
`Points.lean`. -/
theorem bcPt_e1 (J : _root_.PkgI3.AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (Q : J.Pt M) : bcPt J M (E1Sub.bcPt L J M Q) = Q := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (E1Sub.bcPt L J M Q).left ≫ pullback.fst _ _ = Q.left
  rw [Category.id_comp]
  exact E1Sub.bcPt_fst J M Q

theorem bcPhi_eq_ptBC (J : _root_.PkgI3.AbVar K) (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (p : J.Pt (AlgebraicClosure K)) : E1Sub.bcPhi J i p = ptBC J i p := by
  change E1Sub.bcPt L J _ (extPt J i p) = (bcPt J (AlgebraicClosure L)).symm (extPt J i p)
  rw [MulEquiv.eq_symm_apply, bcPt_e1]

theorem bcT_eq_tateBC (ℓ : ℕ) [Fact ℓ.Prime] (J : _root_.PkgI3.AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) : E1Sub.bcT ℓ J i = tateBC J i ℓ := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (bcPhi_eq_ptBC J i (Additive.toMul (x.1 n)))

/-- **e1-sub's `bcT_bijective` without `TateModuleFree` and `hdim`** (characteristic `0`). -/
theorem bcT_bijective_charZero [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (J : _root_.PkgI3.AbVar K)
    (i : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) : Function.Bijective (E1Sub.bcT ℓ J i) := by
  rw [bcT_eq_tateBC]
  exact tateBC_bijective J i ℓ

end ZInQ.Contrib.AbVarBC
