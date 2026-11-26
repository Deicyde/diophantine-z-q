import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.ProEt

universe u

variable {S : Scheme.{u}}

/-- Finite affine pieces of the specified cover: each lies in the given
sieve, and the underlying actual maps are jointly surjective. -/
structure FiniteAffineCoverPieces (U : S.ProEt) (R : Sieve U) where
  n : ℕ
  A : Fin n → S.ProEt
  a : ∀ i, A i ⟶ U
  affine (i : Fin n) : IsAffine (A i).left
  weak (i : Fin n) : WeaklyEtale (a i).left
  mem (i : Fin n) : R (a i)
  covers (x : U.left) : ∃ (i : Fin n) (y : (A i).left), (a i).left y = x

/-- On an affine target, choose finitely many affine restrictions of a
basic pro-étale cover in the original covering sieve. -/
theorem nonempty_finiteAffineCoverPieces_of_covering
    {U : S.ProEt} [IsAffine U.left] {R : Sieve U}
    (hR : R ∈ topology S U) : Nonempty (FiniteAffineCoverPieces U R) := by
  classical
  let L : S.ProEt ⥤ Scheme.{u} := ProEt.forget S ⋙ Over.forget S
  let J : Precoverage S.ProEt := proetalePrecoverage.comap L
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan L :=
    inferInstanceAs (Limits.PreservesLimitsOfShape Limits.WalkingCospan (ProEt.forget S ⋙ Over.forget S))
  let : J.IsStableUnderComposition := inferInstanceAs (proetalePrecoverage.comap L).IsStableUnderComposition
  let : J.IsStableUnderBaseChange := inferInstanceAs (proetalePrecoverage.comap L).IsStableUnderBaseChange
  let : J.HasIsos := inferInstanceAs (proetalePrecoverage.comap L).HasIsos
  let : J.HasPullbacks := inferInstance
  have hb : ∃ P ∈ precoverage S U, P ≤ R :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition (J := J)).1 hR
  obtain ⟨P, hP, hPR⟩ := hb
  obtain ⟨E, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hP
  let E' : U.left.Cover proetalePrecoverage :=
    E.map L (show precoverage S ≤ proetalePrecoverage.comap L from le_rfl)
  let C : U.left.Cover fpqcPrecoverage := E'.weaken proetalePrecoverage_le_fpqcPrecoverage
  let : QuasiCompactCover C.toPreZeroHypercover := presieve₀_mem_qcPrecoverage_iff.mp C.mem₀.1
  obtain ⟨n, k, V, hV, hC⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact C.toPreZeroHypercover
    (U := ⊤) (isAffineOpen_top U.left).isCompact
  let X (i : Fin n) : Scheme.{u} := (V i).toScheme
  let r (i : Fin n) : X i ⟶ (E.X (k i)).left := (V i).ι
  let f (i : Fin n) : X i ⟶ U.left := r i ≫ (E.f (k i)).left
  have hf (i : Fin n) : WeaklyEtale (f i) := by
    let : WeaklyEtale ((E.f (k i)).left) := (Scheme.Cover.forgetQc E').map_prop (k i)
    let : IsOpenImmersion (r i) := (inferInstance : IsOpenImmersion (V i).ι)
    let : Etale (r i) := inferInstance
    change WeaklyEtale (r i ≫ (E.f (k i)).left)
    infer_instance
  let A (i : Fin n) : S.ProEt :=
    let : WeaklyEtale (f i) := hf i
    ProEt.mk (f i ≫ U.hom)
  let a (i : Fin n) : A i ⟶ U :=
    MorphismProperty.Over.homMk (P := @WeaklyEtale) (Q := ⊤) (X := S) (f i) rfl
  let b (i : Fin n) : A i ⟶ E.X (k i) :=
    MorphismProperty.Over.homMk (P := @WeaklyEtale) (Q := ⊤) (X := S) (r i) (by
      change r i ≫ (E.X (k i)).hom = (r i ≫ (E.f (k i)).left) ≫ U.hom
      exact (congrArg (fun g => r i ≫ g) (MorphismProperty.Over.w (E.f (k i))).symm).trans
        (Category.assoc _ _ _).symm)
  have ha (i : Fin n) : R (a i) := by
    have hi : R (E.f (k i)) := hPR _ _ (Presieve.ofArrows.mk (k i))
    have hba : b i ≫ E.f (k i) = a i := MorphismProperty.Over.Hom.ext rfl
    exact hba ▸ R.downward_closed hi (b i)
  have hcover (x : U.left) : ∃ (i : Fin n) (y : (A i).left), (a i).left y = x := by
    have hx : x ∈ ⋃ i, C.f (k i) '' (V i : Set (C.X (k i))) := by
      rw [hC]
      trivial
    obtain ⟨i, y, hy, ey⟩ := Set.mem_iUnion.mp hx
    let y' : X i := ⟨y, hy⟩
    refine ⟨i, y', ?_⟩
    change (r i ≫ (E.f (k i)).left) y' = x
    exact (Scheme.Hom.comp_apply (r i) (E.f (k i)).left y').trans
      (show (E.f (k i)).left ((r i) y') = x from ey)
  exact ⟨⟨n, A, a, (fun i => hV i), hf, ha, hcover⟩⟩

end AlgebraicGeometry.Scheme.ProEt
