import ZInQKernel.Contrib.OneProof.CMHeight62.ShortModel
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open HDec.CMBranch.CMjBridges
variable {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L]

noncomputable def bcProj : (A.baseChange L).X.left ⟶ A.X.left :=
  pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))

example : (η[(A.baseChange L).X]).left ≫ bcProj A L =
    (Functor.LaxMonoidal.ε (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))).left ≫
      pullback.fst _ _ ≫ (η[A.X]).left := by
  show (Functor.LaxMonoidal.ε (Over.pullback _) ≫ (Over.pullback _).map η[A.X]).left ≫ _ = _
  simp [bcProj]
