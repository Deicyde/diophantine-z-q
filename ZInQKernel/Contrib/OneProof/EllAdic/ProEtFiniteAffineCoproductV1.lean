import ZInQKernel.Contrib.OneProof.EllAdic.ProEtFiniteAffineCoverPiecesV1

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

universe u

variable {S : Scheme.{u}}

/-- The affine singleton precover and its covering coproduct components.
Membership in the original sieve is retained on the component composites. -/
structure FiniteAffineSingletonRefinement (U : S.ProEt) (R : Sieve U) where
  n : ℕ
  A : Fin n → S.ProEt
  W : S.ProEt
  q : W ⟶ U
  j : ∀ i, A i ⟶ W
  coproductIso : W.left ≅ ∐ (fun i => (A i).left)
  j_eq (i : Fin n) : (j i).left ≫ coproductIso.hom = Sigma.ι (fun k => (A k).left) i
  mem (i : Fin n) : R (j i ≫ q)
  affineW : IsAffine W.left
  weaklyEtaleQ : WeaklyEtale q.left
  surjectiveQ : Surjective q.left
  singletonQ : Presieve.singleton q ∈ precoverage S U
  coverJ : Presieve.ofArrows A j ∈ precoverage S W

/-- Assemble a particular finite affine subfamily by the actual scheme
coproduct. This is a precover with component membership, not an assertion
that an arbitrary sieve contains the assembled coproduct map. -/
theorem nonempty_finiteAffineSingletonRefinement_from_pieces
    {U : S.ProEt} [IsAffine U.left] {R : Sieve U} (D : FiniteAffineCoverPieces U R) :
    Nonempty (FiniteAffineSingletonRefinement U R) := by
  let X (i : Fin D.n) := (D.A i).left
  let f (i : Fin D.n) : X i ⟶ U.left := (D.a i).left
  let d : (∐ X) ⟶ U.left := Sigma.desc f
  have hi (i : Fin D.n) : Sigma.ι X i ≫ d = f i := Sigma.ι_comp_desc f i
  let : ∀ i, IsAffine (X i) := D.affine
  let : IsAffine (∐ X) := inferInstance
  let : IsAffineHom d := isAffineHom_of_isAffine d
  let : WeaklyEtale d := IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) D.weak
  let : Surjective d := by
    constructor
    intro x
    obtain ⟨i, y, hy⟩ := D.covers x
    refine ⟨Sigma.ι X i y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hi i]
    exact hy
  let W : S.ProEt := ProEt.mk (d ≫ U.hom)
  let q : W ⟶ U := MorphismProperty.Over.homMk (P := @WeaklyEtale) (Q := ⊤) (X := S) d rfl
  let j (i : Fin D.n) : D.A i ⟶ W := MorphismProperty.Over.homMk
    (P := @WeaklyEtale) (Q := ⊤) (X := S) (Sigma.ι X i) (by
      change Sigma.ι X i ≫ (d ≫ U.hom) = (D.A i).hom
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ U.hom) (hi i)).trans (MorphismProperty.Over.w (D.a i))))
  have hfac (i : Fin D.n) : j i ≫ q = D.a i := MorphismProperty.Over.Hom.ext (hi i)
  have hq : Presieve.singleton q ∈ precoverage S U := by
    rw [precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton]
    change Presieve.singleton d ∈ Scheme.propQCPrecoverage (@WeaklyEtale : MorphismProperty Scheme.{u}) U.left
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := (@WeaklyEtale : MorphismProperty Scheme.{u}))
      (f := d) (inferInstance : WeaklyEtale d)
  have hj : Presieve.ofArrows D.A j ∈ precoverage S W := by
    have hle : Scheme.zariskiPrecoverage.{u} ≤ Scheme.etalePrecoverage.{u} := by
      apply Scheme.precoverage_mono
      intro Y Z k hk
      let : IsOpenImmersion k := hk
      exact (inferInstance : Etale k)
    rw [precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    change Presieve.ofArrows X (Sigma.ι X) ∈ Scheme.proetalePrecoverage (∐ X)
    exact Scheme.etalePrecoverage_le_proetalePrecoverage _ (hle _ (AlgebraicGeometry.sigmaOpenCover X).mem₀)
  refine ⟨⟨D.n, D.A, W, q, j, Iso.refl _, ?_, ?_, ?_, ?_, ?_, hq, hj⟩⟩
  · intro i
    exact Category.comp_id (Sigma.ι X i)
  · intro i
    exact (hfac i).symm ▸ D.mem i
  · exact (inferInstance : IsAffine (∐ X))
  · exact (inferInstance : WeaklyEtale d)
  · exact (inferInstance : Surjective d)

/-- Choose and assemble finite affine pieces from a covering sieve. -/
theorem nonempty_finiteAffineSingletonRefinement {U : S.ProEt} [IsAffine U.left]
    {R : Sieve U} (hR : R ∈ topology S U) : Nonempty (FiniteAffineSingletonRefinement U R) :=
  (nonempty_finiteAffineCoverPieces_of_covering hR).elim
    nonempty_finiteAffineSingletonRefinement_from_pieces

end AlgebraicGeometry.Scheme.ProEt
