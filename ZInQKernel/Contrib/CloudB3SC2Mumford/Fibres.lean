import ZInQKernel.Contrib.CloudB3SC2Mumford.Interfaces
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import ZInQKernel.Contrib.OneProof.MumfordRigidity
import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# Fibre preparation for the affine Mumford group-law theorem

The hypotheses here are the original scheme-theoretic fibre hypotheses, not pointwise
identifications. In particular the comparison of fibres uses isomorphisms of pullback schemes
and retains their structure sheaves over nonreduced test schemes.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudB3SC2Mumford

/-- An original abelian variety supplies the vendored, scheme-level abelian-scheme bundle. -/
theorem abelianBundle_of_abVar {k : Type} [Field k] (A : PkgI3.AbVar k) :
    AbelianSchemePropertyBundle k A.X.hom := by
  haveI : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro s
    have ht : A.X.hom.base ⁻¹' {s} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [ht]
    exact isConnected_univ
  · haveI : GrpObj (Over.mk A.X.hom) := A.grp
    exact ⟨relativeGroupLawOfGrpObj k A.X.hom⟩

/-- The original all-field fibre hypothesis gives the geometric-fibre bundles for any affine
base change. No property of the original base's nilpotents is discarded. -/
theorem abelianBundle_geometric_pullback {S : Scheme.{0}} (F : Over S)
    (e : S ⟶ F.left)
    (hfib : ∀ (k : Type) [Field k] (s : Spec (CommRingCat.of k) ⟶ S),
      ∃ (A : PkgI3.AbVar k) (g : A.X.left ⟶ F.left),
        LeafQM.AV.R1UnivRigid.IsAbVarFibre F e s A g)
    {R : Type} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)
    (k : Type) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    AbelianSchemePropertyBundle k (pullback.snd (pullback.snd F.hom a) s) := by
  obtain ⟨A, g, hA, _⟩ := hfib k (s ≫ a)
  let sq := (IsPullback.of_hasPullback (pullback.snd F.hom a) s).paste_horiz
    (IsPullback.of_hasPullback F.hom a)
  let E := hA.isoPullback ≪≫ sq.isoPullback.symm
  have he : E.inv ≫ A.X.hom = pullback.snd (pullback.snd F.hom a) s := by
    simp only [E, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      hA.isoPullback_inv_snd, sq.isoPullback_hom_snd]
  exact (abelianBundle_of_abVar A).of_isPullback
    (ι := 𝟙 (Spec (CommRingCat.of k)))
    (IsPullback.of_horiz_isIso ⟨by simpa using he⟩)

/-- Pull back the prescribed identity section to an affine base. -/
def affineSection {S : Scheme.{0}} (F : Over S) (e : S ⟶ F.left)
    (he : e ≫ F.hom = 𝟙 S) {R : Type} [CommRing R]
    (a : Spec (CommRingCat.of R) ⟶ S) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (pullback.snd F.hom a) :=
  ⟨pullback.lift (a ≫ e) (𝟙 _) (by simp only [Category.assoc, he,
    Category.comp_id, Category.id_comp]), pullback.lift_snd _ _ _⟩

/-- The unique affine group law with the original section as identity. -/
theorem exists_unique_affineLaw (h : AffineGroupLaw.{0}) {S : Scheme.{0}} (F : Over S)
    (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S)
    [Smooth F.hom] [IsProper F.hom] [GeometricallyConnected F.hom]
    (hfib : ∀ (k : Type) [Field k] (s : Spec (CommRingCat.of k) ⟶ S),
      ∃ (A : PkgI3.AbVar k) (g : A.X.left ⟶ F.left),
        LeafQM.AV.R1UnivRigid.IsAbVarFibre F e s A g)
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (a : Spec (CommRingCat.of R) ⟶ S) :
    ∃ L : RelativeGroupLaw R (pullback.snd F.hom a),
      L.one (𝟙 _) = affineSection F e he a ∧ L.IsCommutative ∧
      ∀ L' : RelativeGroupLaw R (pullback.snd F.hom a),
        L'.one (𝟙 _) = affineSection F e he a → L' = L := by
  apply h (pullback.snd F.hom a) inferInstance inferInstance
    (fun s => (pullback.snd F.hom a).isConnected_preimage_singleton s)
    (affineSection F e he a)
  intro k _ _ s
  exact abelianBundle_geometric_pullback F e hfib a k s

/-- The affine coordinate ring in the directed cover of a locally noetherian scheme is
noetherian, as required by the affine theorem. -/
theorem affineOpen_noetherian {S : Scheme.{0}} [IsLocallyNoetherian S]
    (U : S.affineOpens) : IsNoetherianRing Γ(S, U.1) :=
  IsLocallyNoetherian.component_noetherian U

end ZInQ.Contrib.CloudB3SC2Mumford
