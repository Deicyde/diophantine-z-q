import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.SameOpenGroup
import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings
import ZInQKernel.Contrib.OneProof.SGA3NbhdDVR

/-!
# Connect the actual residue fibres to the printed semiabelian witness

The open subgroup in the special fibre is the base change of the specified global
open inclusion. Comparing ranges identifies it over the same ambient fibre with the
subgroup in the printed residue-field semistability statement.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj NumberField

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.HeightFix ZInQ.SemistabAssembly
open DictModels.RaynaudOr (HasSemiAbelianIdCompTorus)
open CToPrinted (idCompSet)

/-- A specified open subgroup with exactly the printed identity-component image is
connected and has the semiabelian structure of the original printed witness. -/
theorem semiabelian_of_printed_component_range {k : Type} [Field k]
    {U N : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj N]
    (j : U ⟶ N) [IsOpenImmersion j.left] [IsMonHom j]
    (hj : Set.range j.left = connectedComponent (unitPt N))
    (hN : HasSemiAbelianG0Torus N) :
    ConnectedSpace U.left ∧ HasSemiAbelianIdCompTorus U := by
  obtain ⟨V, hV, i, hio, him, hRange, rest⟩ := hN
  have : IsOpenImmersion i.left := hio
  have : IsMonHom i := him
  have hc : ConnectedSpace V.left := by
    have h : _root_.IsConnected (i.left '' Set.univ) := by
      rw [Set.image_univ, hRange]
      exact isConnected_connectedComponent
    rw [connectedSpace_iff_univ]
    exact ⟨h.nonempty.of_image, i.left.isOpenEmbedding.isInducing.isPreconnected_image.mp h.isPreconnected⟩
  obtain ⟨e, he, _⟩ := exists_open_group_iso_of_range_eq i j (hRange.trans hj.symm)
  let e₀ := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have : IsIso e.hom.left := e₀.isIso_hom
  have hU : ConnectedSpace U.left := (Scheme.homeoOfIso e₀).connectedSpace_iff.mp hc
  exact ⟨hU, ⟨V, hV, e.hom, inferInstance, he, hc, rest⟩⟩

/-- If the specified open insertion is the global identity component, its actual
special fibres are connected semiabelian schemes. This uses the residue-field
part of the printed semistability, not only the geometric part. -/
theorem semiabelian_resFibres_of_component_range {K L : Type} [Field K] [Field L]
    [NumberField L] [Algebra K L] {A : PkgI3.AbVar K}
    (U N : GroupModel A L) (j : U.G ⟶ N.G) [IsOpenImmersion j.left] [IsMonHom j]
    (hOpen : IsOpen (idCompSet N.G)) (hj : Set.range j.left = idCompSet N.G)
    (hN : IsSemistableResPrinted N) (p : Ideal (𝓞 L)) [p.IsMaximal] :
    ConnectedSpace (resFibre U p).left ∧ HasSemiAbelianIdCompTorus (resFibre U p) := by
  let P := Over.pullback (sResP p)
  let : GrpObj (P.obj U.G) := Functor.grpObjObj
  let : GrpObj (P.obj N.G) := Functor.grpObjObj
  let i : P.obj U.G ⟶ P.obj N.G := P.map j
  have hiOpen : IsOpenImmersion i.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ j
  have hiMon : IsMonHom i := inferInstanceAs (IsMonHom (P.map j))
  have hRange : Set.range i.left = connectedComponent (unitPt (P.obj N.G)) := by
    calc
      _ = pullback.fst N.G.hom (sResP p) ⁻¹' Set.range j.left := range_over_pullback_map _ j
      _ = idCompSet (P.obj N.G) := by
        rw [hj]
        exact SGA3Nbhd.idComp_baseChange' geomConnOfRationalPoint_proof (sResP p) N.G hOpen
      _ = _ := ZInQ.SemiAbDescend.idCompSet_eq_cc _ default
  exact @semiabelian_of_printed_component_range _ _ _ _ _ _ i hiOpen hiMon hRange (hN p)

#print axioms semiabelian_of_printed_component_range
#print axioms semiabelian_resFibres_of_component_range

end ZInQ.Contrib.IsogenyDegree
