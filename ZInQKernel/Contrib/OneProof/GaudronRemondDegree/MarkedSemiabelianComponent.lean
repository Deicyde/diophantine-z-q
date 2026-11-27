import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.GlobalIdCompFromGoodOpen
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.GoodOpenReceiver
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.IdentityComponentFiber
import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.OpenGenericIso
import ZInQKernel.Contrib.OneProof.SemistableNeronBaseChangeNoSGA3

/-!
# Construct the marked semiabelian identity component of the given model

A single nonempty open on which the original model has geometrically connected
fibers suffices. Stacks, Lemma 37.28.4 (Tag 055G), gives such an open from a
geometrically connected generic fiber for a finite-type morphism over an
irreducible base. The output below is the fiberwise identity component globally,
not just the restriction of the model to that good open.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj NumberField

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue ZInQ.HeightFix ZInQ.SemistabAssembly
open DictModels.RaynaudOr (HasSemiAbelianIdCompTorus)
open CToPrinted (idCompSet idCompSet_one idCompGenericFibre)

/-- Given the connected-fiber open of the original model, build its global open
identity component with its actual inclusion, the compatible generic marking,
and connected semiabelian fibers over the original residue fields. -/
theorem exists_markedSemiabelianComponent_of_goodOpen {K L : Type} [Field K] [Field L]
    [NumberField L] [Algebra K L] {A : PkgI3.AbVar K} (N : GroupModel A L)
    (hs : IsSemistableResPrinted N) (V : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (hne : (V : Set (Spec (CommRingCat.of (𝓞 L)))).Nonempty)
    (hConn : GeometricallyConnected (N.G.hom ∣_ V)) :
    ∃ (G : GroupModel A L) (j : G.G ⟶ N.G),
      IsOpenImmersion j.left ∧ IsMonHom j ∧ Set.range j.left = idCompSet N.G ∧
      IsIso ((Over.pullback (jL L)).map j) ∧
      (Over.pullback (jL L)).map j ≫ N.gen.hom = G.gen.hom ∧
      ∀ (p : Ideal (𝓞 L)) [p.IsMaximal],
        ConnectedSpace (resFibre G p).left ∧ HasSemiAbelianIdCompTorus (resFibre G p) := by
  have hOpen : IsOpen (idCompSet N.G) :=
    isOpen_idCompSet_of_preconnected_on_open N.G (V : Set (Spec (CommRingCat.of (𝓞 L)))) V.2 hne
      (fun s hs' => preconnected_fiber_on_open N.G.hom V s hs')
  let W : N.G.left.Opens := ⟨idCompSet N.G, hOpen⟩
  have hg := SGA3Nbhd.idCompSubgroup_proof geomConnOfRationalPoint_proof _ N.G
  have hW : CToPrinted.OpenSub.IsSubgroupOpen N.G W :=
    { one := idCompSet_one N.G, mul := hg.1, inv := hg.2 }
  have hgen := idCompGenericFibre K A L N
  obtain ⟨U, j, hjOpen, hjMon, hjRange⟩ := SGA3Nbhd.openSubgroupModel_at N W hW hgen
  have hRange : Set.range j.left = idCompSet N.G := hjRange
  have hjIso : IsIso ((Over.pullback (jL L)).map j) :=
    generic_isIso_of_openImmersion_of_generic_points U N j
      (fun x hx => hRange.symm ▸ hgen x hx)
  let e := asIso ((Over.pullback (jL L)).map j)
  let G : GroupModel A L :=
    { G := U.G
      gen := e ≪≫ N.gen
      gen_hom := by
        let : GrpObj (genericFibre L U.G) := Functor.grpObjObj
        let : GrpObj (genericFibre L N.G) := Functor.grpObjObj
        let : GrpObj ((Over.pullback (jL L)).obj U.G) := Functor.grpObjObj
        let : GrpObj ((Over.pullback (jL L)).obj N.G) := Functor.grpObjObj
        have hjGeneric : IsMonHom ((Over.pullback (jL L)).map j) := inferInstance
        exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hjGeneric N.gen_hom }
  refine ⟨G, j, hjOpen, hjMon, hRange, hjIso, rfl, ?_⟩
  intro p hp
  exact @semiabelian_resFibres_of_component_range K L _ _ _ _ A G N j hjOpen hjMon hOpen hRange hs p hp

#print axioms exists_markedSemiabelianComponent_of_goodOpen

end ZInQ.Contrib.IsogenyDegree
