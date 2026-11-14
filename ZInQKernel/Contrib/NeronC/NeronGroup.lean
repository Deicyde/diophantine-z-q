import ZInQKernel.HDecomp.Faltings.H5Neron
import ZInQKernel.Contrib.NeronC.NeronGroupAbstract
import ZInQKernel.Contrib.NeronC.NMPInjective

/-! # neron-c: leaf T41 reduced to the scheme-level Néron existence theorem

Task neron-c (2026-11-13). Leaf T41 is h5-neron's `ZInQ.H5Neron.NeronModelExists` (kernel,
`ZInQKernel/HDecomp/Faltings/H5Neron.lean`): `A_L` has a Néron model over `𝓞_L` which is a
`GroupModel`, i.e. a smooth, separated, quasi-compact *group* scheme with a *group* isomorphism
`gen : 𝒩_L ≅ A_L`. Bosch–Lütkebohmert–Raynaud's existence theorem produces a Néron model as a
scheme (BLR §1.2 Def. 1 has no group law); the group law and the homomorphy of `gen` follow from
the mapping property (`NeronGroupAbstract.lean`). So T41 follows from `NeronSchemeModelExists`,
which is BLR §1.4 Thm. 3 for `A_L` over the Dedekind ring `𝓞_L`, word for word. -/

namespace ZInQ.Contrib.NeronC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

/-- Smooth `S`-schemes are closed under `⊗` in `Over S`. -/
lemma smooth_tensor {S : Scheme.{0}} (X Y : Over S) (hX : Smooth X.hom) (hY : Smooth Y.hom) :
    Smooth (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

/-- The unit `𝟙_ (Over S)` is smooth over `S`. -/
lemma smooth_tensorUnit (S : Scheme.{0}) : Smooth (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  have : IsOpenImmersion (𝟙 S) := inferInstance
  infer_instance

/-- **`NeronSchemeModelExists` (LEAF; published).** For an abelian variety `A/K` and a number
field `L ⊇ K`, the abelian variety `A_L` has a Néron model over `𝓞_L` in the sense of BLR §1.2
Def. 1: a smooth, separated `𝓞_L`-scheme `N` of finite type (smooth gives locally of finite
presentation; quasi-compact) with an isomorphism `e : N_L ≅ A_L` of `L`-schemes such that every
`L`-morphism `Y_L → A_L` from the generic fibre of a smooth `𝓞_L`-scheme `Y` extends uniquely to an
`𝓞_L`-morphism `Y → N`. No group structure is asked for. Source: Bosch–Lütkebohmert–Raynaud,
*Néron models* (1990), §1.4 Thm. 3 (existence of Néron models of abelian varieties over a Dedekind
base; here the Dedekind domain `𝓞_L` with fraction field `L`), with §1.2 Def. 1. Locators
UNVERIFIED (no network). -/
def NeronSchemeModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ (N : Over (Spec (CommRingCat.of (𝓞 L)))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (e : genericFibre L N ≅ (A.baseChange L).X),
      ∀ (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [Smooth Y.hom],
        Function.Bijective fun f : Y ⟶ N =>
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f ≫ e.hom

/-- **T41 from the scheme-level existence theorem**: the group law of the Néron model and the
homomorphy of `gen` are supplied by `grpObjOfNeron` and `isMonHom_of_neron`. -/
theorem neronModelExists_of_scheme (h : NeronSchemeModelExists) :
    ZInQ.H5Neron.NeronModelExists := by
  intro K _ A L _ _ _
  obtain ⟨N, hS, hSep, hQC, e, hN⟩ := h K A L
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))
  let P : Over (Spec (CommRingCat.of (𝓞 L))) → Prop := fun Y => Smooth Y.hom
  have hP1 : P (𝟙_ _) := smooth_tensorUnit _
  have hP2 : ∀ X Y, P X → P Y → P (X ⊗ Y) := fun X Y hX hY => smooth_tensor X Y hX hY
  have hB : ∀ Y, P Y → Function.Bijective fun f : Y ⟶ N => F.map f ≫ e.hom :=
    fun Y hY => @hN Y hY
  letI : GrpObj N := grpObjOfNeron F P hP1 hP2 N hS _ e hB
  let 𝒩 : GroupModel A L :=
    { G := N
      gen := e
      gen_hom := isMonHom_of_neron F P hP1 hP2 N hS _ e hB }
  exact ⟨𝒩, fun Y _ => hN Y⟩

/-- Conversely, T41 gives the scheme-level statement (so the reduction loses nothing). -/
theorem neronSchemeModelExists_of_neronModelExists (h : ZInQ.H5Neron.NeronModelExists) :
    NeronSchemeModelExists := by
  intro K _ A L _ _ _
  obtain ⟨𝒩, h𝒩⟩ := h K A L
  exact ⟨𝒩.G, inferInstance, inferInstance, inferInstance, 𝒩.gen, fun Y _ => h𝒩 Y⟩

/-- **`NeronSchemeExtensionExists` (LEAF; published, strictly weaker than
`NeronSchemeModelExists`).** As `NeronSchemeModelExists`, but only the *existence* of the extension
`Y → N` of an `L`-morphism `Y_L → A_L` is asked for; its uniqueness is automatic
(`pullback_map_injective`: `Y` is flat over `𝓞_L`, `Spec L → Spec 𝓞_L` is scheme-theoretically
dominant and `N` is separated). Source: as for `NeronSchemeModelExists` (BLR §1.4 Thm. 3 with §1.2
Def. 1; locators UNVERIFIED). -/
def NeronSchemeExtensionExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ (N : Over (Spec (CommRingCat.of (𝓞 L)))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (e : genericFibre L N ≅ (A.baseChange L).X),
      ∀ (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N =>
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f ≫ e.hom

/-- Uniqueness of extensions into a separated model, for smooth test schemes over `𝓞_L`. -/
theorem neron_extension_injective (L : Type) [Field L] [NumberField L]
    (N : Over (Spec (CommRingCat.of (𝓞 L)))) [IsSeparated N.hom] {B : Over (Spec (CommRingCat.of L))}
    (e : genericFibre L N ≅ B) (Y : Over (Spec (CommRingCat.of (𝓞 L)))) [Smooth Y.hom] :
    Function.Injective fun f : Y ⟶ N =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).map f ≫ e.hom := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))) :=
    isSchemeTheoreticallyDominant_spec_map _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)
  intro f g hfg
  apply pullback_map_injective (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))) Y N
  exact (cancel_mono e.hom).mp hfg

/-- `NeronSchemeModelExists` from the existence half alone. -/
theorem neronSchemeModelExists_of_extension (h : NeronSchemeExtensionExists) :
    NeronSchemeModelExists := by
  intro K _ A L _ _ _
  obtain ⟨N, hS, hSep, hQC, e, hN⟩ := h K A L
  exact ⟨N, hS, hSep, hQC, e, fun Y _ => ⟨neron_extension_injective L N e Y, hN Y⟩⟩

/-- **T41 from the existence half of the scheme-level Néron theorem.** -/
theorem neronModelExists_of_extension (h : NeronSchemeExtensionExists) :
    ZInQ.H5Neron.NeronModelExists :=
  neronModelExists_of_scheme (neronSchemeModelExists_of_extension h)

/-- Conversely, T41 gives `NeronSchemeExtensionExists` (so the reduction loses nothing). -/
theorem neronSchemeExtensionExists_of_neronModelExists (h : ZInQ.H5Neron.NeronModelExists) :
    NeronSchemeExtensionExists := by
  intro K _ A L _ _ _
  obtain ⟨N, hS, hSep, hQC, e, hN⟩ := neronSchemeModelExists_of_neronModelExists h K A L
  exact ⟨N, hS, hSep, hQC, e, fun Y _ => (hN Y).2⟩

end ZInQ.Contrib.NeronC

#print axioms ZInQ.Contrib.NeronC.grpObjOfNeron
#print axioms ZInQ.Contrib.NeronC.isMonHom_of_neron
#print axioms ZInQ.Contrib.NeronC.neronModelExists_of_scheme
#print axioms ZInQ.Contrib.NeronC.neronSchemeModelExists_of_neronModelExists
#print axioms ZInQ.Contrib.NeronC.neron_extension_injective
#print axioms ZInQ.Contrib.NeronC.neronModelExists_of_extension
#print axioms ZInQ.Contrib.NeronC.neronSchemeExtensionExists_of_neronModelExists
