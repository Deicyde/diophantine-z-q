import ZInQKernel.Contrib.OneProof.FaltingsDict

/-! The print-form conclusion of Faltings' extension lemma over a DVR. -/

noncomputable section

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open ReductSplit ZInQ.HeightSplit
set_option linter.style.haveILetI false

/-- Faltings, Invent. Math. 73 (1983), p. 350, Lemma 1: the morphism
“läßt sich eindeutig auf ganz S fortsetzen”. Here the normal base is
`S = Spec O`, and the dense open `U` is its generic point. The input
is a homomorphism; the printed conclusion asserts a unique morphism. -/
def FaltingsLemma1DVRPrint : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A B : PkgI3.AbVar K) (G : GroupModelO A O) (H : GroupModelO B O),
    IsSemiabelianModelO G → IsSemiabelianModelO H →
    let F := Over.pullback (jO O)
    letI : GrpObj (F.obj G.G) := Functor.grpObjObj
    letI : GrpObj (F.obj H.G) := Functor.grpObjObj
    ∀ f : F.obj G.G ⟶ F.obj H.G, IsMonHom f →
      ∃! g : G.G ⟶ H.G, F.map g = f

/-- A morphism between these models that is a homomorphism on the generic
fibre already preserves the group structure over the DVR. -/
theorem isMonHom_of_generic
    {K : Type} [Field K] {O : ValuationSubring K} {A B : PkgI3.AbVar K}
    (G : GroupModelO A O) (H : GroupModelO B O) (g : G.G ⟶ H.G) :
    let F := Over.pullback (jO O)
    letI : GrpObj (F.obj G.G) := Functor.grpObjObj
    letI : GrpObj (F.obj H.G) := Functor.grpObjObj
    ∀ f : F.obj G.G ⟶ F.obj H.G, IsMonHom f → F.map g = f → IsMonHom g := by
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  letI : GrpObj (F.obj H.G) := Functor.grpObjObj
  dsimp only
  intro f hf hgf
  haveI : IsSchemeTheoreticallyDominant (jO O) :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _
      (FaithfulSMul.algebraMap_injective O K)
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O)))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (G.G ⊗ G.G).hom :=
    ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  refine ReductGlue.isMonHom_of_ext F f (𝟙 _) hf inferInstance ?_ ?_ g (by simpa using hgf)
  · simpa only [Category.comp_id] using
      ZInQ.Contrib.NeronC.pullback_map_injective (jO O)
        (𝟙_ (Over (Spec (CommRingCat.of O)))) H.G
  · simpa only [Category.comp_id] using
      ZInQ.Contrib.NeronC.pullback_map_injective (jO O) (G.G ⊗ G.G) H.G

/-- The printed extension as a morphism and the original extension as a
homomorphism are equivalent. -/
theorem faltingsLemma1DVR_iff_print : FaltingsLemma1DVR ↔ FaltingsLemma1DVRPrint := by
  constructor
  · intro h K _ O _ A B G H hG hH
    dsimp only
    intro f hf
    obtain ⟨g, ⟨_, hg⟩, hu⟩ := h K O A B G H hG hH f hf
    exact ⟨g, hg, fun y hy => hu y ⟨isMonHom_of_generic G H y f hf hy, hy⟩⟩
  · intro h K _ O _ A B G H hG hH
    dsimp only
    intro f hf
    obtain ⟨g, hg, hu⟩ := h K O A B G H hG hH f hf
    exact ⟨g, ⟨isMonHom_of_generic G H g f hf hg, hg⟩, fun y hy => hu y hy.2⟩

/-- The morphism conclusion of the extension theorem specializes to the
print-form DVR leaf using the pointwise fibre dictionary. -/
theorem faltingsLemma1DVRPrint_of_printed_points
    (extend : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (A B : PkgI3.AbVar K) (G : GroupModelO A O) (H : GroupModelO B O),
      IsIntegrallyClosed O →
      FaltingsSemiabelianDef G → FaltingsSemiabelianDef H →
      ∀ {U : Scheme.{0}} (j : U ⟶ Spec (CommRingCat.of O)), IsOpenImmersion j → DenseRange j →
      let F := Over.pullback j
      letI : GrpObj (F.obj G.G) := Functor.grpObjObj
      letI : GrpObj (F.obj H.G) := Functor.grpObjObj
      ∀ f : F.obj G.G ⟶ F.obj H.G, IsMonHom f →
        ∃! g : G.G ⟶ H.G, F.map g = f) :
    FaltingsLemma1DVRPrint ∧ FaltingsLemma1DVR := by
  suffices h : FaltingsLemma1DVRPrint from ⟨h, faltingsLemma1DVR_iff_print.mpr h⟩
  intro K _ O _ A B G H hG hH
  obtain ⟨hG', hH'⟩ := faltingsLemma1DVR_models G H hG hH
  obtain ⟨hj, hd, _⟩ := jO_genericOpen O
  exact extend K O A B G H inferInstance hG' hH' (jO O) hj hd

end ZInQ.FaltingsRestate
