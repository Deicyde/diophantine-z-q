import ZInQKernel.Contrib.OneProof.T10Proetale.Tower
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Discrete coefficients on the big étale site

Continuous functions to a discrete abelian group compute the sections of the
sheafification of the constant presheaf, just as on the small pro-étale site.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

private abbrev J : GrothendieckTopology Scheme.{0} := Scheme.etaleTopology

variable (B : Type) [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

/-- Continuous functions with values in the coefficient group, as a big étale
abelian sheaf with the universe lift used for derived evaluation. -/
def etaleContinuousCoefficients : Sheaf J Ab.{1} :=
  (sheafCompose J AddCommGrpCat.uliftFunctor.{1}).obj
    ⟨continuousMapPresheafAb B,
      .of_le (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology)
        (isSheaf_fpqcTopology_continuousMapPresheafAb B)⟩

private abbrev constValue := AddCommGrpCat.uliftFunctor.{1}.obj (AddCommGrpCat.of B)

set_option backward.isDefEq.respectTransparency false in
private def constantSection :
    (Functor.const Scheme.{0}ᵒᵖ).obj (constValue B) ⟶ (etaleContinuousCoefficients B).obj where
  app U := AddCommGrpCat.ofHom
    { toFun := fun b => ULift.up (ContinuousMap.const U.unop b.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := by
    ext b
    rfl

private theorem etale_openCover {U : Scheme.{0}} {I : Type} (O : I → U.Opens)
    (h : ∀ u : U, ∃ i, u ∈ O i) : Sieve.ofArrows _ (fun i => (O i).ι) ∈ J U := by
  apply Precoverage.generate_mem_toGrothendieck
  apply (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
  exact ⟨fun u => let ⟨i, hi⟩ := h u; ⟨i, ⟨u, hi⟩, rfl⟩,
    fun i => inferInstanceAs (Etale (O i).ι)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem constantSection_locallyInjective :
    Presheaf.IsLocallyInjective J (constantSection B) where
  equalizerSieve_mem {X} b c h := by
    by_cases hX : Nonempty X.unop
    · obtain ⟨u⟩ := hX
      have eq : b = c := ULift.ext (congrArg (fun f : ULift.{1} C(X.unop, B) => f.down u) h)
      rw [eq, Presheaf.equalizerSieve_self_eq_top]
      exact J.top_mem _
    · let O (_ : Empty) : X.unop.Opens := ⊥
      refine J.superset_covering ?_ (etale_openCover O (fun u => (hX ⟨u⟩).elim))
      rw [Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

variable [DiscreteTopology B]

set_option backward.isDefEq.respectTransparency false in
private theorem constantSection_locallySurjective :
    Presheaf.IsLocallySurjective J (constantSection B) where
  imageSieve_mem {U} a := by
    let v : C(U, B) := a.down
    let O (b : B) : U.Opens :=
      ⟨(v : U → B) ⁻¹' {b}, (isOpen_discrete ({b} : Set B)).preimage v.continuous⟩
    have hc : Sieve.ofArrows _ (fun b => (O b).ι) ∈ J U :=
      etale_openCover O (fun u => ⟨v u, rfl⟩)
    refine J.superset_covering ?_ hc
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨b⟩
    refine ⟨ULift.up b, ULift.ext (ContinuousMap.ext (fun u => ?_))⟩
    exact u.2.symm

set_option backward.isDefEq.respectTransparency false in
/-- The big étale constant sheaf used for finite H¹ is the sheaf of continuous
maps to the discrete coefficient group, via the constant sections. -/
def etaleDiscreteCoefficientsIso :
    (constantSheaf J Ab.{1}).obj (constValue B) ≅ etaleContinuousCoefficients B := by
  let f := constantSection B
  have hJ : J.W f := (J.W_iff_isLocallyBijective f).mpr
    ⟨constantSection_locallyInjective B, constantSection_locallySurjective B⟩
  have h : IsIso ((presheafToSheaf J Ab.{1}).map f) := (J.W_iff f).mp hJ
  exact asIso ((presheafToSheaf J Ab.{1}).map f) ≪≫
    asIso ((sheafificationAdjunction J Ab.{1}).counit.app (etaleContinuousCoefficients B))

set_option backward.isDefEq.respectTransparency false in
/-- The big étale constant sheaf restricts to the actual continuous coefficient
presheaf on the small pro-étale site. -/
def etaleDiscreteCoefficientsRestrictionIso (X : Scheme.{0}) :
    (T10Etale.piX X).op ⋙ ((constantSheaf J Ab.{1}).obj (constValue B)).obj ≅
      (continuousCoefficients X B).obj :=
  Functor.isoWhiskerLeft (T10Etale.piX X).op
    ((sheafToPresheaf J Ab.{1}).mapIso (etaleDiscreteCoefficientsIso B))

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition with a continuous additive homomorphism on the big étale site. -/
def mapEtaleContinuousCoefficients {B D : Type} [TopologicalSpace B] [TopologicalSpace D]
    [AddCommGroup B] [AddCommGroup D] [IsTopologicalAddGroup B] [IsTopologicalAddGroup D]
    (f : B →+ D) (hf : Continuous f) :
    etaleContinuousCoefficients B ⟶ etaleContinuousCoefficients D :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun b => ULift.up ((⟨f, hf⟩ : C(B, D)).comp b.down)
          map_zero' := ULift.ext (ContinuousMap.ext (fun _ => f.map_zero))
          map_add' b c := by
            let b' : C(U.unop, B) := b.down
            let c' : C(U.unop, B) := c.down
            exact ULift.ext (ContinuousMap.ext (fun x => f.map_add (b' x) (c' x))) }
      naturality _ _ _ := by ext b; rfl }

set_option backward.isDefEq.respectTransparency false in
/-- The canonical identification of discrete coefficients commutes with
all additive coefficient maps, including residue reductions and scalars. -/
theorem etaleDiscreteCoefficientsIso_naturality
    {B D : Type} [TopologicalSpace B] [TopologicalSpace D]
    [AddCommGroup B] [AddCommGroup D] [IsTopologicalAddGroup B] [IsTopologicalAddGroup D]
    [DiscreteTopology B] [DiscreteTopology D] (f : B →+ D) :
    (constantSheaf J Ab.{1}).map (AddCommGrpCat.uliftFunctor.{1}.map (AddCommGrpCat.ofHom f)) ≫
      (etaleDiscreteCoefficientsIso D).hom =
    (etaleDiscreteCoefficientsIso B).hom ≫ mapEtaleContinuousCoefficients f continuous_of_discreteTopology := by
  let H := presheafToSheaf J Ab.{1}
  let η := (sheafificationAdjunction J Ab.{1}).counit
  let t := mapEtaleContinuousCoefficients f continuous_of_discreteTopology
  let g := (Functor.const Scheme.{0}ᵒᵖ).map
    (AddCommGrpCat.uliftFunctor.{1}.map (AddCommGrpCat.ofHom f))
  have hh : g ≫ constantSection D = constantSection B ≫ t.hom := by
    ext U a
    rfl
  change H.map g ≫ (H.map (constantSection D) ≫ η.app (etaleContinuousCoefficients D)) =
    (H.map (constantSection B) ≫ η.app (etaleContinuousCoefficients B)) ≫ t
  have hn := η.naturality t
  change H.map t.hom ≫ η.app (etaleContinuousCoefficients D) =
    η.app (etaleContinuousCoefficients B) ≫ t at hn
  rw [Category.assoc, ← hn]
  change H.map g ≫ (H.map (constantSection D) ≫ η.app (etaleContinuousCoefficients D)) =
    H.map (constantSection B) ≫ (H.map t.hom ≫ η.app (etaleContinuousCoefficients D))
  simp only [← Category.assoc, ← Functor.map_comp, hh]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the coefficient comparison intertwines the original small
site's continuous coefficient maps and the big site constant coefficient maps. -/
theorem etaleDiscreteCoefficientsRestrictionIso_naturality (X : Scheme.{0})
    {B D : Type} [TopologicalSpace B] [TopologicalSpace D]
    [AddCommGroup B] [AddCommGroup D] [IsTopologicalAddGroup B] [IsTopologicalAddGroup D]
    [DiscreteTopology B] [DiscreteTopology D] (f : B →+ D) :
    Functor.whiskerLeft (T10Etale.piX X).op
      (((constantSheaf J Ab.{1}).map
        (AddCommGrpCat.uliftFunctor.{1}.map (AddCommGrpCat.ofHom f))).hom) ≫
      (etaleDiscreteCoefficientsRestrictionIso D X).hom =
    (etaleDiscreteCoefficientsRestrictionIso B X).hom ≫
      (mapContinuousCoefficients X f continuous_of_discreteTopology).hom := by
  let R := (sheafToPresheaf J Ab.{1}) ⋙
    (Functor.whiskeringLeft _ _ _).obj (T10Etale.piX X).op
  have h := congrArg R.map (etaleDiscreteCoefficientsIso_naturality f)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

end
end ZInQ.Manuscript.T10Proetale
