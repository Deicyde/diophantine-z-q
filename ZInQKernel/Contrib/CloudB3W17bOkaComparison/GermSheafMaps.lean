import ZInQKernel.Contrib.CloudB3W17bOka.Oka.ComplexSpace

/-!
# Genuine Oka germ and sheaf maps from locally analytic coordinate maps

This is a small direct interface to Oka's actual holomorphic structure sheaf,
not a map of sets labelled analytic.  Evaluation is descended through the real
stalk colimit.  Precomposition gives a natural transformation on every open,
and the stalk maps are proved local by evaluation/unit reflection.

The precomposition construction follows Oka/AnalyticSpace/HolomorphicMapOpen
at chrisflav/oka 9a9fc315498d58484ac1abc9668548212eb7c1ff, with input stated as
a locally analytic coordinate map instead of an already bundled tuple.  Credit
for that construction: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten;
Apache-2.0, as recorded in LICENSE.  No GAGA or algebraic-morphism premise is used.
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The compatible evaluation cocone on the real neighbourhood diagram. -/
def okaEvalCocone (x : ι → ℂ) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of (ι → ℂ)) x).op ⋙ okaCommPresheaf ι) where
  pt := CommRingCat.of ℂ
  ι :=
    { app := fun U => CommRingCat.ofHom (OkaRing.evalHom U.unop.2)
      naturality := fun _ _ _ => by ext f; rfl }

/-- Evaluation on the actual Oka stalk, by the universal property of its stalk colimit. -/
def okaGermEvalC (x : ι → ℂ) : (okaCommPresheaf ι).stalk x ⟶ CommRingCat.of ℂ := by
  change colimit ((OpenNhds.inclusion (X := TopCat.of (ι → ℂ)) x).op ⋙ okaCommPresheaf ι) ⟶ _
  exact colimit.desc _ (okaEvalCocone x)

/-- Evaluation of a germ is evaluation of its representative, with no choice of a lift. -/
theorem okaGermEvalC_germ (x : ι → ℂ) (U : Opens (ι → ℂ)) (hx : x ∈ U) (f : OkaRing U) :
    (okaGermEvalC x).hom ((okaCommPresheaf ι).germ U x hx f) = OkaRing.evalHom hx f := by
  change (((okaCommPresheaf ι).germ U x hx ≫ okaGermEvalC x).hom) f = _
  exact ConcreteCategory.congr_hom (colimit.ι_desc (okaEvalCocone x) (op ⟨U, hx⟩)) f

/-- A genuine holomorphic germ is a unit exactly when its value is nonzero. -/
theorem isUnit_okaGerm_iff_eval_ne_zero (x : ι → ℂ) (U : Opens (ι → ℂ))
    (hx : x ∈ U) (f : OkaRing U) :
    IsUnit ((okaCommPresheaf ι).germ U x hx f) ↔ OkaRing.evalHom hx f ≠ 0 := by
  constructor
  · intro h
    have he := h.map (okaGermEvalC x).hom
    rw [okaGermEvalC_germ] at he
    exact isUnit_iff_ne_zero.mp he
  · exact isUnit_okaGerm hx f

variable (U : Opens (complexSpace ι)) (f : (ι → ℂ) → (κ → ℂ))
variable (hf : ∀ x ∈ U, AnalyticAt ℂ f x)

/-- The continuous map on the genuine open Oka source underlying precomposition. -/
def localCoordinateBase :
    ((complexSpace ι).restrict U.isOpenEmbedding).toTopCat ⟶ (complexSpace κ).toTopCat :=
  TopCat.ofHom ⟨fun x => f x.1,
    continuousOn_iff_continuous_restrict.mp (fun x hx => (hf x hx).continuousAt.continuousWithinAt)⟩

/-- The source open on which a target section is pulled back. -/
def localCoordinateSource (W : Opens (κ → ℂ)) : Opens (ι → ℂ) :=
  U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map (localCoordinateBase U f hf)).obj W)

/-- Membership in a pullback source means both source membership and the genuine target condition. -/
theorem localCoordinateSource_mem {W : Opens (κ → ℂ)} {x : ι → ℂ}
    (hx : x ∈ localCoordinateSource U f hf W) : x ∈ U ∧ f x ∈ W := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y.2, hy⟩

/-- Actual precomposition on all holomorphic sections over all target opens. -/
def localCoordinateC (W : Opens (κ → ℂ)) :
    OkaRing W →+* ((complexSpace ι).restrict U.isOpenEmbedding).presheaf.obj
      (op ((Opens.map (localCoordinateBase U f hf)).obj W)) where
  toFun s := OkaRing.mk
    (fun x => s.toFun W ⟨f x.1, (localCoordinateSource_mem U f hf x.2).2⟩)
    (s.2.comp_analyticOn f
      (fun x hx => hf x (localCoordinateSource_mem U f hf hx).1)
      (fun _ hx => (localCoordinateSource_mem U f hf hx).2))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Precomposition preserves the actual value, not merely the zero set. -/
theorem localCoordinateC_eval (W : Opens (κ → ℂ)) (s : OkaRing W)
    {x : ι → ℂ} (hx : x ∈ localCoordinateSource U f hf W) :
    OkaRing.evalHom hx (localCoordinateC U f hf W s) =
      OkaRing.evalHom (localCoordinateSource_mem U f hf hx).2 s := rfl

/-- The actual presheafed-space morphism, including naturality of the section maps. -/
def localCoordinatePre :
    ((complexSpace ι).restrict U.isOpenEmbedding).toPresheafedSpace.Hom
      (complexSpace κ).toPresheafedSpace where
  base := localCoordinateBase U f hf
  c :=
    { app := fun W => CommRingCat.ofHom (localCoordinateC U f hf W.unop)
      naturality := fun _ _ _ => rfl }

/-- The precomposition stalk maps really are local ring homomorphisms. -/
theorem isLocalHom_localCoordinatePre (x : (complexSpace ι).restrict U.isOpenEmbedding) :
    IsLocalHom ((localCoordinatePre U f hf).stalkMap x).hom := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨W, hw, s, rfl⟩ := (okaCommPresheaf κ).exists_germ_eq a
  have hx : x ∈ (Opens.map (localCoordinateBase U f hf)).obj W := hw
  have hmap := PresheafedSpace.stalkMap_germ_apply (localCoordinatePre U f hf) W x hw s
  have hap := (congrArg IsUnit hmap).mp ha
  have hiso := (complexSpace ι).restrictStalkIso_hom_eq_germ_apply U.isOpenEmbedding
    ((Opens.map (localCoordinateBase U f hf)).obj W) x hx (localCoordinateC U f hf W s)
  have hau := hiso ▸ hap.map ((complexSpace ι).restrictStalkIso U.isOpenEmbedding x).hom.hom
  have hsource : x.1 ∈ localCoordinateSource U f hf W := ⟨x, hx, rfl⟩
  have hne := (isUnit_okaGerm_iff_eval_ne_zero x.1
    (localCoordinateSource U f hf W) hsource (localCoordinateC U f hf W s)).mp hau
  have htarget : OkaRing.evalHom hw s ≠ 0 := by
    simpa only [localCoordinateC_eval] using hne
  exact isUnit_okaGerm hw s htarget

/-- The resulting morphism of Oka's actual locally ringed spaces. -/
def localCoordinateLRS : (complexSpace ι).restrict U.isOpenEmbedding ⟶ complexSpace κ :=
  ⟨localCoordinatePre U f hf, isLocalHom_localCoordinatePre U f hf⟩

@[simp]
theorem localCoordinateLRS_base (x : U) : (localCoordinateLRS U f hf).base x = f x.1 := rfl

/-- The actual sheaf map pulls a constant section back to the same constant section. -/
theorem localCoordinateLRS_const (c : ℂ) :
    (LocallyRingedSpace.Γ.map (localCoordinateLRS U f hf).op).hom
      (algebraMap ℂ (OkaRing (⊤ : Opens (κ → ℂ))) c) =
        algebraMap ℂ (OkaRing (U.isOpenEmbedding.isOpenMap.functor.obj ⊤)) c := rfl

end ZInQ.Contrib.CloudB3W17bOkaComparison
