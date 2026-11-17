import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.ModelFacePairH01
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FiberBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.BasicOpen
import ZInQKernel.Contrib.CloudR2Poincare.L2.ConeRanks
import ZInQKernel.Contrib.CloudR2Poincare.L2.TildeConeFiniteFree
import ZInQKernel.Contrib.CloudR2Poincare.L4.CubeFaces.Family

/-!
# Actual cube-family retained-model cone integration

This is a source-only continuation. The existing retained comparison maps,
all-scalar quasi-isomorphisms and face homotopies are kept, not replaced by
models selected from ranks. The internal quantitative step combines the
original mapping-cone rank suppliers with the actual scalar/tilde fibre
comparison and the existing sheaf-cone semicontinuity theorem.

The geometric public endpoint `exists_open_cubeFibreHZero_ge_one` is declared
below with a complete SOURCE proof body. It consumes L1's produced native-H01
models, the actual residue cube-product/face diagrams, genuine localization
and affine-chart point lifts, and original residue-field cohomology transport.
Private rank/injection subgoals are derived from the actual Picard
trivializations; none is added to the public telescope. No residue-map
flatness or nonnegative cone is used. This is not a native proof certificate.

No compiler, native-kernel, raw-expression ABI or default-budget grade is
claimed by this source. There are no numerical proof-budget overrides.
-/

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry HomologicalComplex

namespace ZInQ.Contrib.CloudR2Poincare.L2.CubeConeFibreIntegration

namespace ResidueCartesian

/-- The actual map changing only the parameter of a native pullback. -/
def familyMap {B U Z W : Scheme.{u}} (p : U ⟶ B) (a : Z ⟶ B) (b : W ⟶ Z) :
    pullback p (b ≫ a) ⟶ pullback p a :=
  pullback.map p (b ≫ a) p a (𝟙 U) b (𝟙 B) (by simp) (by simp)

private theorem familyMap_fst {B U Z W : Scheme.{u}}
    (p : U ⟶ B) (a : Z ⟶ B) (b : W ⟶ Z) :
    familyMap p a b ≫ pullback.fst p a = pullback.fst p (b ≫ a) := by
  simp only [familyMap, pullback.map, pullback.lift_fst, Category.comp_id]

private theorem familyMap_snd {B U Z W : Scheme.{u}}
    (p : U ⟶ B) (a : Z ⟶ B) (b : W ⟶ Z) :
    familyMap p a b ≫ pullback.snd p a = pullback.snd p (b ≫ a) ≫ b := by
  unfold familyMap
  exact pullback.lift_snd _ _ _

/-- Cancellation of the original pullback square gives the actual parameter
Cartesian square. There is no flatness condition on b. -/
theorem familyMap_isPullback {B U Z W : Scheme.{u}}
    (p : U ⟶ B) (a : Z ⟶ B) (b : W ⟶ Z) :
    IsPullback (familyMap p a b) (pullback.snd p (b ≫ a)) (pullback.snd p a) b := by
  have efst : familyMap p a b ≫ pullback.fst p a = pullback.fst p (b ≫ a) := by
    simp only [familyMap, pullback.map, pullback.lift_fst, Category.comp_id]
  have esnd : familyMap p a b ≫ pullback.snd p a = pullback.snd p (b ≫ a) ≫ b := by
    simp only [familyMap, pullback.map, pullback.lift_snd]
  have outer : IsPullback (pullback.snd p (b ≫ a))
      (familyMap p a b ≫ pullback.fst p a) (b ≫ a) p :=
    efst.symm ▸ (IsPullback.of_hasPullback p (b ≫ a)).flip
  exact (outer.of_bot esnd.symm (IsPullback.of_hasPullback p a).flip).flip

variable {k κ : Type u} [Field k] [Field κ] {X Y Z : Scheme.{u}}

/-- The canonical projection of the field-changed product to its X-factor. -/
def fieldFst (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    pullback (pullback.fst f g ≫ f) α ⟶ pullback f α :=
  pullback.lift (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.fst f g)
    (pullback.snd (pullback.fst f g ≫ f) α)
    ((Category.assoc _ _ _).trans (pullback.condition (f := pullback.fst f g ≫ f) (g := α)))

/-- The canonical projection of the same field-changed product to Y. -/
def fieldSnd (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    pullback (pullback.fst f g ≫ f) α ⟶ pullback g α :=
  pullback.lift (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.snd f g)
    (pullback.snd (pullback.fst f g ≫ f) α) (by
      calc
        (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.snd f g) ≫ g =
            pullback.fst (pullback.fst f g ≫ f) α ≫ (pullback.snd f g ≫ g) := Category.assoc _ _ _
        _ = pullback.fst (pullback.fst f g ≫ f) α ≫ (pullback.fst f g ≫ f) :=
          congrArg (fun h => pullback.fst (pullback.fst f g ≫ f) α ≫ h)
            (pullback.condition (f := f) (g := g)).symm
        _ = pullback.snd (pullback.fst f g ≫ f) α ≫ α :=
          pullback.condition (f := pullback.fst f g ≫ f) (g := α))

private theorem fieldFst_fst (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    fieldFst f g α ≫ pullback.fst f α =
      pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.fst f g := by
  unfold fieldFst
  exact pullback.lift_fst _ _ _

private theorem fieldFst_snd (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    fieldFst f g α ≫ pullback.snd f α = pullback.snd (pullback.fst f g ≫ f) α := by
  unfold fieldFst
  exact pullback.lift_snd _ _ _

private theorem fieldSnd_fst (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    fieldSnd f g α ≫ pullback.fst g α =
      pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.snd f g := by
  unfold fieldSnd
  exact pullback.lift_fst _ _ _

private theorem fieldSnd_snd (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    fieldSnd f g α ≫ pullback.snd g α = pullback.snd (pullback.fst f g ≫ f) α := by
  unfold fieldSnd
  exact pullback.lift_snd _ _ _

/-- The actual field-changed product is Cartesian over the actual field.
This is the universal pullback comparison, not a numerical object iso. -/
theorem fieldProduct_isPullback
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    IsPullback (fieldFst f g α) (fieldSnd f g α) (pullback.snd f α) (pullback.snd g α) := by
  have hfst : fieldFst f g α ≫ pullback.fst f α =
      pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.fst f g := by
    unfold fieldFst
    exact pullback.lift_fst _ _ _
  have hsnd : fieldFst f g α ≫ pullback.snd f α =
      pullback.snd (pullback.fst f g ≫ f) α := by
    unfold fieldFst
    exact pullback.lift_snd _ _ _
  have source : IsPullback (pullback.fst (pullback.fst f g ≫ f) α)
      (fieldFst f g α ≫ pullback.snd f α) (pullback.fst f g ≫ f) α :=
    hsnd.symm ▸ IsPullback.of_hasPullback (pullback.fst f g ≫ f) α
  have hx : IsPullback (pullback.fst (pullback.fst f g ≫ f) α)
      (fieldFst f g α) (pullback.fst f g) (pullback.fst f α) :=
    source.of_bot hfst.symm (IsPullback.of_hasPullback f α)
  have outer := hx.paste_horiz (IsPullback.of_hasPullback f g).flip
  have outer' : IsPullback
      (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.snd f g)
      (fieldFst f g α) g (pullback.snd f α ≫ α) :=
    (pullback.condition (f := f) (g := α)) ▸ outer
  have yfst : fieldSnd f g α ≫ pullback.fst g α =
      pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.snd f g := by
    unfold fieldSnd
    exact pullback.lift_fst _ _ _
  have ysnd : fieldSnd f g α ≫ pullback.snd g α =
      pullback.snd (pullback.fst f g ≫ f) α := by
    unfold fieldSnd
    exact pullback.lift_snd _ _ _
  have source' : IsPullback (fieldFst f g α) (fieldSnd f g α ≫ pullback.fst g α)
      (pullback.snd f α ≫ α) g := yfst.symm ▸ outer'.flip
  exact source'.of_bot (hsnd.trans ysnd.symm) (IsPullback.of_hasPullback g α).flip

/-- The native field-product isomorphism fixed by the actual projections. -/
def fieldProductIso (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    pullback (pullback.fst f g ≫ f) α ≅ pullback (pullback.snd f α) (pullback.snd g α) :=
  (fieldProduct_isPullback f g α).isoPullback

@[reassoc] theorem fieldProductIso_hom_fst
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    (fieldProductIso f g α).hom ≫ pullback.fst (pullback.snd f α) (pullback.snd g α) =
      fieldFst f g α := (fieldProduct_isPullback f g α).isoPullback_hom_fst

@[reassoc] theorem fieldProductIso_hom_snd
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    (fieldProductIso f g α).hom ≫ pullback.snd (pullback.snd f α) (pullback.snd g α) =
      fieldSnd f g α := (fieldProduct_isPullback f g α).isoPullback_hom_snd

/-- The actual rational point is changed along the actual field parameter. -/
def point (f : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (α : Spec (.of κ) ⟶ Spec (.of k)) : Spec (.of κ) ⟶ pullback f α :=
  pullback.lift (α ≫ x) (𝟙 _) (by simp [Category.assoc, hx])

@[reassoc] theorem point_struct
    (f : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (α : Spec (.of κ) ⟶ Spec (.of k)) : point f x hx α ≫ pullback.snd f α = 𝟙 _ := by
  simp [point]

/-- The existing X-face commutes with the actual change of parameter.
The first-projection square is L4's original CubeFaces pullback square. -/
theorem faceX_family_square
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) {W : Scheme.{u}} (b : W ⟶ Z)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫ familyMap (pullback.fst f g ≫ f) a b =
      familyMap f a b ≫ L6.nativeCubeFaceXR f g a y hy := by
  have hs := L4.CubeFaces.nativeCubeFaceXR_isPullback f g (b ≫ a) y hy
  have ht := L4.CubeFaces.nativeCubeFaceXR_isPullback f g a y hy
  apply pullback.hom_ext
  · calc
      (L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫ familyMap (pullback.fst f g ≫ f) a b) ≫
          pullback.fst (pullback.fst f g ≫ f) a =
        L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫ pullback.fst (pullback.fst f g ≫ f) (b ≫ a) := by
          simp [familyMap, Category.assoc]
      _ = pullback.fst f (b ≫ a) ≫ L6.nativeCubeFaceXBase f g y hy := hs.w.symm
      _ = (familyMap f a b ≫ L6.nativeCubeFaceXR f g a y hy) ≫
          pullback.fst (pullback.fst f g ≫ f) a := by
          rw [Category.assoc, ← ht.w]
          simp [familyMap, Category.assoc]
  · calc
      (L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫ familyMap (pullback.fst f g ≫ f) a b) ≫
          pullback.snd (pullback.fst f g ≫ f) a =
        L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫
          (familyMap (pullback.fst f g ≫ f) a b ≫ pullback.snd (pullback.fst f g ≫ f) a) :=
        Category.assoc _ _ _
      _ = L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫
          (pullback.snd (pullback.fst f g ≫ f) (b ≫ a) ≫ b) :=
        congrArg (fun h => L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫ h)
          (familyMap_snd (pullback.fst f g ≫ f) a b)
      _ = (L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫
          pullback.snd (pullback.fst f g ≫ f) (b ≫ a)) ≫ b := (Category.assoc _ _ _).symm
      _ = pullback.snd f (b ≫ a) ≫ b :=
        congrArg (fun h => h ≫ b) (L4.CubeFaces.nativeCubeFaceXR_structure f g (b ≫ a) y hy)
      _ = familyMap f a b ≫ pullback.snd f a := (familyMap_snd f a b).symm
      _ = familyMap f a b ≫ (L6.nativeCubeFaceXR f g a y hy ≫
          pullback.snd (pullback.fst f g ≫ f) a) :=
        congrArg (fun h => familyMap f a b ≫ h)
          (L4.CubeFaces.nativeCubeFaceXR_structure f g a y hy).symm
      _ = (familyMap f a b ≫ L6.nativeCubeFaceXR f g a y hy) ≫
          pullback.snd (pullback.fst f g ≫ f) a := (Category.assoc _ _ _).symm

/-- The existing Y-face has the same actual parameter square. -/
theorem faceY_family_square
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) {W : Scheme.{u}} (b : W ⟶ Z)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫ familyMap (pullback.fst f g ≫ f) a b =
      familyMap g a b ≫ L6.nativeCubeFaceYR f g a x hx := by
  have hs := L4.CubeFaces.nativeCubeFaceYR_isPullback f g (b ≫ a) x hx
  have ht := L4.CubeFaces.nativeCubeFaceYR_isPullback f g a x hx
  apply pullback.hom_ext
  · calc
      (L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫ familyMap (pullback.fst f g ≫ f) a b) ≫
          pullback.fst (pullback.fst f g ≫ f) a =
        L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫ pullback.fst (pullback.fst f g ≫ f) (b ≫ a) := by
          simp [familyMap, Category.assoc]
      _ = pullback.fst g (b ≫ a) ≫ L6.nativeCubeFaceYBase f g x hx := hs.w.symm
      _ = (familyMap g a b ≫ L6.nativeCubeFaceYR f g a x hx) ≫
          pullback.fst (pullback.fst f g ≫ f) a := by
          rw [Category.assoc, ← ht.w]
          simp [familyMap, Category.assoc]
  · calc
      (L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫ familyMap (pullback.fst f g ≫ f) a b) ≫
          pullback.snd (pullback.fst f g ≫ f) a =
        L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫
          (familyMap (pullback.fst f g ≫ f) a b ≫ pullback.snd (pullback.fst f g ≫ f) a) :=
        Category.assoc _ _ _
      _ = L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫
          (pullback.snd (pullback.fst f g ≫ f) (b ≫ a) ≫ b) :=
        congrArg (fun h => L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫ h)
          (familyMap_snd (pullback.fst f g ≫ f) a b)
      _ = (L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫
          pullback.snd (pullback.fst f g ≫ f) (b ≫ a)) ≫ b := (Category.assoc _ _ _).symm
      _ = pullback.snd g (b ≫ a) ≫ b :=
        congrArg (fun h => h ≫ b) (L4.CubeFaces.nativeCubeFaceYR_structure f g (b ≫ a) x hx)
      _ = familyMap g a b ≫ pullback.snd g a := (familyMap_snd g a b).symm
      _ = familyMap g a b ≫ (L6.nativeCubeFaceYR f g a x hx ≫
          pullback.snd (pullback.fst f g ≫ f) a) :=
        congrArg (fun h => familyMap g a b ≫ h)
          (L4.CubeFaces.nativeCubeFaceYR_structure f g a x hx).symm
      _ = (familyMap g a b ≫ L6.nativeCubeFaceYR f g a x hx) ≫
          pullback.snd (pullback.fst f g ≫ f) a := (Category.assoc _ _ _).symm

/-- HC for the literal field cube, without a field-flatness hypothesis. -/
theorem HC (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z) :
    IsPullback (familyMap (pullback.fst f g ≫ f) a b)
      (pullback.snd (pullback.fst f g ≫ f) (b ≫ a))
      (pullback.snd (pullback.fst f g ≫ f) a) b :=
  familyMap_isPullback (pullback.fst f g ≫ f) a b

/-- HX uses the original face and family triangles, not a substitute face. -/
theorem HX (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    IsPullback (familyMap f a b)
      (L6.nativeCubeFaceXR f g (b ≫ a) y hy ≫ pullback.snd (pullback.fst f g ≫ f) (b ≫ a))
      (L6.nativeCubeFaceXR f g a y hy ≫ pullback.snd (pullback.fst f g ≫ f) a) b := by
  simpa only [L4.CubeFaces.nativeCubeFaceXR_structure] using familyMap_isPullback f a b

/-- HY is the literal companion Cartesian square for the original Y-face. -/
theorem HY (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    IsPullback (familyMap g a b)
      (L6.nativeCubeFaceYR f g (b ≫ a) x hx ≫ pullback.snd (pullback.fst f g ≫ f) (b ≫ a))
      (L6.nativeCubeFaceYR f g a x hx ≫ pullback.snd (pullback.fst f g ≫ f) a) b := by
  simpa only [L4.CubeFaces.nativeCubeFaceYR_structure] using familyMap_isPullback g a b

/-- The actual X-face projects to identity on X and to the actual point on Y. -/
theorem faceX_projections
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceXR f g α y hy ≫ fieldFst f g α = 𝟙 _ ∧
      L6.nativeCubeFaceXR f g α y hy ≫ fieldSnd f g α = pullback.snd f α ≫ point g y hy α := by
  constructor
  · apply pullback.hom_ext
    · calc
        (L6.nativeCubeFaceXR f g α y hy ≫ fieldFst f g α) ≫ pullback.fst f α =
            L6.nativeCubeFaceXR f g α y hy ≫ (fieldFst f g α ≫ pullback.fst f α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceXR f g α y hy ≫
            (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.fst f g) :=
          congrArg (fun h => L6.nativeCubeFaceXR f g α y hy ≫ h) (fieldFst_fst f g α)
        _ = (L6.nativeCubeFaceXR f g α y hy ≫ pullback.fst (pullback.fst f g ≫ f) α) ≫
            pullback.fst f g := (Category.assoc _ _ _).symm
        _ = (pullback.fst f α ≫ L6.nativeCubeFaceXBase f g y hy) ≫ pullback.fst f g :=
          congrArg (fun h => h ≫ pullback.fst f g) (L4.CubeFaces.nativeCubeFaceXR_base_comm f g α y hy)
        _ = pullback.fst f α ≫ (L6.nativeCubeFaceXBase f g y hy ≫ pullback.fst f g) := Category.assoc _ _ _
        _ = pullback.fst f α ≫ 𝟙 X :=
          congrArg (fun h => pullback.fst f α ≫ h) (L4.CubeFaces.nativeCubeFaceXBase_fst f g y hy)
        _ = 𝟙 (pullback f α) ≫ pullback.fst f α :=
          (Category.comp_id _).trans (Category.id_comp _).symm
    · calc
        (L6.nativeCubeFaceXR f g α y hy ≫ fieldFst f g α) ≫ pullback.snd f α =
            L6.nativeCubeFaceXR f g α y hy ≫ (fieldFst f g α ≫ pullback.snd f α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceXR f g α y hy ≫ pullback.snd (pullback.fst f g ≫ f) α :=
          congrArg (fun h => L6.nativeCubeFaceXR f g α y hy ≫ h) (fieldFst_snd f g α)
        _ = pullback.snd f α := L4.CubeFaces.nativeCubeFaceXR_structure f g α y hy
        _ = 𝟙 (pullback f α) ≫ pullback.snd f α := (Category.id_comp _).symm
  · have base_snd : L6.nativeCubeFaceXBase f g y hy ≫ pullback.snd f g = f ≫ y := by
      unfold L6.nativeCubeFaceXBase
      exact pullback.lift_snd _ _ _
    have point_fst : point g y hy α ≫ pullback.fst g α = α ≫ y := by
      unfold point
      exact pullback.lift_fst _ _ _
    apply pullback.hom_ext
    · calc
        (L6.nativeCubeFaceXR f g α y hy ≫ fieldSnd f g α) ≫ pullback.fst g α =
            L6.nativeCubeFaceXR f g α y hy ≫ (fieldSnd f g α ≫ pullback.fst g α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceXR f g α y hy ≫
            (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.snd f g) :=
          congrArg (fun h => L6.nativeCubeFaceXR f g α y hy ≫ h) (fieldSnd_fst f g α)
        _ = (L6.nativeCubeFaceXR f g α y hy ≫ pullback.fst (pullback.fst f g ≫ f) α) ≫
            pullback.snd f g := (Category.assoc _ _ _).symm
        _ = (pullback.fst f α ≫ L6.nativeCubeFaceXBase f g y hy) ≫ pullback.snd f g :=
          congrArg (fun h => h ≫ pullback.snd f g) (L4.CubeFaces.nativeCubeFaceXR_base_comm f g α y hy)
        _ = pullback.fst f α ≫ (L6.nativeCubeFaceXBase f g y hy ≫ pullback.snd f g) := Category.assoc _ _ _
        _ = pullback.fst f α ≫ (f ≫ y) := congrArg (fun h => pullback.fst f α ≫ h) base_snd
        _ = (pullback.fst f α ≫ f) ≫ y := (Category.assoc _ _ _).symm
        _ = (pullback.snd f α ≫ α) ≫ y :=
          congrArg (fun h => h ≫ y) (pullback.condition (f := f) (g := α))
        _ = pullback.snd f α ≫ (α ≫ y) := Category.assoc _ _ _
        _ = pullback.snd f α ≫ (point g y hy α ≫ pullback.fst g α) :=
          congrArg (fun h => pullback.snd f α ≫ h) point_fst.symm
        _ = (pullback.snd f α ≫ point g y hy α) ≫ pullback.fst g α := (Category.assoc _ _ _).symm
    · calc
        (L6.nativeCubeFaceXR f g α y hy ≫ fieldSnd f g α) ≫ pullback.snd g α =
            L6.nativeCubeFaceXR f g α y hy ≫ (fieldSnd f g α ≫ pullback.snd g α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceXR f g α y hy ≫ pullback.snd (pullback.fst f g ≫ f) α :=
          congrArg (fun h => L6.nativeCubeFaceXR f g α y hy ≫ h) (fieldSnd_snd f g α)
        _ = pullback.snd f α := L4.CubeFaces.nativeCubeFaceXR_structure f g α y hy
        _ = pullback.snd f α ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = pullback.snd f α ≫ (point g y hy α ≫ pullback.snd g α) :=
          congrArg (fun h => pullback.snd f α ≫ h) (point_struct g y hy α).symm
        _ = (pullback.snd f α ≫ point g y hy α) ≫ pullback.snd g α := (Category.assoc _ _ _).symm

/-- The actual Y-face has the companion projection equations. -/
theorem faceY_projections
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    L6.nativeCubeFaceYR f g α x hx ≫ fieldFst f g α = pullback.snd g α ≫ point f x hx α ∧
      L6.nativeCubeFaceYR f g α x hx ≫ fieldSnd f g α = 𝟙 _ := by
  constructor
  · have base_fst : L6.nativeCubeFaceYBase f g x hx ≫ pullback.fst f g = g ≫ x := by
      unfold L6.nativeCubeFaceYBase
      exact pullback.lift_fst _ _ _
    have point_fst : point f x hx α ≫ pullback.fst f α = α ≫ x := by
      unfold point
      exact pullback.lift_fst _ _ _
    apply pullback.hom_ext
    · calc
        (L6.nativeCubeFaceYR f g α x hx ≫ fieldFst f g α) ≫ pullback.fst f α =
            L6.nativeCubeFaceYR f g α x hx ≫ (fieldFst f g α ≫ pullback.fst f α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceYR f g α x hx ≫
            (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.fst f g) :=
          congrArg (fun h => L6.nativeCubeFaceYR f g α x hx ≫ h) (fieldFst_fst f g α)
        _ = (L6.nativeCubeFaceYR f g α x hx ≫ pullback.fst (pullback.fst f g ≫ f) α) ≫
            pullback.fst f g := (Category.assoc _ _ _).symm
        _ = (pullback.fst g α ≫ L6.nativeCubeFaceYBase f g x hx) ≫ pullback.fst f g :=
          congrArg (fun h => h ≫ pullback.fst f g) (L4.CubeFaces.nativeCubeFaceYR_base_comm f g α x hx)
        _ = pullback.fst g α ≫ (L6.nativeCubeFaceYBase f g x hx ≫ pullback.fst f g) := Category.assoc _ _ _
        _ = pullback.fst g α ≫ (g ≫ x) := congrArg (fun h => pullback.fst g α ≫ h) base_fst
        _ = (pullback.fst g α ≫ g) ≫ x := (Category.assoc _ _ _).symm
        _ = (pullback.snd g α ≫ α) ≫ x :=
          congrArg (fun h => h ≫ x) (pullback.condition (f := g) (g := α))
        _ = pullback.snd g α ≫ (α ≫ x) := Category.assoc _ _ _
        _ = pullback.snd g α ≫ (point f x hx α ≫ pullback.fst f α) :=
          congrArg (fun h => pullback.snd g α ≫ h) point_fst.symm
        _ = (pullback.snd g α ≫ point f x hx α) ≫ pullback.fst f α := (Category.assoc _ _ _).symm
    · calc
        (L6.nativeCubeFaceYR f g α x hx ≫ fieldFst f g α) ≫ pullback.snd f α =
            L6.nativeCubeFaceYR f g α x hx ≫ (fieldFst f g α ≫ pullback.snd f α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceYR f g α x hx ≫ pullback.snd (pullback.fst f g ≫ f) α :=
          congrArg (fun h => L6.nativeCubeFaceYR f g α x hx ≫ h) (fieldFst_snd f g α)
        _ = pullback.snd g α := L4.CubeFaces.nativeCubeFaceYR_structure f g α x hx
        _ = pullback.snd g α ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = pullback.snd g α ≫ (point f x hx α ≫ pullback.snd f α) :=
          congrArg (fun h => pullback.snd g α ≫ h) (point_struct f x hx α).symm
        _ = (pullback.snd g α ≫ point f x hx α) ≫ pullback.snd f α := (Category.assoc _ _ _).symm
  · apply pullback.hom_ext
    · calc
        (L6.nativeCubeFaceYR f g α x hx ≫ fieldSnd f g α) ≫ pullback.fst g α =
            L6.nativeCubeFaceYR f g α x hx ≫ (fieldSnd f g α ≫ pullback.fst g α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceYR f g α x hx ≫
            (pullback.fst (pullback.fst f g ≫ f) α ≫ pullback.snd f g) :=
          congrArg (fun h => L6.nativeCubeFaceYR f g α x hx ≫ h) (fieldSnd_fst f g α)
        _ = (L6.nativeCubeFaceYR f g α x hx ≫ pullback.fst (pullback.fst f g ≫ f) α) ≫
            pullback.snd f g := (Category.assoc _ _ _).symm
        _ = (pullback.fst g α ≫ L6.nativeCubeFaceYBase f g x hx) ≫ pullback.snd f g :=
          congrArg (fun h => h ≫ pullback.snd f g) (L4.CubeFaces.nativeCubeFaceYR_base_comm f g α x hx)
        _ = pullback.fst g α ≫ (L6.nativeCubeFaceYBase f g x hx ≫ pullback.snd f g) := Category.assoc _ _ _
        _ = pullback.fst g α ≫ 𝟙 Y :=
          congrArg (fun h => pullback.fst g α ≫ h) (L4.CubeFaces.nativeCubeFaceYBase_snd f g x hx)
        _ = 𝟙 (pullback g α) ≫ pullback.fst g α :=
          (Category.comp_id _).trans (Category.id_comp _).symm
    · calc
        (L6.nativeCubeFaceYR f g α x hx ≫ fieldSnd f g α) ≫ pullback.snd g α =
            L6.nativeCubeFaceYR f g α x hx ≫ (fieldSnd f g α ≫ pullback.snd g α) := Category.assoc _ _ _
        _ = L6.nativeCubeFaceYR f g α x hx ≫ pullback.snd (pullback.fst f g ≫ f) α :=
          congrArg (fun h => L6.nativeCubeFaceYR f g α x hx ≫ h) (fieldSnd_snd f g α)
        _ = pullback.snd g α := L4.CubeFaces.nativeCubeFaceYR_structure f g α x hx
        _ = 𝟙 (pullback g α) ≫ pullback.snd g α := (Category.id_comp _).symm

/-- BOTH literal face equations under the actual field-product comparison. -/
theorem fieldProductIso_faces
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k))
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceXR f g α y hy ≫ (fieldProductIso f g α).hom =
        L6.nativeCubeFaceXBase (pullback.snd f α) (pullback.snd g α)
          (point g y hy α) (point_struct g y hy α) ∧
      L6.nativeCubeFaceYR f g α x hx ≫ (fieldProductIso f g α).hom =
        L6.nativeCubeFaceYBase (pullback.snd f α) (pullback.snd g α)
          (point f x hx α) (point_struct f x hx α) := by
  constructor
  · apply pullback.hom_ext
    · rw [Category.assoc, fieldProductIso_hom_fst, (faceX_projections f g α y hy).1]
      simp [L6.nativeCubeFaceXBase]
    · rw [Category.assoc, fieldProductIso_hom_snd, (faceX_projections f g α y hy).2]
      simp [L6.nativeCubeFaceXBase]
  · apply pullback.hom_ext
    · rw [Category.assoc, fieldProductIso_hom_fst, (faceY_projections f g α x hx).1]
      simp [L6.nativeCubeFaceYBase]
    · rw [Category.assoc, fieldProductIso_hom_snd, (faceY_projections f g α x hx).2]
      simp [L6.nativeCubeFaceYBase]

/-- The product comparison preserves the original field structure map. -/
@[reassoc] theorem fieldProductIso_hom_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    (fieldProductIso f g α).hom ≫
        (pullback.fst (pullback.snd f α) (pullback.snd g α) ≫ pullback.snd f α) =
      pullback.snd (pullback.fst f g ≫ f) α := by
  calc
    (fieldProductIso f g α).hom ≫
        (pullback.fst (pullback.snd f α) (pullback.snd g α) ≫ pullback.snd f α) =
      ((fieldProductIso f g α).hom ≫ pullback.fst (pullback.snd f α) (pullback.snd g α)) ≫
        pullback.snd f α := (Category.assoc _ _ _).symm
    _ = fieldFst f g α ≫ pullback.snd f α :=
      congrArg (fun h => h ≫ pullback.snd f α) (fieldProductIso_hom_fst f g α)
    _ = pullback.snd (pullback.fst f g ≫ f) α := fieldFst_snd f g α

/-- The inverse preserves that SAME field action on the native product. -/
@[reassoc] theorem fieldProductIso_inv_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (α : Spec (.of κ) ⟶ Spec (.of k)) :
    (fieldProductIso f g α).inv ≫ pullback.snd (pullback.fst f g ≫ f) α =
      pullback.fst (pullback.snd f α) (pullback.snd g α) ≫ pullback.snd f α := by
  calc
    (fieldProductIso f g α).inv ≫ pullback.snd (pullback.fst f g ≫ f) α =
        (fieldProductIso f g α).inv ≫ ((fieldProductIso f g α).hom ≫
          (pullback.fst (pullback.snd f α) (pullback.snd g α) ≫ pullback.snd f α)) := by
        rw [fieldProductIso_hom_struct]
    _ = pullback.fst (pullback.snd f α) (pullback.snd g α) ≫ pullback.snd f α := by simp

/-- HC on the native field-product coordinates used by L6's initial facts. -/
theorem product_HC (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z) :
    IsPullback ((fieldProductIso f g (b ≫ a)).inv ≫ familyMap (pullback.fst f g ≫ f) a b)
      (pullback.fst (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a)) ≫ pullback.snd f (b ≫ a))
      (pullback.snd (pullback.fst f g ≫ f) a) b := by
  exact (HC f g a b).of_iso' (fieldProductIso f g (b ≫ a)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Category.comp_id _).symm
    ((fieldProductIso_inv_struct f g (b ≫ a)).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- HX on the SAME native product X-face, proved from the existing face triangle. -/
theorem product_HX (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    IsPullback (familyMap f a b)
      (L6.nativeCubeFaceXBase (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a))
        (point g y hy (b ≫ a)) (point_struct g y hy (b ≫ a)) ≫
        (pullback.fst (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a)) ≫ pullback.snd f (b ≫ a)))
      (L6.nativeCubeFaceXR f g a y hy ≫ pullback.snd (pullback.fst f g ≫ f) a) b := by
  simpa only [L6.nativeCubeFaceXBase_struct, L4.CubeFaces.nativeCubeFaceXR_structure]
    using familyMap_isPullback f a b

/-- HY on the SAME native product Y-face. -/
theorem product_HY (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) :
    IsPullback (familyMap g a b)
      (L6.nativeCubeFaceYBase (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a))
        (point f x hx (b ≫ a)) (point_struct f x hx (b ≫ a)) ≫
        (pullback.fst (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a)) ≫ pullback.snd f (b ≫ a)))
      (L6.nativeCubeFaceYR f g a x hx ≫ pullback.snd (pullback.fst f g ≫ f) a) b := by
  simpa only [L6.nativeCubeFaceYBase_struct, L4.CubeFaces.nativeCubeFaceYR_structure]
    using familyMap_isPullback g a b

/-- The X model/native-H square uses the actual product coordinate map. -/
theorem product_faceX_square
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceXBase (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a))
        (point g y hy (b ≫ a)) (point_struct g y hy (b ≫ a)) ≫
        ((fieldProductIso f g (b ≫ a)).inv ≫ familyMap (pullback.fst f g ≫ f) a b) =
      familyMap f a b ≫ L6.nativeCubeFaceXR f g a y hy := by
  rw [← (fieldProductIso_faces f g (b ≫ a) x hx y hy).1]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using faceX_family_square f g a b y hy

/-- The Y square retains the original Y-face under the SAME product coordinate map. -/
theorem product_faceY_square
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z)
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    L6.nativeCubeFaceYBase (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a))
        (point f x hx (b ≫ a)) (point_struct f x hx (b ≫ a)) ≫
        ((fieldProductIso f g (b ≫ a)).inv ≫ familyMap (pullback.fst f g ≫ f) a b) =
      familyMap g a b ≫ L6.nativeCubeFaceYR f g a x hx := by
  rw [← (fieldProductIso_faces f g (b ≫ a) x hx y hy).2]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using faceY_family_square f g a b x hx

/-- The actual iterated field fibre PB(q,b) is the native kappa-product.
This is exactly the parent-requested Cartesian object comparison. -/
def cubeResidueProductIso
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z) :
    pullback (pullback.snd (pullback.fst f g ≫ f) a) b ≅
      pullback (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a)) :=
  ((IsPullback.of_hasPullback (pullback.snd (pullback.fst f g ≫ f) a) b).paste_horiz
    (IsPullback.of_hasPullback (pullback.fst f g ≫ f) a)).isoPullback ≪≫
      fieldProductIso f g (b ≫ a)

/-- The original fibre structure is the actual product field structure. -/
@[reassoc] theorem cubeResidueProductIso_struct
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (a : Z ⟶ Spec (.of k)) (b : Spec (.of κ) ⟶ Z) :
    (cubeResidueProductIso f g a b).hom ≫
        (pullback.fst (pullback.snd f (b ≫ a)) (pullback.snd g (b ≫ a)) ≫ pullback.snd f (b ≫ a)) =
      pullback.snd (pullback.snd (pullback.fst f g ≫ f) a) b := by
  rw [cubeResidueProductIso, Iso.trans_hom, Category.assoc, fieldProductIso_hom_struct]
  exact ((IsPullback.of_hasPullback (pullback.snd (pullback.fst f g ≫ f) a) b).paste_horiz
    (IsPullback.of_hasPullback (pullback.fst f g ≫ f) a)).isoPullback_hom_snd

end ResidueCartesian

/-- The canonical actual-complex version of the retained cone fibre bridge.
This computes homology after the original beta extension; it never claims
that beta (which need not be flat) commutes with homology. -/
private def scalarFibreHomologyIso (S : Type u) [CommRing S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) (s : Spec (.of S)) (n : ℤ) :
    (((L2.nativeResidueCochainFunctor S s).obj P).homology n) ≅
      (moduleSpecΓFunctor (R := (Spec (.of S)).residueField s)).obj
        ((((Scheme.Modules.pullback ((Spec (.of S)).fromSpecResidueField s)).mapHomologicalComplex
          (.up ℤ)).obj ((L2.nativeTildeCochainFunctor (.of S)).obj P)).homology n) :=
  L2.nativeFieldTildeHomologyIso ((Spec (.of S)).residueField s)
      (Field.toIsField ((Spec (.of S)).residueField s))
      ((L2.nativeResidueCochainFunctor S s).obj P) n ≪≫
    (moduleSpecΓFunctor (R := (Spec (.of S)).residueField s)).mapIso
      ((HomologicalComplex.homologyFunctor ((Spec ((Spec (.of S)).residueField s)).Modules)
        (.up ℤ) n).mapIso (L2.nativeResidueTildeComplexIso S P s).symm)

/-- Finiteness comes from the actual free finite raw terms, the actual
residue pullback and the canonical field comparison, not from a rank input. -/
private theorem finite_scalarFibre_homology (S : Type u) [CommRing S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (freeP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n))
    (s : Spec (.of S)) (n : ℤ) :
    Module.Finite ((Spec (.of S)).residueField s)
      (((L2.nativeResidueCochainFunctor S s).obj P).homology n) := by
  letI : Module.Finite ((Spec (.of S)).residueField s)
      ((moduleSpecΓFunctor (R := (Spec (.of S)).residueField s)).obj
        ((((Scheme.Modules.pullback ((Spec (.of S)).fromSpecResidueField s)).mapHomologicalComplex
          (.up ℤ)).obj ((L2.nativeTildeCochainFunctor (.of S)).obj P)).homology n)) :=
    Scheme.Modules.finite_moduleSpecΓFunctor_obj_homology_pullback
      (L2.nativeTildeCochain_freeFiniteTerms S P freeP)
      (Field.toIsField ((Spec (.of S)).residueField s))
      ((Spec (.of S)).fromSpecResidueField s) n
  exact Module.Finite.equiv (scalarFibreHomologyIso S P s n).toLinearEquiv.symm

/-- The original cochain biproduct component has its canonical module
product equivalence. Its functions are the ACTUAL projection/inclusion
components, never functions selected from a dimension. -/
private def biprodComponentEquiv (S : Type u) [CommRing S]
    (P Q : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    (P ⊞ Q).X n ≃ₗ[S] (P.X n × Q.X n) where
  toFun z := ((biprod.fst : P ⊞ Q ⟶ P).f n z, (biprod.snd : P ⊞ Q ⟶ Q).f n z)
  invFun z := (biprod.inl : P ⟶ P ⊞ Q).f n z.1 + (biprod.inr : Q ⟶ P ⊞ Q).f n z.2
  left_inv z := by
    have total : (biprod.fst : P ⊞ Q ⟶ P) ≫ biprod.inl +
        (biprod.snd : P ⊞ Q ⟶ Q) ≫ biprod.inr = 𝟙 (P ⊞ Q) := by
      apply biprod.hom_ext <;> simp
    have h := congrArg (fun φ : P ⊞ Q ⟶ P ⊞ Q => φ.f n z) total
    change (biprod.inl : P ⟶ P ⊞ Q).f n ((biprod.fst : P ⊞ Q ⟶ P).f n z) +
      (biprod.inr : Q ⟶ P ⊞ Q).f n ((biprod.snd : P ⊞ Q ⟶ Q).f n z) = z at h
    exact h
  right_inv z := by
    apply Prod.ext
    · have h1 : (biprod.inl : P ⟶ P ⊞ Q) ≫ biprod.fst = 𝟙 P := by simp
      have h2 : (biprod.inr : Q ⟶ P ⊞ Q) ≫ biprod.fst = (0 : Q ⟶ P) := by simp
      have a := congrArg (fun φ : P ⟶ P => φ.f n z.1) h1
      have b := congrArg (fun φ : Q ⟶ P => φ.f n z.2) h2
      change (biprod.fst : P ⊞ Q ⟶ P).f n ((biprod.inl : P ⟶ P ⊞ Q).f n z.1) = z.1 at a
      change (biprod.fst : P ⊞ Q ⟶ P).f n ((biprod.inr : Q ⟶ P ⊞ Q).f n z.2) = 0 at b
      change (biprod.fst : P ⊞ Q ⟶ P).f n
        ((biprod.inl : P ⟶ P ⊞ Q).f n z.1 + (biprod.inr : Q ⟶ P ⊞ Q).f n z.2) = z.1
      rw [map_add, a, b, add_zero]
    · have h1 : (biprod.inl : P ⟶ P ⊞ Q) ≫ biprod.snd = (0 : P ⟶ Q) := by simp
      have h2 : (biprod.inr : Q ⟶ P ⊞ Q) ≫ biprod.snd = 𝟙 Q := by simp
      have a := congrArg (fun φ : P ⟶ Q => φ.f n z.1) h1
      have b := congrArg (fun φ : Q ⟶ Q => φ.f n z.2) h2
      change (biprod.snd : P ⊞ Q ⟶ Q).f n ((biprod.inl : P ⟶ P ⊞ Q).f n z.1) = 0 at a
      change (biprod.snd : P ⊞ Q ⟶ Q).f n ((biprod.inr : Q ⟶ P ⊞ Q).f n z.2) = z.2 at b
      change (biprod.snd : P ⊞ Q ⟶ Q).f n
        ((biprod.inl : P ⟶ P ⊞ Q).f n z.1 + (biprod.inr : Q ⟶ P ⊞ Q).f n z.2) = z.2
      rw [map_add, a, b, zero_add]
  map_add' z w :=
    Prod.ext (((biprod.fst : P ⊞ Q ⟶ P).f n).hom.map_add z w)
      (((biprod.snd : P ⊞ Q ⟶ Q).f n).hom.map_add z w)
  map_smul' a z :=
    Prod.ext (((biprod.fst : P ⊞ Q ⟶ P).f n).hom.map_smul a z)
      (((biprod.snd : P ⊞ Q ⟶ Q).f n).hom.map_smul a z)

/-- Actual raw target PX biprod PY is finite free from the two produced
finite-free complexes, not an extra rank/model premise. -/
private theorem freeFinite_biprod_terms (S : Type u) [CommRing S]
    (P Q : CochainComplex (ModuleCat.{u} S) ℤ)
    (freeP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n))
    (freeQ : ∀ n, Module.Free S (Q.X n) ∧ Module.Finite S (Q.X n)) :
    ∀ n, Module.Free S ((P ⊞ Q).X n) ∧ Module.Finite S ((P ⊞ Q).X n) := by
  intro n
  letI : Module.Free S (P.X n) := (freeP n).1
  letI : Module.Finite S (P.X n) := (freeP n).2
  letI : Module.Free S (Q.X n) := (freeQ n).1
  letI : Module.Finite S (Q.X n) := (freeQ n).2
  letI : Module.Free S (P.X n × Q.X n) := inferInstance
  letI : Module.Finite S (P.X n × Q.X n) := inferInstance
  let e := biprodComponentEquiv S P Q n
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- PRIVATE quantitative assembly for the SAME original raw Phi. In the
cube application L1's semantic squares and the actual face trivializations
must discharge these rank/injection subgoals. They are not public geometry
premises, and no comparison is chosen from them. -/
private theorem retained_sourceHZero_neighbourhood
    (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D)
    (freeP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n))
    (freeD : ∀ n, Module.Free S (D.X n) ∧ Module.Finite S (D.X n))
    (targetHZero : ∀ s : Spec (.of S),
      Module.finrank ((Spec (.of S)).residueField s)
        (((L2.nativeResidueCochainFunctor S s).obj D).homology 0) = 2)
    (s : Spec (.of S))
    (initialHZero : Module.finrank ((Spec (.of S)).residueField s)
      (((L2.nativeResidueCochainFunctor S s).obj P).homology 0) = 1)
    (initialHZeroInjective : Function.Injective (HomologicalComplex.homologyMap
      ((L2.nativeResidueCochainFunctor S s).map Φ) (0 : ℤ)))
    (initialHOneInjective : Function.Injective (HomologicalComplex.homologyMap
      ((L2.nativeResidueCochainFunctor S s).map Φ) (1 : ℤ))) :
    ∃ V : (Spec (.of S)).Opens, s ∈ V ∧ ∀ z : Spec (.of S), z ∈ V →
      1 ≤ Module.finrank ((Spec (.of S)).residueField z)
        (((L2.nativeResidueCochainFunctor S z).obj P).homology 0) := by
  let Es := L2.nativeResidueCochainFunctor S s
  letI : Module.Finite ((Spec (.of S)).residueField s) ((Es.obj D).homology 0) :=
    finite_scalarFibre_homology S D freeD s 0
  have initialCone : Module.finrank ((Spec (.of S)).residueField s)
      ((CochainComplex.mappingCone (Es.map Φ)).homology 0) = 1 :=
    L2.hZero_mappingCone_eq_one (Es.obj P) (Es.obj D) (Es.map Φ)
      initialHZero (targetHZero s) initialHZeroInjective initialHOneInjective
  obtain ⟨V, hs, hV⟩ := L2.nativeTildeCone_exists_open_finrankHZero_le
    S P D Φ freeP freeD s
  refine ⟨V, hs, fun z hz => ?_⟩
  let Ez := L2.nativeResidueCochainFunctor S z
  letI : Module.Finite ((Spec (.of S)).residueField z) ((Ez.obj P).homology 0) :=
    finite_scalarFibre_homology S P freeP z 0
  letI : Module.Finite ((Spec (.of S)).residueField z) ((Ez.obj D).homology 0) :=
    finite_scalarFibre_homology S D freeD z 0
  letI : Module.Finite ((Spec (.of S)).residueField z)
      ((CochainComplex.mappingCone (Ez.map Φ)).homology 0) :=
    L2.nativeTildeCone_finite_fibreHomology S P D Φ freeP freeD z 0
  have coneBound : Module.finrank ((Spec (.of S)).residueField z)
      ((CochainComplex.mappingCone (Ez.map Φ)).homology 0) ≤ 1 := by
    have bound := hV z hz
    change Module.finrank ((Spec (.of S)).residueField z)
        ((CochainComplex.mappingCone (Ez.map Φ)).homology 0) ≤
      Module.finrank ((Spec (.of S)).residueField s)
        ((CochainComplex.mappingCone (Es.map Φ)).homology 0) at bound
    rw [initialCone] at bound
    exact bound
  exact L2.one_le_hZero_of_cone_bound (Ez.obj P) (Ez.obj D) (Ez.map Φ)
    (targetHZero z) coneBound

/-- The quantitative step on the LITERAL same-ring two-face arrow.
PX/PY/psiX/psiY are L1's produced objects/maps; the target is the ORIGINAL
biprod, and beta is the actual residue scalar map at every point. Its
remaining private rank/injection subgoals are discharged only once L1's
geometric native-H squares are supplied, never exposed as final premises. -/
private theorem retained_twoFaceHZero_neighbourhood
    (S : Type u) [CommRing S]
    (P PX PY : CochainComplex (ModuleCat.{u} S) ℤ)
    (ψX : P ⟶ PX) (ψY : P ⟶ PY)
    (freeP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n))
    (freePX : ∀ n, Module.Free S (PX.X n) ∧ Module.Finite S (PX.X n))
    (freePY : ∀ n, Module.Free S (PY.X n) ∧ Module.Finite S (PY.X n))
    (targetHZero : ∀ s : Spec (.of S),
      Module.finrank ((Spec (.of S)).residueField s)
        (((L2.nativeResidueCochainFunctor S s).obj (PX ⊞ PY)).homology 0) = 2)
    (s : Spec (.of S))
    (initialHZero : Module.finrank ((Spec (.of S)).residueField s)
      (((L2.nativeResidueCochainFunctor S s).obj P).homology 0) = 1)
    (initialHZeroInjective : Function.Injective (HomologicalComplex.homologyMap
      ((L2.nativeResidueCochainFunctor S s).map (biprod.lift ψX ψY)) (0 : ℤ)))
    (initialHOneInjective : Function.Injective (HomologicalComplex.homologyMap
      ((L2.nativeResidueCochainFunctor S s).map (biprod.lift ψX ψY)) (1 : ℤ))) :
    ∃ V : (Spec (.of S)).Opens, s ∈ V ∧ ∀ z : Spec (.of S), z ∈ V →
      1 ≤ Module.finrank ((Spec (.of S)).residueField z)
        (((L2.nativeResidueCochainFunctor S z).obj P).homology 0) :=
  retained_sourceHZero_neighbourhood S P (PX ⊞ PY) (biprod.lift ψX ψY)
    freeP (freeFinite_biprod_terms S PX PY freePX freePY) targetHZero s
    initialHZero initialHZeroInjective initialHOneInjective

/-- Literal residue-cone neighbourhood statement, separated from every
geometric and native-H compatibility assertion. -/
private def retainedModelConeNeighbourhoodStatement
    {R : Type u} [CommRing R] {Q FX FY : Scheme.{u}}
    {q : Q ⟶ Spec (.of R)} {jX : FX ⟶ Q} {jY : FY ⟶ Q}
    {M : Q.Modules} {ι : Type u} [Fintype ι] {U : ι → Q.Opens}
    {d : Γ(Spec (.of R), ⊤)}
    (m : L1.RetainedNativeCechFaceModels R q jX jY M U d)
    (s : Spec (.of (Localization.Away d))) : Prop :=
  ∃ V : (Spec (.of (Localization.Away d))).Opens,
    s ∈ V ∧ ∀ z : Spec (.of (Localization.Away d)), z ∈ V →
      Module.finrank ((Spec (.of (Localization.Away d))).residueField z)
          ((CochainComplex.mappingCone
            ((L2.nativeResidueCochainFunctor (Localization.Away d) z).map
              (biprod.lift m.ψX m.ψY))).homology 0) ≤
        Module.finrank ((Spec (.of (Localization.Away d))).residueField s)
          ((CochainComplex.mappingCone
            ((L2.nativeResidueCochainFunctor (Localization.Away d) s).map
              (biprod.lift m.ψX m.ψY))).homology 0)

/-- The cone bound alone, for the actual retained free-finite model. No
properness, flatness, invertibility or native-H compatibility instance enters. -/
private theorem retainedModel_coneNeighbourhood
    {R : Type u} [CommRing R] {Q FX FY : Scheme.{u}}
    {q : Q ⟶ Spec (.of R)} {jX : FX ⟶ Q} {jY : FY ⟶ Q}
    {M : Q.Modules} {ι : Type u} [Fintype ι] {U : ι → Q.Opens}
    {d : Γ(Spec (.of R), ⊤)}
    (m : L1.RetainedNativeCechFaceModels R q jX jY M U d)
    (s : Spec (.of (Localization.Away d))) :
    retainedModelConeNeighbourhoodStatement m s :=
  L2.nativeTildeCone_exists_open_finrankHZero_le
    (Localization.Away d) m.P (m.PX ⊞ m.PY) (biprod.lift m.ψX m.ψY)
    m.freeFiniteP
    (freeFinite_biprod_terms (Localization.Away d) m.PX m.PY m.freeFinitePX m.freeFinitePY) s

/-- Abstract retained-diagram assembly, so a concrete cube does not expand
all of its pullback coordinates while producing the finite-free cone bound. -/
private theorem retainedFaceConeNeighbourhood
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {Q FX FY : Scheme.{u}} (q : Q ⟶ Spec (.of R)) (jX : FX ⟶ Q) (jY : FY ⟶ Q)
    [IsProper q] [Flat q] [IsProper (jX ≫ q)] [Flat (jX ≫ q)]
    [IsProper (jY ≫ q)] [Flat (jY ≫ q)] [IsAffineHom jX] [IsAffineHom jY]
    (M : Q.Modules) [M.IsInvertible]
    {ι : Type u} [Fintype ι] [Nonempty ι] (U : ι → Q.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (p : Ideal Γ(Spec (.of R), ⊤)) [p.IsPrime] :
    ∃ d ∉ p, ∃ m : L1.RetainedNativeCechFaceModels R q jX jY M U d,
      m.NativeH01Compatible affineU coverU ∧
      ∀ s : Spec (.of (Localization.Away d)), retainedModelConeNeighbourhoodStatement m s := by
  obtain ⟨d, hd, m, nativeH01⟩ :=
    L1.exists_retained_nativeCechFaceModels_with_nativeH01 R q jX jY M U affineU coverU p
  exact ⟨d, hd, m, nativeH01, fun s => retainedModel_coneNeighbourhood m s⟩

/-- Actual affine cube families have L1's SAME retained two-face models and
an actual scalar-cone semicontinuity neighbourhood at EVERY point of their
common localization. Face properness/flatness/affineness is DERIVED from the
actual cube maps. The true finite affine cover is explicit local chart data;
no model, rank, injection, residue-flatness or cone condition is supplied as
geometry. The returned bound uses the LITERAL biprod.lift psiX psiY cone. -/
theorem exists_retained_cubeFace_cone_neighbourhood
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (a : Spec (.of R) ⟶ Spec (.of k))
    (M : (pullback (pullback.fst f g ≫ f) a).Modules) [M.IsInvertible]
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (U : ι → (pullback (pullback.fst f g ≫ f) a).Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (p : Ideal Γ(Spec (.of R), ⊤)) [p.IsPrime] :
    let q := pullback.snd (pullback.fst f g ≫ f) a
    let jX := L6.nativeCubeFaceXR f g a y hy
    let jY := L6.nativeCubeFaceYR f g a x hx
    letI : IsProper q := (L4.CubeFaces.nativeCubeFamily_geometry f g a).1
    letI : IsProper (jX ≫ q) :=
      (L4.CubeFaces.nativeCubeFaceXR_family_geometry f g a y hy).1
    letI : IsProper (jY ≫ q) :=
      (L4.CubeFaces.nativeCubeFaceYR_family_geometry f g a x hx).1
    letI : IsAffineHom jX := L4.CubeFaces.nativeCubeFaceXR_isAffineHom f g a y hy
    letI : IsAffineHom jY := L4.CubeFaces.nativeCubeFaceYR_isAffineHom f g a x hx
    ∃ d ∉ p, ∃ m : L1.RetainedNativeCechFaceModels R q jX jY M U d,
      m.NativeH01Compatible affineU coverU ∧
      ∀ s : Spec (.of (Localization.Away d)), retainedModelConeNeighbourhoodStatement m s := by
  intro q jX jY
  obtain ⟨properQ, flatQ, _⟩ := L4.CubeFaces.nativeCubeFamily_geometry f g a
  letI : IsProper q := properQ
  letI : Flat q := flatQ
  obtain ⟨properX, flatX⟩ := L4.CubeFaces.nativeCubeFaceXR_family_geometry f g a y hy
  obtain ⟨properY, flatY⟩ := L4.CubeFaces.nativeCubeFaceYR_family_geometry f g a x hx
  letI : IsProper (jX ≫ q) := properX
  letI : Flat (jX ≫ q) := flatX
  letI : IsProper (jY ≫ q) := properY
  letI : Flat (jY ≫ q) := flatY
  letI affineX : IsAffineHom jX := L4.CubeFaces.nativeCubeFaceXR_isAffineHom.{u} f g a y hy
  letI affineY : IsAffineHom jY := L4.CubeFaces.nativeCubeFaceYR_isAffineHom.{u} f g a x hx
  exact @retainedFaceConeNeighbourhood.{u}
    R ‹CommRing R› ‹IsNoetherianRing R›
    (pullback (C := Scheme.{u}) (pullback.fst f g ≫ f) a)
    (pullback (C := Scheme.{u}) f a) (pullback (C := Scheme.{u}) g a)
    q jX jY properQ flatQ properX flatX properY flatY affineX affineY
    M ‹M.IsInvertible› ι ‹Fintype ι› ‹Nonempty ι› U affineU coverU p ‹p.IsPrime›

/-- A field-valued commuting diagram factors through the ORIGINAL residue
fibre at its image point. Thus an actual residue-fibre Picard trivialization
pulls back to an actual field-fibre trivialization, with no flatness premise. -/
private theorem fieldPicard_trivial_of_residue
    {κ : Type u} [Field κ] {Q T B : Scheme.{u}}
    (q : Q ⟶ T) (b : Spec (.of κ) ⟶ T) (qB : B ⟶ Spec (.of κ)) (a : B ⟶ Q)
    (commutes : a ≫ q = qB ≫ b) (M : Q.Modules) [M.IsInvertible]
    (hM : Scheme.Pic.map (q.fiberι (b (IsLocalRing.closedPoint κ))) (Scheme.Pic.mk M) = 1) :
    Scheme.Pic.mk ((Scheme.Modules.pullback a).obj M) = 1 := by
  let t := b (IsLocalRing.closedPoint κ)
  let φ : T.residueField t ⟶ CommRingCat.of κ := T.descResidueField (Scheme.stalkClosedPointTo b)
  have hφ : Spec.map φ ≫ T.fromSpecResidueField t = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField κ T b
  let lift : B ⟶ q.fiber t := pullback.lift a (qB ≫ Spec.map φ) (by
    rw [Category.assoc, hφ]
    exact commutes)
  have hlift : lift ≫ q.fiberι t = a := by
    unfold lift Scheme.Hom.fiberι
    exact pullback.lift_fst _ _ _
  rw [← Scheme.Pic.map_mk, ← hlift, Scheme.Pic.map_comp, hM, Scheme.Pic.map_one]

/-- A finite NONEMPTY affine cover is genuine compact-space data. This is
the compact affine-basis construction used by the native finite-free provider,
not a boundedness assumption on the original non-alternating Cech complex. -/
private theorem finite_nonempty_affine_cover (Q : Scheme.{u}) [CompactSpace Q] :
    ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι) (U : ι → Q.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ := by
  obtain ⟨affines, finiteAffines, covering⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : Q.Opens))).mp
      (by simpa using isCompact_univ)
  letI : Finite affines := finiteAffines
  refine ⟨Option affines, inferInstance, inferInstance,
    fun i ↦ i.elim ⊥ fun affine ↦ affine.1.1, ?_, ?_⟩
  · rintro (_ | affine)
    exacts [isAffineOpen_bot Q, affine.1.2]
  · refine le_antisymm le_top ?_
    rw [covering]
    exact iSup₂_le fun affine membership ↦ le_iSup_of_le (some ⟨affine, membership⟩) le_rfl

/-- The SAME raw localization chart is an actual open immersion. -/
private theorem retainedChart_isOpenImmersion (R : Type u) [CommRing R]
    (d : Γ(Spec (.of R), ⊤)) :
    IsOpenImmersion (L1.retainedModelBaseChart R (Localization.Away d)) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Spec (.of R), ⊤) (Localization.Away d)))) :=
    IsOpenImmersion.of_isLocalization d (S := Localization.Away d)
  unfold L1.retainedModelBaseChart
  infer_instance

/-- Nonvanishing at the original prime lifts the ACTUAL base point to the
SAME localization chart. No auxiliary field point is selected from ranks. -/
private theorem retainedChart_lift_point (R : Type u) [CommRing R]
    (d : Γ(Spec (.of R), ⊤)) (t : Spec (.of R))
    (hd : d ∉ ((Spec (.of R)).isoSpec.hom t).asIdeal) :
    ∃ s : Spec (.of (Localization.Away d)), L1.retainedModelBaseChart R (Localization.Away d) s = t := by
  let A := Γ(Spec (.of R), ⊤)
  let α := algebraMap A (Localization.Away d)
  have hrange : (Spec (.of R)).isoSpec.hom t ∈ Set.range (Spec.map (CommRingCat.ofHom α)) := by
    change (Spec (.of R)).isoSpec.hom t ∈ Set.range (PrimeSpectrum.comap α)
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away d) d]
    exact hd
  obtain ⟨s, hs⟩ := hrange
  refine ⟨s, ?_⟩
  change (Spec (.of R)).isoSpec.inv ((Spec.map (CommRingCat.ofHom α)) s) = t
  rw [hs, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

/-- The SAME model source H0 is the ACTUAL original physical fibre H0 at
its chart image. This uses the produced source map, the native coefficient
comparison and genuine residue-field base change, not a rank-selected iso. -/
private theorem modelHZero_eq_hFiber
    (R : Type u) [CommRing R] {Q FX FY : Scheme.{u}}
    (q : Q ⟶ Spec (.of R)) [IsProper q] (jX : FX ⟶ Q) (jY : FY ⟶ Q)
    (M : Q.Modules) [M.IsInvertible] {ι : Type u} [Fintype ι]
    (U : ι → Q.Opens) (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (d : Γ(Spec (.of R), ⊤))
    (m : L1.RetainedNativeCechFaceModels R q jX jY M U d)
    (s : Spec (.of (Localization.Away d))) :
    Module.finrank ((Spec (.of (Localization.Away d))).residueField s)
        (((L2.nativeResidueCochainFunctor (Localization.Away d) s).obj m.P).homology 0) =
      M.hFiber q 0 (L1.retainedModelBaseChart R (Localization.Away d) s) := by
  letI : M.IsQuasicoherent := SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u} ‹M.IsInvertible›
  let S := Localization.Away d
  let chart := L1.retainedModelBaseChart R S
  let qS := pullback.snd q chart
  let MS := (Scheme.Modules.pullback (pullback.fst q chart)).obj M
  let κ := (Spec (.of S)).residueField s
  let qB := qS.fiberToSpecResidueField s
  let a := qS.fiberι s ≫ pullback.fst q chart
  letI : (qS.fiber s).Over (Spec κ) := ⟨qB⟩
  have chartSquare : IsPullback a qB q
      ((Spec (.of S)).fromSpecResidueField s ≫ chart) :=
    (congrArg (fun h : Spec κ ⟶ Spec (.of R) => IsPullback a qB q h)
      (L1.retainedFieldBasePoint_residue R S s)).mp
        (L1.retainedChartFibre_isPullback R S q s)
  let e := m.sourceResidueH affineU coverU s qB a chartSquare 0
  have he := e.finrank_eq
  have coefficientRank : Module.finrank κ (((Scheme.Modules.pullback a).obj M).H 0) =
      MS.hFiber qS 0 s :=
    Scheme.Modules.finrankH_congr κ (L1.retainedChartFibreCoefficientIso R S q M s) 0
  have baseRank : MS.hFiber qS 0 s = M.hFiber q 0 (chart s) :=
    Scheme.Modules.hFiber_pullback_of_isPullback q M chart (pullback.fst q chart) qS
      (IsPullback.of_hasPullback q chart) 0 s
  exact he.trans (coefficientRank.trans baseRank)

/-- Picard functoriality for an abstract commuting face square. Keeping
its schemes abstract avoids expanding concrete product coordinates here. -/
private theorem facePic_trivial_of_square
    {Q F QB FB : Scheme.{u}} (j : F ⟶ Q) (a : QB ⟶ Q) (b : FB ⟶ F) (jB : FB ⟶ QB)
    (square : jB ≫ a = b ≫ j) (M : Q.Modules) [M.IsInvertible]
    (hM : Scheme.Pic.map j (Scheme.Pic.mk M) = 1) :
    Scheme.Pic.mk ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M)) = 1 := by
  letI : ((Scheme.Modules.pullback a).obj M).IsInvertible :=
    Scheme.Modules.isInvertible_pullback a M
  letI : ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M)).IsInvertible :=
    Scheme.Modules.isInvertible_pullback jB ((Scheme.Modules.pullback a).obj M)
  rw [← Scheme.Pic.map_mk, ← Scheme.Pic.map_mk, ← Scheme.Pic.map_comp, square,
    Scheme.Pic.map_comp, hM, Scheme.Pic.map_one]

open MonoidalCategory CartesianMonoidalCategory

/-- Target rank transport over abstract field-face diagrams. The two unit
isomorphisms are obtained from the actual entire-face Picard equalities. -/
private theorem modelTargetPair_rankTwo
    (R : Type u) [CommRing R] {Q FX FY QB XB YB : Scheme.{u}}
    (q : Q ⟶ Spec (.of R)) (jX : FX ⟶ Q) (jY : FY ⟶ Q)
    [IsProper q] [IsAffineHom jX] [IsProper (jX ≫ q)]
    [IsAffineHom jY] [IsProper (jY ≫ q)]
    (M : Q.Modules) [M.IsInvertible] {ι : Type u} [Fintype ι]
    (U : ι → Q.Opens) (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (d : Γ(Spec (.of R), ⊤)) (m : L1.RetainedNativeCechFaceModels R q jX jY M U d)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    (qB : QB ⟶ Spec (.of κ)) (aB : QB ⟶ Q)
    (bX : XB ⟶ FX) (jXB : XB ⟶ QB) (bY : YB ⟶ FY) (jYB : YB ⟶ QB)
    [IsProper (jXB ≫ qB)] [GeometricallyIntegral (jXB ≫ qB)]
    [IsProper (jYB ≫ qB)] [GeometricallyIntegral (jYB ≫ qB)]
    (HC : IsPullback aB qB q (L1.retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (L1.retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (L1.retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ aB = bX ≫ jX) (squareY : jYB ≫ aB = bY ≫ jY)
    (hX : Scheme.Pic.map jX (Scheme.Pic.mk M) = 1)
    (hY : Scheme.Pic.map jY (Scheme.Pic.mk M) = 1) :
    Module.finrank κ
      (((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).obj (m.PX ⊞ m.PY)).homology 0) = 2 := by
  letI : QB.Over (Spec (.of κ)) := ⟨qB⟩
  letI : XB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
  letI : YB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
  let MB : QB.Modules := (Scheme.Modules.pullback aB).obj M
  have invertibleMB : MB.IsInvertible :=
    @Scheme.Modules.isInvertible_pullback.{u} QB Q aB M ‹M.IsInvertible›
  letI : MB.IsInvertible := invertibleMB
  let MX : XB.Modules := (Scheme.Modules.pullback jXB).obj MB
  letI : MX.IsInvertible := @Scheme.Modules.isInvertible_pullback.{u} XB QB jXB MB invertibleMB
  let MY : YB.Modules := (Scheme.Modules.pullback jYB).obj MB
  letI : MY.IsInvertible := @Scheme.Modules.isInvertible_pullback.{u} YB QB jYB MB invertibleMB
  have hMX : Scheme.Pic.mk MX = 1 := facePic_trivial_of_square jX aB bX jXB squareX M hX
  have hMY : Scheme.Pic.mk MY = 1 := facePic_trivial_of_square jY aB bY jYB squareY M hY
  obtain ⟨eX⟩ := (Scheme.Pic.mk_eq_mk_iff MX (Scheme.Modules.unit XB)).mp
    (hMX.trans Scheme.Pic.one_eq_mk_unit)
  obtain ⟨eY⟩ := (Scheme.Pic.mk_eq_mk_iff MY (Scheme.Modules.unit YB)).mp
    (hMY.trans Scheme.Pic.one_eq_mk_unit)
  have pairRank : Module.finrank κ
      (((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).obj (m.PX ⊞ m.PY)).homology 0) =
      Module.finrank κ (MX.H 0 × MY.H 0) :=
    m.finrank_modelTargetPair_eq_nativeFaces affineU coverU κ β qB aB bX jXB bY jYB
      HC HX HY squareX squareY
  haveI : IsProper (Over.mk (jXB ≫ qB)).hom := inferInstanceAs (IsProper (jXB ≫ qB))
  haveI : GeometricallyIntegral (Over.mk (jXB ≫ qB)).hom :=
    inferInstanceAs (GeometricallyIntegral (jXB ≫ qB))
  haveI : IsProper (Over.mk (jYB ≫ qB)).hom := inferInstanceAs (IsProper (jYB ≫ qB))
  haveI : GeometricallyIntegral (Over.mk (jYB ≫ qB)).hom :=
    inferInstanceAs (GeometricallyIntegral (jYB ≫ qB))
  have nativeTwo : Module.finrank κ (MX.H 0 × MY.H 0) = 2 :=
    L6.nativeHZero_trivialFaces_finrank_eq_two (Over.mk (jXB ≫ qB)) (Over.mk (jYB ≫ qB)) MX MY eX eY
  exact pairRank.trans nativeTwo

/-- Initial source rank and the two actual map injections, over abstract
native product factors. Only the original constructed model comparisons and
an actual coefficient trivialization are transported. -/
private theorem modelProduct_initialHZeroHOne
    (R : Type u) [CommRing R] {Q FX FY : Scheme.{u}}
    (q : Q ⟶ Spec (.of R)) (jX : FX ⟶ Q) (jY : FY ⟶ Q)
    [IsProper q] [IsAffineHom jX] [IsProper (jX ≫ q)]
    [IsAffineHom jY] [IsProper (jY ≫ q)]
    (M : Q.Modules) [M.IsInvertible] {ι : Type u} [Fintype ι]
    (U : ι → Q.Opens) (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (d : Γ(Spec (.of R), ⊤)) (m : L1.RetainedNativeCechFaceModels R q jX jY M U d)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    (A B : Over (Spec (.of κ)))
    [IsProper A.hom] [GeometricallyIntegral A.hom]
    [IsProper B.hom] [GeometricallyIntegral B.hom]
    (xκ : 𝟙_ (Over (Spec (.of κ))) ⟶ A) (yκ : 𝟙_ (Over (Spec (.of κ))) ⟶ B)
    (aB : (A ⊗ B).left ⟶ Q) (bX : A.left ⟶ FX) (bY : B.left ⟶ FY)
    (HC : IsPullback aB (A ⊗ B).hom q (L1.retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX ((lift (𝟙 A) (toUnit A ≫ yκ)).left ≫ (A ⊗ B).hom)
      (jX ≫ q) (L1.retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY ((lift (toUnit B ≫ xκ) (𝟙 B)).left ≫ (A ⊗ B).hom)
      (jY ≫ q) (L1.retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : (lift (𝟙 A) (toUnit A ≫ yκ)).left ≫ aB = bX ≫ jX)
    (squareY : (lift (toUnit B ≫ xκ) (𝟙 B)).left ≫ aB = bY ≫ jY)
    (eB : (Scheme.Modules.pullback aB).obj M ≅ Scheme.Modules.unit (A ⊗ B).left) :
    Module.finrank κ
        (((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).obj m.P).homology 0) = 1 ∧
      Function.Injective (HomologicalComplex.homologyMap
        ((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (0 : ℤ)) ∧
      Function.Injective (HomologicalComplex.homologyMap
        ((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (1 : ℤ)) := by
  letI : (A ⊗ B).left.Over (Spec (.of κ)) := ⟨(A ⊗ B).hom⟩
  letI : A.left.Over (Spec (.of κ)) := ⟨A.hom⟩
  letI : B.left.Over (Spec (.of κ)) := ⟨B.hom⟩
  let jXB := (lift (𝟙 A) (toUnit A ≫ yκ)).left
  let jYB := (lift (toUnit B ≫ xκ) (𝟙 B)).left
  have sourceOne : Module.finrank κ
      (((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).obj m.P).homology 0) = 1 :=
    (m.sourceFieldH affineU coverU κ β (A ⊗ B).hom aB HC 0).finrank_eq.trans
      (L6.nativeHZero_trivialProduct_finrank_eq_one A B ((Scheme.Modules.pullback aB).obj M) eB)
  have nativeZero : Function.Injective (fun z : ((Scheme.Modules.pullback aB).obj M).H 0 =>
      (Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback aB).obj M) 0 z,
        Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback aB).obj M) 0 z)) :=
    L6.nativeHZero_twoFacesModule_injective A B xκ yκ ((Scheme.Modules.pullback aB).obj M) eB
  have nativeOne : Function.Injective (fun z : ((Scheme.Modules.pullback aB).obj M).H 1 =>
      (Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback aB).obj M) 1 z,
        Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback aB).obj M) 1 z)) :=
    L6.nativeHOne_twoFacesModule_injective A B xκ yκ ((Scheme.Modules.pullback aB).obj M) eB
  have injectZero : Function.Injective (HomologicalComplex.homologyMap
      ((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (0 : ℤ)) :=
    (m.homology_modelPair_injective_iff_nativeFacePair affineU coverU κ β
      (A ⊗ B).hom aB bX jXB bY jYB HC HX HY squareX squareY 0 (by omega)).mpr nativeZero
  have injectOne : Function.Injective (HomologicalComplex.homologyMap
      ((L1.RetainedFaceFibreConstruction.scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (1 : ℤ)) :=
    (m.homology_modelPair_injective_iff_nativeFacePair affineU coverU κ β
      (A ⊗ B).hom aB bX jXB bY jYB HC HX HY squareX squareY 1 (by omega)).mpr nativeOne
  exact ⟨sourceOne, injectZero, injectOne⟩

/-- Actual residue H0 dimension, named independently of geometry and
native-H site instances. This is the same scalar complex and homology. -/
private def residueHZeroDimension (S : Type u) [CommRing S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) (s : Spec (.of S)) : ℕ :=
  Module.finrank ((Spec (.of S)).residueField s)
    (((L2.nativeResidueCochainFunctor S s).obj P).homology 0)

/-- Injectivity of the literal residue two-face map, stated independently
of its geometric construction. No injection assumption is introduced. -/
private def residueTwoFaceInjection (S : Type u) [CommRing S]
    (P PX PY : CochainComplex (ModuleCat.{u} S) ℤ)
    (ψX : P ⟶ PX) (ψY : P ⟶ PY) (s : Spec (.of S)) (n : ℤ) : Prop :=
  Function.Injective (HomologicalComplex.homologyMap
    ((L2.nativeResidueCochainFunctor S s).map (biprod.lift ψX ψY)) n)

/-- The target-rank consequence at one residue point. Its construction is
separate from initial source rank and initial map injectivity. -/
private theorem cubeModel_residueTargetRank
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (R : Type u) [CommRing R] (a : Spec (.of R) ⟶ Spec (.of k))
    (M : (pullback (pullback.fst f g ≫ f) a).Modules) [M.IsInvertible]
    {ι : Type u} [Fintype ι] (U : ι → (pullback (pullback.fst f g ≫ f) a).Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (d : Γ(Spec (.of R), ⊤))
    (m : L1.RetainedNativeCechFaceModels R (pullback.snd (pullback.fst f g ≫ f) a)
      (L6.nativeCubeFaceXR f g a y hy) (L6.nativeCubeFaceYR f g a x hx) M U d)
    (hX : Scheme.Pic.map (L6.nativeCubeFaceXR f g a y hy) (Scheme.Pic.mk M) = 1)
    (hY : Scheme.Pic.map (L6.nativeCubeFaceYR f g a x hx) (Scheme.Pic.mk M) = 1)
    (s : Spec (.of (Localization.Away d))) :
    residueHZeroDimension (Localization.Away d) (m.PX ⊞ m.PY) s = 2 := by
  let q := pullback.snd (pullback.fst f g ≫ f) a
  let jX := L6.nativeCubeFaceXR f g a y hy
  let jY := L6.nativeCubeFaceYR f g a x hx
  letI : IsProper q := (L4.CubeFaces.nativeCubeFamily_geometry f g a).1
  letI : IsProper (jX ≫ q) := (L4.CubeFaces.nativeCubeFaceXR_family_geometry f g a y hy).1
  letI : IsProper (jY ≫ q) := (L4.CubeFaces.nativeCubeFaceYR_family_geometry f g a x hx).1
  letI : IsAffineHom jX := L4.CubeFaces.nativeCubeFaceXR_isAffineHom f g a y hy
  letI : IsAffineHom jY := L4.CubeFaces.nativeCubeFaceYR_isAffineHom f g a x hx
  let S := Localization.Away d
  let κ := (Spec (.of S)).residueField s
  let β := L2.nativeResidueScalarMap S s
  let chart := L1.retainedModelBaseChart R S
  let b := (Spec (.of S)).fromSpecResidueField s ≫ chart
  let α := b ≫ a
  let qB := pullback.fst (pullback.snd f α) (pullback.snd g α) ≫ pullback.snd f α
  let aB := (ResidueCartesian.fieldProductIso f g α).inv ≫
    ResidueCartesian.familyMap (pullback.fst f g ≫ f) a b
  let bX := ResidueCartesian.familyMap f a b
  let bY := ResidueCartesian.familyMap g a b
  let xκ := ResidueCartesian.point f x hx α
  let yκ := ResidueCartesian.point g y hy α
  let hxκ := ResidueCartesian.point_struct f x hx α
  let hyκ := ResidueCartesian.point_struct g y hy α
  let jXB := L6.nativeCubeFaceXBase (pullback.snd f α) (pullback.snd g α) yκ hyκ
  let jYB := L6.nativeCubeFaceYBase (pullback.snd f α) (pullback.snd g α) xκ hxκ
  have squareX : jXB ≫ aB = bX ≫ jX := ResidueCartesian.product_faceX_square f g a b x hx y hy
  have squareY : jYB ≫ aB = bY ≫ jY := ResidueCartesian.product_faceY_square f g a b x hx y hy
  have hc : IsPullback aB qB q (L1.retainedFieldBasePoint R S κ β) := by
    rw [L1.retainedFieldBasePoint_residue]
    exact ResidueCartesian.product_HC f g a b
  have hcx : IsPullback bX (jXB ≫ qB) (jX ≫ q) (L1.retainedFieldBasePoint R S κ β) := by
    rw [L1.retainedFieldBasePoint_residue]
    exact ResidueCartesian.product_HX f g a b y hy
  have hcy : IsPullback bY (jYB ≫ qB) (jY ≫ q) (L1.retainedFieldBasePoint R S κ β) := by
    rw [L1.retainedFieldBasePoint_residue]
    exact ResidueCartesian.product_HY f g a b x hx
  have structX : jXB ≫ qB = pullback.snd f α :=
    L6.nativeCubeFaceXBase_struct (pullback.snd f α) (pullback.snd g α) yκ hyκ
  have structY : jYB ≫ qB = pullback.snd g α :=
    L6.nativeCubeFaceYBase_struct (pullback.snd f α) (pullback.snd g α) xκ hxκ
  have properXB : IsProper (jXB ≫ qB) :=
    Eq.mpr (congrArg (fun σ => IsProper σ) structX) (inferInstanceAs (IsProper (pullback.snd f α)))
  have integralXB : GeometricallyIntegral (jXB ≫ qB) :=
    Eq.mpr (congrArg (fun σ => GeometricallyIntegral σ) structX)
      (inferInstanceAs (GeometricallyIntegral (pullback.snd f α)))
  have properYB : IsProper (jYB ≫ qB) :=
    Eq.mpr (congrArg (fun σ => IsProper σ) structY) (inferInstanceAs (IsProper (pullback.snd g α)))
  have integralYB : GeometricallyIntegral (jYB ≫ qB) :=
    Eq.mpr (congrArg (fun σ => GeometricallyIntegral σ) structY)
      (inferInstanceAs (GeometricallyIntegral (pullback.snd g α)))
  exact @modelTargetPair_rankTwo R _ _ _ _ _ _ _ q jX jY _ _ _ _ _ M _ ι _
    U affineU coverU d m κ _ β qB aB bX jXB bY jYB
    properXB integralXB properYB integralYB hc hcx hcy squareX squareY hX hY

/-- Initial source rank and actual H0/H1 injections at one residue point.
This declaration does not also elaborate the target-rank consequence. -/
private theorem cubeModel_residueInitialFacts
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (R : Type u) [CommRing R] (a : Spec (.of R) ⟶ Spec (.of k))
    (M : (pullback (pullback.fst f g ≫ f) a).Modules) [M.IsInvertible]
    {ι : Type u} [Fintype ι] (U : ι → (pullback (pullback.fst f g ≫ f) a).Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (d : Γ(Spec (.of R), ⊤))
    (m : L1.RetainedNativeCechFaceModels R (pullback.snd (pullback.fst f g ≫ f) a)
      (L6.nativeCubeFaceXR f g a y hy) (L6.nativeCubeFaceYR f g a x hx) M U d)
    (s : Spec (.of (Localization.Away d)))
    (initialPic : Scheme.Pic.map ((pullback.snd (pullback.fst f g ≫ f) a).fiberι
      (L1.retainedModelBaseChart R (Localization.Away d) s)) (Scheme.Pic.mk M) = 1) :
    residueHZeroDimension (Localization.Away d) m.P s = 1 ∧
      residueTwoFaceInjection (Localization.Away d) m.P m.PX m.PY m.ψX m.ψY s (0 : ℤ) ∧
      residueTwoFaceInjection (Localization.Away d) m.P m.PX m.PY m.ψX m.ψY s (1 : ℤ) := by
  let q := pullback.snd (pullback.fst f g ≫ f) a
  let jX := L6.nativeCubeFaceXR f g a y hy
  let jY := L6.nativeCubeFaceYR f g a x hx
  letI : IsProper q := (L4.CubeFaces.nativeCubeFamily_geometry f g a).1
  letI : IsProper (jX ≫ q) := (L4.CubeFaces.nativeCubeFaceXR_family_geometry f g a y hy).1
  letI : IsProper (jY ≫ q) := (L4.CubeFaces.nativeCubeFaceYR_family_geometry f g a x hx).1
  letI : IsAffineHom jX := L4.CubeFaces.nativeCubeFaceXR_isAffineHom f g a y hy
  letI : IsAffineHom jY := L4.CubeFaces.nativeCubeFaceYR_isAffineHom f g a x hx
  let S := Localization.Away d
  let κ := (Spec (.of S)).residueField s
  let β := L2.nativeResidueScalarMap S s
  let chart := L1.retainedModelBaseChart R S
  let b := (Spec (.of S)).fromSpecResidueField s ≫ chart
  let α := b ≫ a
  let Xκ : Over (Spec κ) := Over.mk (pullback.snd f α)
  let Yκ : Over (Spec κ) := Over.mk (pullback.snd g α)
  let Pκ := pullback (pullback.snd f α) (pullback.snd g α)
  let qB := pullback.fst (pullback.snd f α) (pullback.snd g α) ≫ pullback.snd f α
  let aB := (ResidueCartesian.fieldProductIso f g α).inv ≫
    ResidueCartesian.familyMap (pullback.fst f g ≫ f) a b
  let bX := ResidueCartesian.familyMap f a b
  let bY := ResidueCartesian.familyMap g a b
  let xκ := ResidueCartesian.point f x hx α
  let yκ := ResidueCartesian.point g y hy α
  let hxκ := ResidueCartesian.point_struct f x hx α
  let hyκ := ResidueCartesian.point_struct g y hy α
  let jXB := L6.nativeCubeFaceXBase (pullback.snd f α) (pullback.snd g α) yκ hyκ
  let jYB := L6.nativeCubeFaceYBase (pullback.snd f α) (pullback.snd g α) xκ hxκ
  letI : Pκ.Over (Spec κ) := ⟨qB⟩
  letI : (pullback f α).Over (Spec κ) := ⟨pullback.snd f α⟩
  letI : (pullback g α).Over (Spec κ) := ⟨pullback.snd g α⟩
  letI : IsProper Xκ.hom := inferInstanceAs (IsProper (pullback.snd f α))
  letI : GeometricallyIntegral Xκ.hom := inferInstanceAs (GeometricallyIntegral (pullback.snd f α))
  letI : IsProper Yκ.hom := inferInstanceAs (IsProper (pullback.snd g α))
  letI : GeometricallyIntegral Yκ.hom := inferInstanceAs (GeometricallyIntegral (pullback.snd g α))
  let MB : Pκ.Modules := (Scheme.Modules.pullback aB).obj M
  have invertibleMB : MB.IsInvertible :=
    @Scheme.Modules.isInvertible_pullback.{u} _ _ aB M ‹M.IsInvertible›
  letI : MB.IsInvertible := invertibleMB
  have squareX : jXB ≫ aB = bX ≫ jX := ResidueCartesian.product_faceX_square f g a b x hx y hy
  have squareY : jYB ≫ aB = bY ≫ jY := ResidueCartesian.product_faceY_square f g a b x hx y hy
  have hc : IsPullback aB qB q (L1.retainedFieldBasePoint R S κ β) := by
    rw [L1.retainedFieldBasePoint_residue]
    exact ResidueCartesian.product_HC f g a b
  have hcx : IsPullback bX (jXB ≫ qB) (jX ≫ q) (L1.retainedFieldBasePoint R S κ β) := by
    rw [L1.retainedFieldBasePoint_residue]
    exact ResidueCartesian.product_HX f g a b y hy
  have hcy : IsPullback bY (jYB ≫ qB) (jY ≫ q) (L1.retainedFieldBasePoint R S κ β) := by
    rw [L1.retainedFieldBasePoint_residue]
    exact ResidueCartesian.product_HY f g a b x hx
  have pointImage : b (IsLocalRing.closedPoint κ) = chart s := by
    change chart ((Spec (.of S)).fromSpecResidueField s (IsLocalRing.closedPoint κ)) = chart s
    exact congrArg (fun z : Spec (.of S) => chart z)
      (Scheme.fromSpecResidueField_apply (X := Spec (.of S)) s (IsLocalRing.closedPoint κ))
  have initialAtPoint : Scheme.Pic.map (q.fiberι (b (IsLocalRing.closedPoint κ)))
      (Scheme.Pic.mk M) = 1 :=
    Eq.mpr (congrArg (fun z : Spec (.of R) =>
      Scheme.Pic.map (q.fiberι z) (Scheme.Pic.mk M) = 1) pointImage) initialPic
  have hMB : Scheme.Pic.mk MB = 1 :=
    fieldPicard_trivial_of_residue q b qB aB (ResidueCartesian.product_HC f g a b).w M initialAtPoint
  obtain ⟨eB⟩ := (Scheme.Pic.mk_eq_mk_iff MB (Scheme.Modules.unit Pκ)).mp
    (hMB.trans Scheme.Pic.one_eq_mk_unit)
  let xp : Over.mk (𝟙 (Spec κ)) ⟶ Xκ := Over.homMk xκ hxκ
  let yp : Over.mk (𝟙 (Spec κ)) ⟶ Yκ := Over.homMk yκ hyκ
  exact modelProduct_initialHZeroHOne R q jX jY M U affineU coverU d m κ β
    Xκ Yκ xp yp aB bX bY hc hcx hcy squareX squareY eB

/-- The actual entire faces force rank two of the SAME residue target;
an initially trivial physical fibre forces source rank one and BOTH actual
model-map injections. All comparison maps come from L1's produced package. -/
private theorem cubeModel_fieldFacts
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (R : Type u) [CommRing R] (a : Spec (.of R) ⟶ Spec (.of k))
    (M : (pullback (pullback.fst f g ≫ f) a).Modules) [M.IsInvertible]
    {ι : Type u} [Fintype ι] (U : ι → (pullback (pullback.fst f g ≫ f) a).Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (d : Γ(Spec (.of R), ⊤))
    (m : L1.RetainedNativeCechFaceModels R (pullback.snd (pullback.fst f g ≫ f) a)
      (L6.nativeCubeFaceXR f g a y hy) (L6.nativeCubeFaceYR f g a x hx) M U d)
    (hX : Scheme.Pic.map (L6.nativeCubeFaceXR f g a y hy) (Scheme.Pic.mk M) = 1)
    (hY : Scheme.Pic.map (L6.nativeCubeFaceYR f g a x hx) (Scheme.Pic.mk M) = 1) :
    ∀ s : Spec (.of (Localization.Away d)),
      residueHZeroDimension (Localization.Away d) (m.PX ⊞ m.PY) s = 2 ∧
      (Scheme.Pic.map ((pullback.snd (pullback.fst f g ≫ f) a).fiberι
          (L1.retainedModelBaseChart R (Localization.Away d) s)) (Scheme.Pic.mk M) = 1 →
        residueHZeroDimension (Localization.Away d) m.P s = 1 ∧
        residueTwoFaceInjection (Localization.Away d) m.P m.PX m.PY m.ψX m.ψY s (0 : ℤ) ∧
        residueTwoFaceInjection (Localization.Away d) m.P m.PX m.PY m.ψX m.ψY s (1 : ℤ)) := by
  intro s
  exact ⟨cubeModel_residueTargetRank f g x hx y hy R a M U affineU coverU d m hX hY s,
    fun h => cubeModel_residueInitialFacts f g x hx y hy R a M U affineU coverU d m s h⟩

/-- On an actual affine cube parameter, the lower H0 bound is produced by
EXACTLY the two-face cone mechanism. Ordinary h0 semicontinuity is never used
to infer openness. The model and all numeric/map subgoals are derived. -/
private theorem exists_open_affine_cubeHZero
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f] [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (a : Spec (.of R) ⟶ Spec (.of k))
    (M : (pullback (pullback.fst f g ≫ f) a).Modules) [M.IsInvertible]
    (hX : Scheme.Pic.map (L6.nativeCubeFaceXR f g a y hy) (Scheme.Pic.mk M) = 1)
    (hY : Scheme.Pic.map (L6.nativeCubeFaceYR f g a x hx) (Scheme.Pic.mk M) = 1)
    (t : Spec (.of R))
    (ht : Scheme.Pic.map ((pullback.snd (pullback.fst f g ≫ f) a).fiberι t) (Scheme.Pic.mk M) = 1) :
    ∃ V : (Spec (.of R)).Opens, t ∈ V ∧ ∀ z : Spec (.of R), z ∈ V →
      1 ≤ M.hFiber (pullback.snd (pullback.fst f g ≫ f) a) 0 z := by
  classical
  let q := pullback.snd (pullback.fst f g ≫ f) a
  let jX := L6.nativeCubeFaceXR f g a y hy
  let jY := L6.nativeCubeFaceYR f g a x hx
  letI : IsProper q := (L4.CubeFaces.nativeCubeFamily_geometry f g a).1
  letI : Flat q := (L4.CubeFaces.nativeCubeFamily_geometry f g a).2.1
  letI : IsProper (jX ≫ q) := (L4.CubeFaces.nativeCubeFaceXR_family_geometry f g a y hy).1
  letI : Flat (jX ≫ q) := (L4.CubeFaces.nativeCubeFaceXR_family_geometry f g a y hy).2
  letI : IsProper (jY ≫ q) := (L4.CubeFaces.nativeCubeFaceYR_family_geometry f g a x hx).1
  letI : Flat (jY ≫ q) := (L4.CubeFaces.nativeCubeFaceYR_family_geometry f g a x hx).2
  letI : IsAffineHom jX := L4.CubeFaces.nativeCubeFaceXR_isAffineHom f g a y hy
  letI : IsAffineHom jY := L4.CubeFaces.nativeCubeFaceYR_isAffineHom f g a x hx
  letI : CompactSpace ↥(pullback (C := Scheme.{u}) (pullback.fst f g ≫ f) a) :=
    QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨ι, finiteι, nonemptyι, U, affineU, coverU⟩ :=
    finite_nonempty_affine_cover (pullback (pullback.fst f g ≫ f) a)
  letI : Finite ι := finiteι
  letI : Nonempty ι := nonemptyι
  letI : Fintype ι := Fintype.ofFinite ι
  let p : Ideal Γ(Spec (.of R), ⊤) := ((Spec (.of R)).isoSpec.hom t).asIdeal
  letI : p.IsPrime := ((Spec (.of R)).isoSpec.hom t).isPrime
  obtain ⟨d, hd, m, nativeH01⟩ :
      ∃ d ∉ p, ∃ m : L1.RetainedNativeCechFaceModels R q jX jY M U d,
        m.NativeH01Compatible affineU coverU :=
    L1.exists_retained_nativeCechFaceModels_with_nativeH01 R q jX jY M U affineU coverU p
  let S := Localization.Away d
  let chart := L1.retainedModelBaseChart R S
  obtain ⟨s, hs⟩ := retainedChart_lift_point R d t hd
  have facts := cubeModel_fieldFacts f g x hx y hy R a M U affineU coverU d m hX hY
  have initialAtChart : Scheme.Pic.map (q.fiberι (chart s)) (Scheme.Pic.mk M) = 1 :=
    Eq.mpr (congrArg (fun z : Spec (.of R) =>
      Scheme.Pic.map (q.fiberι z) (Scheme.Pic.mk M) = 1) hs) ht
  have initial := (facts s).2 initialAtChart
  let D := m.PX ⊞ m.PY
  let Φ := biprod.lift m.ψX m.ψY
  have freeD := freeFinite_biprod_terms S m.PX m.PY m.freeFinitePX m.freeFinitePY
  let Es := L2.nativeResidueCochainFunctor S s
  letI : Module.Finite ((Spec (.of S)).residueField s) ((Es.obj D).homology 0) :=
    finite_scalarFibre_homology S D freeD s 0
  -- (1) ACTUAL initial H0/H1 map injections and source1/target2 give cone1.
  have initialCone : Module.finrank ((Spec (.of S)).residueField s)
      ((CochainComplex.mappingCone (Es.map Φ)).homology 0) = 1 :=
    L2.hZero_mappingCone_eq_one (Es.obj m.P) (Es.obj D) (Es.map Φ)
      initial.1 (facts s).1 initial.2.1 initial.2.2
  -- (2) UPPER semicontinuity of the ACTUAL cone, via canonical tilde/fibre.
  obtain ⟨VS, hsVS, hCone⟩ := L2.nativeTildeCone_exists_open_finrankHZero_le
    S m.P D Φ m.freeFiniteP freeD s
  letI : IsOpenImmersion chart := retainedChart_isOpenImmersion R d
  let V : (Spec (.of R)).Opens :=
    ⟨chart '' (VS : Set (Spec (.of S))), chart.isOpenMap _ VS.isOpen⟩
  refine ⟨V, ⟨s, hsVS, hs⟩, ?_⟩
  intro z hz
  obtain ⟨zS, hzS, rfl⟩ := hz
  let Ez := L2.nativeResidueCochainFunctor S zS
  letI : Module.Finite ((Spec (.of S)).residueField zS) ((Ez.obj m.P).homology 0) :=
    finite_scalarFibre_homology S m.P m.freeFiniteP zS 0
  letI : Module.Finite ((Spec (.of S)).residueField zS) ((Ez.obj D).homology 0) :=
    finite_scalarFibre_homology S D freeD zS 0
  letI : Module.Finite ((Spec (.of S)).residueField zS)
      ((CochainComplex.mappingCone (Ez.map Φ)).homology 0) :=
    L2.nativeTildeCone_finite_fibreHomology S m.P D Φ m.freeFiniteP freeD zS 0
  have bound : Module.finrank ((Spec (.of S)).residueField zS)
      ((CochainComplex.mappingCone (Ez.map Φ)).homology 0) ≤ 1 := by
    have h := hCone zS hzS
    change Module.finrank ((Spec (.of S)).residueField zS)
        ((CochainComplex.mappingCone (Ez.map Φ)).homology 0) ≤
      Module.finrank ((Spec (.of S)).residueField s)
        ((CochainComplex.mappingCone (Es.map Φ)).homology 0) at h
    rw [initialCone] at h
    exact h
  -- (3) Entire ACTUAL face triviality proves target2 at this residue point.
  have targetTwo : Module.finrank ((Spec (.of S)).residueField zS) ((Ez.obj D).homology 0) = 2 :=
    (facts zS).1
  -- (4) ACTUAL cone exactness/rank-nullity forces source H0>=1.
  have sourcePositive := L2.one_le_hZero_of_cone_bound (Ez.obj m.P) (Ez.obj D) (Ez.map Φ)
    targetTwo bound
  rw [← modelHZero_eq_hFiber R q jX jY M U affineU coverU d m zS]
  exact sourcePositive

/-- The exact public cube-fibre lower bound. Genuine affine-chart and
original residue-field transport assemble the four-step two-face cone proof.
No reduced parameter, supplied model/rank/injection or beta-flatness premise. -/
theorem exists_open_cubeFibreHZero_ge_one
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    [IsProper g] [GeometricallyIntegral g]
    (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _)
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
    (T : Over (Spec (.of k))) [IsLocallyNoetherian T.left]
    (M : (pullback (pullback.fst f g ≫ f) T.hom).Modules)
    [M.IsInvertible]
    (hX : Scheme.Pic.map (L6.nativeCubeFaceXR f g T.hom y hy)
      (Scheme.Pic.mk M) = 1)
    (hY : Scheme.Pic.map (L6.nativeCubeFaceYR f g T.hom x hx)
      (Scheme.Pic.mk M) = 1)
    (t : T.left)
    (ht : Scheme.Pic.map
      ((pullback.snd (pullback.fst f g ≫ f) T.hom).fiberι t)
      (Scheme.Pic.mk M) = 1) :
    ∃ V : T.left.Opens, t ∈ V ∧ ∀ z : T.left, z ∈ V →
      let q := pullback.snd (pullback.fst f g ≫ f) T.hom
      letI : (q.fiber z).Over (Spec (T.left.residueField z)) :=
        ⟨q.fiberToSpecResidueField z⟩
      1 ≤ Module.finrank (T.left.residueField z)
        (((Scheme.Modules.pullback (q.fiberι z)).obj M).H 0) := by
  classical
  letI : M.IsQuasicoherent := SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u} ‹M.IsInvertible›
  let q := pullback.snd (pullback.fst f g ≫ f) T.hom
  letI : IsProper q := (L4.CubeFaces.nativeCubeFamily_geometry f g T.hom).1
  obtain ⟨W, affineW, htW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
  let R := Γ(T.left, W)
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨W, affineW⟩
  let chart : Spec R ⟶ T.left := affineW.fromSpec
  let a := chart ≫ T.hom
  let Qmap := ResidueCartesian.familyMap (pullback.fst f g ≫ f) T.hom chart
  let qR := pullback.snd (pullback.fst f g ≫ f) a
  let MR := (Scheme.Modules.pullback Qmap).obj M
  letI : MR.IsInvertible := Scheme.Modules.isInvertible_pullback Qmap M
  have hChart : IsPullback Qmap qR q chart :=
    ResidueCartesian.familyMap_isPullback (pullback.fst f g ≫ f) T.hom chart
  have htRange : t ∈ Set.range chart := by
    rw [affineW.range_fromSpec]
    exact htW
  obtain ⟨tR, htR⟩ := htRange
  have hXR : Scheme.Pic.map (L6.nativeCubeFaceXR f g a y hy) (Scheme.Pic.mk MR) = 1 := by
    change Scheme.Pic.map (L6.nativeCubeFaceXR f g a y hy)
      (Scheme.Pic.mk ((Scheme.Modules.pullback Qmap).obj M)) = 1
    rw [← Scheme.Pic.map_mk, ← Scheme.Pic.map_comp,
      ResidueCartesian.faceX_family_square f g T.hom chart y hy,
      Scheme.Pic.map_comp, hX, Scheme.Pic.map_one]
  have hYR : Scheme.Pic.map (L6.nativeCubeFaceYR f g a x hx) (Scheme.Pic.mk MR) = 1 := by
    change Scheme.Pic.map (L6.nativeCubeFaceYR f g a x hx)
      (Scheme.Pic.mk ((Scheme.Modules.pullback Qmap).obj M)) = 1
    rw [← Scheme.Pic.map_mk, ← Scheme.Pic.map_comp,
      ResidueCartesian.faceY_family_square f g T.hom chart x hx,
      Scheme.Pic.map_comp, hY, Scheme.Pic.map_one]
  let K := (Spec R).residueField tR
  let qb := qR.fiberToSpecResidueField tR
  let ab := qR.fiberι tR ≫ Qmap
  let bb := (Spec R).fromSpecResidueField tR ≫ chart
  have fibreSquare : IsPullback ab qb q bb :=
    (IsPullback.of_hasPullback qR ((Spec R).fromSpecResidueField tR)).paste_horiz hChart
  have imagePoint : bb (IsLocalRing.closedPoint K) = t := by
    change chart ((Spec R).fromSpecResidueField tR (IsLocalRing.closedPoint K)) = t
    exact (congrArg (fun z : Spec R => chart z)
      (Scheme.fromSpecResidueField_apply (X := Spec R) tR (IsLocalRing.closedPoint K))).trans htR
  have initialAtImage : Scheme.Pic.map (q.fiberι (bb (IsLocalRing.closedPoint K)))
      (Scheme.Pic.mk M) = 1 :=
    Eq.mpr (congrArg (fun z : T.left =>
      Scheme.Pic.map (q.fiberι z) (Scheme.Pic.mk M) = 1) imagePoint) ht
  have hInitialComposite : Scheme.Pic.mk ((Scheme.Modules.pullback ab).obj M) = 1 :=
    fieldPicard_trivial_of_residue q bb qb ab fibreSquare.w M initialAtImage
  have htMR : Scheme.Pic.map (qR.fiberι tR) (Scheme.Pic.mk MR) = 1 := by
    change Scheme.Pic.map (qR.fiberι tR) (Scheme.Pic.mk ((Scheme.Modules.pullback Qmap).obj M)) = 1
    rw [← Scheme.Pic.map_mk, ← Scheme.Pic.map_comp, Scheme.Pic.map_mk]
    exact hInitialComposite
  obtain ⟨VR, htVR, positiveR⟩ :=
    exists_open_affine_cubeHZero f g x hx y hy R a MR hXR hYR tR htMR
  letI : IsOpenImmersion chart := inferInstance
  let V : T.left.Opens := ⟨chart '' (VR : Set (Spec R)), chart.isOpenMap _ VR.isOpen⟩
  refine ⟨V, ⟨tR, htVR, htR⟩, ?_⟩
  intro z hz
  obtain ⟨zR, hzR, rfl⟩ := hz
  have originalFibre : MR.hFiber qR 0 zR = M.hFiber q 0 (chart zR) :=
    Scheme.Modules.hFiber_pullback_of_isPullback q M chart Qmap qR hChart 0 zR
  change 1 ≤ M.hFiber q 0 (chart zR)
  rw [← originalFibre]
  exact positiveR zR hzR

end ZInQ.Contrib.CloudR2Poincare.L2.CubeConeFibreIntegration
