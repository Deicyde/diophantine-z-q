import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.DescentDatum

/-!
# Descent data and pullback-preserving functors

The morphism on the universal double overlap defines the transport on every
test object in the target category. The unit and cocycle are checked on the
images of the universal objects, including the triple overlap.
-/

open CategoryTheory CategoryTheory.Limits

namespace ZInQ.Manuscript.T10Proetale

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {C D : Type*} [Category* C] [Category* D] [HasPullbacks C]
    (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    {A B : C} {p : A ⟶ B} {R : Over A} (d : Over.DescentDatum p R)

private theorem mappedSquare {Y Z W : C} (a : Z ⟶ W) (b : Y ⟶ W) :
    IsPullback (F.map (pullback.fst b a)) (F.map (pullback.snd b a))
      (F.map b) (F.map a) :=
  Functor.map_isPullback F (IsPullback.of_hasPullback b a)

private abbrev transportCondition {T : D} (x : T ⟶ F.obj R.left) (v : T ⟶ F.obj A) :=
  x ≫ F.map (R.hom ≫ p) = v ≫ F.map p

private def transition {T : D} (x : T ⟶ F.obj R.left) (v : T ⟶ F.obj A)
    (w : transportCondition (p := p) F x v) : T ⟶ F.obj R.left :=
  (mappedSquare F p (R.hom ≫ p)).lift x v w ≫ F.map d.toHom

private theorem transition_congr {T : D} {x x' : T ⟶ F.obj R.left} {v v' : T ⟶ F.obj A}
    (hx : x = x') (hv : v = v') {w : transportCondition (p := p) F x v}
    {w' : transportCondition (p := p) F x' v'} :
    transition F d x v w = transition F d x' v' w' := by
  cases hx
  cases hv
  rfl

private theorem transition_over {T : D} (x : T ⟶ F.obj R.left) (v : T ⟶ F.obj A)
    (w : transportCondition (p := p) F x v) :
    transition F d x v w ≫ F.map R.hom = v := by
  have hw : d.toHom ≫ R.hom = pullback.snd (R.hom ≫ p) p := by
    exact Over.w (d.transport _ _ _ Over.DescentDatum.universalPoint)
  rw [transition, Category.assoc, ← F.map_comp, hw, (mappedSquare F p _).lift_snd]

private theorem transition_over_condition {T : D} (x : T ⟶ F.obj R.left) (v : T ⟶ F.obj A)
    (w : transportCondition (p := p) F x v) :
    transition F d x v w ≫ F.map (R.hom ≫ p) = v ≫ F.map p :=
  calc
    _ = transition F d x v w ≫ (F.map R.hom ≫ F.map p) :=
      congrArg (transition F d x v w ≫ ·) (F.map_comp R.hom p)
    _ = _ := by rw [← Category.assoc, transition_over]

private theorem transition_comp {T T' : D} (h : T' ⟶ T)
    (x : T ⟶ F.obj R.left) (v : T ⟶ F.obj A) (w : transportCondition (p := p) F x v) :
    transition F d (h ≫ x) (h ≫ v) (by simpa only [transportCondition, Category.assoc] using congrArg (h ≫ ·) w) =
      h ≫ transition F d x v w := by
  simp only [transition, ← Category.assoc]
  congr 1
  apply (mappedSquare F p _).hom_ext <;>
    simp only [IsPullback.lift_fst, IsPullback.lift_snd, Category.assoc]

private theorem transition_image {T : C} (u v : T ⟶ A) (e : u ≫ p = v ≫ p)
    (x : Over.mk u ⟶ R) :
    transition F d (F.map x.left) (F.map v) (by
      have hx : x.left ≫ R.hom = u := Over.w x
      rw [transportCondition, ← F.map_comp, ← Category.assoc, hx, e, F.map_comp]) =
      F.map (d.transport u v e x).left := by
  rw [d.transport_left_eq_lift_toHom]
  refine (congrArg (· ≫ F.map d.toHom) ?_).trans (F.map_comp _ _).symm
  apply (mappedSquare F p _).hom_ext <;>
    simp only [IsPullback.lift_fst, IsPullback.lift_snd, ← F.map_comp,
      pullback.lift_fst, pullback.lift_snd]

private theorem transition_self {T : D} (x : T ⟶ F.obj R.left) :
    transition F d x (x ≫ F.map R.hom) (by simp [transportCondition]) = x := by
  have h := transition_image F d R.hom R.hom rfl
    (Over.homMk (𝟙 R.left) (Category.id_comp R.hom))
  have h' : transition F d (𝟙 (F.obj R.left)) (F.map R.hom) (by simp [transportCondition]) =
      𝟙 (F.obj R.left) := by
    have h₀ := h.trans (congrArg (fun t : Over.mk R.hom ⟶ R => F.map t.left)
      (d.transport_self R.hom _))
    refine Eq.trans ?_ (h₀.trans (F.map_id _))
    exact transition_congr F d (F.map_id _).symm rfl
  have h'' := transition_comp F d x (𝟙 (F.obj R.left)) (F.map R.hom)
    (by simp [transportCondition])
  simpa only [Category.comp_id, h'] using h''

private theorem transition_image_trans {T : C} (x : T ⟶ R.left) (v w : T ⟶ A)
    (hv : x ≫ (R.hom ≫ p) = v ≫ p) (hw : v ≫ p = w ≫ p) :
    transition F d (transition F d (F.map x) (F.map v) (by
      rw [transportCondition, ← F.map_comp, hv, F.map_comp])) (F.map w) (by
      exact (transition_over_condition F d ..).trans (by rw [← F.map_comp, hw, F.map_comp])) =
      transition F d (F.map x) (F.map w) (by
        rw [transportCondition, ← F.map_comp, hv, hw, F.map_comp]) := by
  let h : (x ≫ R.hom) ≫ p = v ≫ p := by simpa only [Category.assoc] using hv
  let q : Over.mk (x ≫ R.hom) ⟶ R := Over.homMk x rfl
  let y := d.transport (x ≫ R.hom) v h q
  have h₁ := transition_image F d (x ≫ R.hom) v h q
  have h₂ := transition_image F d v w hw y
  have h₃ := transition_image F d (x ≫ R.hom) w (h.trans hw) q
  change transition F d (F.map x) (F.map v) _ = F.map y.left at h₁
  change transition F d (F.map x) (F.map w) _ = F.map (d.transport _ _ _ q).left at h₃
  simp only [h₁, h₂, h₃, y, d.transport_transport]

private theorem transition_trans {T : D} (x : T ⟶ F.obj R.left) (v w : T ⟶ F.obj A)
    (hv : transportCondition (p := p) F x v) (hw : v ≫ F.map p = w ≫ F.map p) :
    transition F d (transition F d x v hv) w (by
      exact (transition_over_condition F d ..).trans hw) =
      transition F d x w (hv.trans hw) := by
  let q := pullback.snd (R.hom ≫ p) p
  let q' := pullback.fst (R.hom ≫ p) p
  let g := (mappedSquare F p (R.hom ≫ p)).lift x v hv
  let k := (mappedSquare F p (q ≫ p)).lift g w (by
    rw [F.map_comp, ← Category.assoc, IsPullback.lift_snd, hw])
  let a := pullback.fst (q ≫ p) p ≫ q'
  let b := pullback.fst (q ≫ p) p ≫ q
  let c := pullback.snd (q ≫ p) p
  have ha : k ≫ F.map a = x := by
    simp only [a, F.map_comp, ← Category.assoc, k, g, q', IsPullback.lift_fst]
  have hb : k ≫ F.map b = v := by
    simp only [b, F.map_comp, ← Category.assoc, k, g, q, IsPullback.lift_fst, IsPullback.lift_snd]
  have hc : k ≫ F.map c = w := IsPullback.lift_snd ..
  have hab : a ≫ (R.hom ≫ p) = b ≫ p := by simp [a, b, q, q', pullback.condition]
  have hbc : b ≫ p = c ≫ p := by simp [b, c, pullback.condition]
  have htop := congrArg (k ≫ ·) (transition_image_trans F d a b c hab hbc)
  have w₁ : transportCondition (p := p) F (F.map a) (F.map b) := by
    rw [transportCondition, ← F.map_comp, hab, F.map_comp]
  have w₂ : transportCondition (p := p) F (F.map a) (F.map c) := by
    rw [transportCondition, ← F.map_comp, hab, hbc, F.map_comp]
  have w₃ : transportCondition (p := p) F (transition F d (F.map a) (F.map b) w₁) (F.map c) :=
    (transition_over_condition F d ..).trans (by rw [← F.map_comp, hbc, F.map_comp])
  have hmid : k ≫ transition F d (F.map a) (F.map b) w₁ = transition F d x v hv :=
    (transition_comp F d k _ _ w₁).symm.trans (transition_congr F d ha hb)
  exact (transition_congr F d hmid.symm hc.symm).trans
    ((transition_comp F d k _ _ w₃).trans
      (htop.trans ((transition_comp F d k _ _ w₂).symm.trans (transition_congr F d ha hc))))

/-- A pullback-preserving functor takes a descent datum to one on the image
object, including its transport for tests outside the original category. -/
def mapDescentDatum : Over.DescentDatum (F.map p) ((Over.post F).obj R) where
  transport u v e q :=
    Over.homMk (transition F d q.left v (by
      rw [transportCondition, F.map_comp, ← Category.assoc]
      exact (congrArg (· ≫ F.map p) (Over.w q)).trans e))
      (transition_over ..)
  transport_homMk_comp h u v e q := by
    apply Over.OverMorphism.ext
    exact transition_comp F d h q.left v (by
      rw [transportCondition, F.map_comp, ← Category.assoc]
      exact (congrArg (· ≫ F.map p) (Over.w q)).trans e)
  transport_self u q := by
    apply Over.OverMorphism.ext
    have h := Over.w q
    change q.left ≫ F.map R.hom = u at h
    have eq := transition_self F d q.left
    change transition F d q.left u _ = q.left
    simpa only [h] using eq
  transport_transport u v w e₁ e₂ q := by
    apply Over.OverMorphism.ext
    exact transition_trans F d q.left v w (by
      rw [transportCondition, F.map_comp, ← Category.assoc]
      exact (congrArg (· ≫ F.map p) (Over.w q)).trans e₁) e₂

/-- The transported datum agrees on the images of the original test points. -/
theorem mapDescentDatum_transport_image {T : C} (u v : T ⟶ A) (e : u ≫ p = v ≫ p)
    (q : Over.mk u ⟶ R) (eq : F.map u ≫ F.map p = F.map v ≫ F.map p) :
    ((mapDescentDatum F d).transport (F.map u) (F.map v) eq ((Over.post F).map q)).left =
      F.map (d.transport u v e q).left :=
  transition_image F d u v e q

end
end ZInQ.Manuscript.T10Proetale
