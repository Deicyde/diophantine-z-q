import ZInQKernel.Contrib.OneProof.RC.ModelTarget.FormulaMorphism
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Equation
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! The scheme group law on the projective cubic of a unit-discriminant equation over a
noetherian domain, once the cubic is smooth. The identity is `(0 : 1 : 0)`, the
inverse is `(X : -Y - a₁X - a₃Z : Z)`, and the multiplication is glued from Mathlib's
addition law `addXYZ` (attached to the line `Z = 0`) and the second Bosma–Lenstra law
`dblAddXYZ` (attached to `Y = 0`) of Tau Ceti, which do not vanish together at any
pair of field points (W. Bosma and H. W. Lenstra Jr., *Complete systems of two addition
laws for elliptic curves*, J. Number Theory 53 (1995), Theorem 2, UNVERIFIED). The group
axioms are checked at field points (the products of the smooth cubic are reduced and the
cubic is separated), where they are Mathlib's group law. On the spot (c): the manuscript
constructs nothing here. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open WeierstrassCurve
open scoped WeierstrassCurve.Projective

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The projective cubic as a scheme over the base. -/
abbrev cubic : Over (Spec (.of R)) := Over.mk (projStructure W)

/-- The spectrum of a field over the base. -/
abbrev fieldPt {F : Type} [Field F] (g : R →+* F) : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom g))

/-- The affine value of a field point of the cubic over the base. -/
def val {F : Type} [Field F] {g : R →+* F} (p : fieldPt g ⟶ cubic W) : (W.map g).toAffine.Point :=
  fieldValue W g p.left (Over.w p)

theorem cubicHom_ext [W.IsElliptic] {T : Over (Spec (.of R))} [IsReduced T.left]
    {f f' : T ⟶ cubic W}
    (h : ∀ (F : Type) [Field F] (g : R →+* F) (p : fieldPt g ⟶ T), val W (p ≫ f) = val W (p ≫ f')) :
    f = f' := by
  apply Over.OverMorphism.ext
  apply eq_of_fieldValues W T.hom f.left f'.left (Over.w f) (Over.w f')
  intro F _ g p hp
  exact h F g (Over.homMk p hp)

/-! ### The identity -/

theorem origin_equation {A : Type} [CommRing A] (g : R →+* A) :
    (W.toProjective.map g).Equation ![0, 1, 0] := Projective.equation_zero

omit [CommRing R] in
theorem origin_unit {A : Type} [CommRing A] : IsUnit ((![0, 1, 0] : Fin 3 → A) 1) := isUnit_one

/-- The identity section `(0 : 1 : 0)`. -/
def cubicOne : 𝟙_ (Over (Spec (.of R))) ⟶ cubic W :=
  Over.homMk (chartMorphism W (RingHom.id R) ![0, 1, 0] (origin_equation W _) 1 origin_unit) (by
    change _ ≫ projStructure W = 𝟙 _
    rw [chartMorphism_structure]
    simp)

theorem origin_map {F : Type} [Field F] (g : R →+* F) :
    Spec.map (CommRingCat.ofHom g) ≫
        chartMorphism W (RingHom.id R) ![0, 1, 0] (origin_equation W _) 1 origin_unit =
      chartMorphism W g ![0, 1, 0] (origin_equation W g) 1 origin_unit := by
  unfold chartMorphism
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine congrArg CommRingCat.ofHom ?_
  apply chartEval_eq_of
  · ext r
    simp [chartEval_const]
  · intro j
    simp only [RingHom.coe_comp, Function.comp_apply]
    have := chartEval_ratio W (RingHom.id R) ![0, 1, 0] (origin_equation W _) 1 origin_unit j
    rw [show (![0, 1, 0] : Fin 3 → R) 1 = 1 from rfl, _root_.one_mul] at this
    rw [this, show (![0, 1, 0] : Fin 3 → F) 1 = 1 from rfl, _root_.one_mul]
    fin_cases j <;> simp

theorem val_one {F : Type} [Field F] (g : R →+* F) :
    val W (toUnit (fieldPt g) ≫ cubicOne W) = 0 := by
  have e : (toUnit (fieldPt g) ≫ cubicOne W).left =
      chartMorphism W g ![0, 1, 0] (origin_equation W g) 1 origin_unit := origin_map W g
  rw [val, fieldValue_congr W g e _ (chartMorphism_structure ..), fieldValue_chartMorphism]
  exact Projective.Point.toAffine_zero

/-! ### The inverse -/

theorem neg_map {A B : Type} [CommRing A] [CommRing B] (g : R →+* A) (φ : A →+* B)
    (v : Fin 3 → A) : φ ∘ (W.toProjective.map g).neg v = (W.toProjective.map (φ.comp g)).neg (φ ∘ v) := by
  funext i
  fin_cases i <;> simp [Projective.neg, Projective.negY]

theorem equation_neg' {A : Type} [CommRing A] (W' : WeierstrassCurve.Projective A) {v : Fin 3 → A}
    (hv : W'.Equation v) : W'.Equation (W'.neg v) := by
  rw [Projective.equation_iff] at hv ⊢
  simp only [Projective.neg, Projective.negY, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination hv

variable [W.IsElliptic]

theorem exists_cubicInv [IsReduced (cubic W).left] :
    ∃ (m : (cubic W).left ⟶ Proj W.toProjective.grading) (hm : m ≫ projStructure W = (cubic W).hom),
      Computes W (cubic W).left (cubic W).hom ![𝟙 _] (fun _ => by simp)
        (fun _ _ _ P => -P 0) (𝟙 _) m (by rw [hm, Category.id_comp]) := by
  classical
  refine morphism_of_formulas W (cubic W).left (cubic W).hom ![𝟙 _] (fun _ => by simp)
    (fun _ _ _ P => -P 0) (I := Unit) (fun A _ g _ v => (W.toProjective.map g).neg (v 0))
    (fun A B _ _ g φ _ v => neg_map W g φ (v 0))
    (fun A _ g _ v hv => equation_neg' _ (hv 0)) ?_
  intro F _ g v hv
  have hn := Projective.nonsingular_neg (hv 0)
  exact ⟨⟨(), Projective.ne_zero_of_nonsingular hn⟩, fun _ _ => Projective.Point.toAffine_neg (hv 0)⟩

/-- The inverse of the cubic. -/
def cubicInv [IsReduced (cubic W).left] : cubic W ⟶ cubic W :=
  Over.homMk (exists_cubicInv W).choose (exists_cubicInv W).choose_spec.choose

theorem val_inv [IsReduced (cubic W).left] {F : Type} [Field F] (g : R →+* F)
    (p : fieldPt g ⟶ cubic W) : val W (p ≫ cubicInv W) = -val W p := by
  have h := (exists_cubicInv W).choose_spec.choose_spec F g p.left
    (by rw [Category.id_comp]; exact Over.w p)
  change fieldValue W g (p.left ≫ (exists_cubicInv W).choose) _ = _
  rw [h]
  exact congrArg Neg.neg (fieldValue_congr W g (by simp) _ _)

/-! ### The multiplication -/

/-- The two Bosma–Lenstra laws. -/
def addLaws {A : Type} [CommRing A] (g : R →+* A) (b : Bool) (v : Fin 2 → Fin 3 → A) : Fin 3 → A :=
  if b then (W.toProjective.map g).addXYZ (v 0) (v 1) else (W.toProjective.map g).dblAddXYZ (v 0) (v 1)

omit [W.IsElliptic] in
theorem addLaws_map {A B : Type} [CommRing A] [CommRing B] (g : R →+* A) (φ : A →+* B) (b : Bool)
    (v : Fin 2 → Fin 3 → A) : φ ∘ addLaws W g b v = addLaws W (φ.comp g) b (fun a => φ ∘ v a) := by
  cases b
  · simp only [addLaws, Bool.false_eq_true, ↓reduceIte]
    rw [← Projective.map_dblAddXYZ]
    rfl
  · simp only [addLaws, ↓reduceIte]
    rw [← Projective.map_addXYZ]
    rfl

theorem exists_cubicMul [IsReduced (cubic W ⊗ cubic W).left] :
    ∃ (m : (cubic W ⊗ cubic W).left ⟶ Proj W.toProjective.grading)
      (hm : m ≫ projStructure W = (cubic W ⊗ cubic W).hom),
      Computes W (cubic W ⊗ cubic W).left (cubic W ⊗ cubic W).hom
        ![(fst (cubic W) (cubic W)).left, (snd (cubic W) (cubic W)).left]
        (fun a => by
          fin_cases a
          · exact Over.w _
          · exact (Over.w _).trans (Over.w (fst (cubic W) (cubic W))).symm)
        (fun F _ _ P => letI := Classical.decEq F; P 0 + P 1) (𝟙 _) m (by rw [hm, Category.id_comp]) := by
  classical
  refine morphism_of_formulas W _ _ _ _ _ (I := Bool) (fun A _ g b v => addLaws W g b v)
    (fun A B _ _ g φ b v => addLaws_map W g φ b v) ?_ ?_
  · intro A _ g b v hv
    cases b
    · exact Projective.Equation.dblAddXYZ (hv 0) (hv 1)
    · exact Projective.Equation.addXYZ (hv 0) (hv 1)
  · intro F _ g v hv
    refine ⟨?_, ?_⟩
    · rcases Projective.addXYZ_ne_zero_or_dblAddXYZ_ne_zero (hv 0) (hv 1) with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · intro b hb
      let _ := Classical.decEq F
      have hadd := Projective.Point.toAffine_add (hv 0) (hv 1)
      cases b
      · rw [← hadd]
        exact Projective.Point.toAffine_of_equiv (Projective.dblAddXYZ_equiv_add (hv 0) (hv 1) hb)
      · rw [← hadd]
        simp only [addLaws, ↓reduceIte] at hb ⊢
        rw [Projective.add_of_addXYZ_ne_zero hb]

/-- The multiplication of the cubic. -/
def cubicMul [IsReduced (cubic W ⊗ cubic W).left] : cubic W ⊗ cubic W ⟶ cubic W :=
  Over.homMk (exists_cubicMul W).choose (exists_cubicMul W).choose_spec.choose

theorem val_mul [IsReduced (cubic W ⊗ cubic W).left] {F : Type} [Field F] [DecidableEq F]
    (g : R →+* F)
    (p q : fieldPt g ⟶ cubic W) : val W (lift p q ≫ cubicMul W) = val W p + val W q := by
  have h := (exists_cubicMul W).choose_spec.choose_spec F g (lift p q).left
    (by rw [Category.id_comp]; exact Over.w (lift p q))
  beta_reduce at h
  rw [show Classical.decEq F = ‹DecidableEq F› from Subsingleton.elim _ _] at h
  change fieldValue W g ((lift p q).left ≫ (exists_cubicMul W).choose) _ = _
  rw [h]
  have h0 : ((lift p q).left ≫ 𝟙 _) ≫ (fst (cubic W) (cubic W)).left = p.left := by
    rw [Category.comp_id]; exact congrArg (fun u => u.left) (lift_fst p q)
  have h1 : ((lift p q).left ≫ 𝟙 _) ≫ (snd (cubic W) (cubic W)).left = q.left := by
    rw [Category.comp_id]; exact congrArg (fun u => u.left) (lift_snd p q)
  congr 1
  · exact fieldValue_congr W g h0 _ _
  · exact fieldValue_congr W g h1 _ _

#print axioms cubicHom_ext
#print axioms val_one
#print axioms val_inv
#print axioms val_mul

end ZInQ.Manuscript.RC.ModelTarget
