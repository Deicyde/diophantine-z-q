/-
H5 FIX EDITION STEP-F2 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/TwistSelection.lean (sha256 66ea81d2c75d3ff30e49c31cbd52f027cacbe4df5af6b03437b6dd183babe2c8).
Body change relative to the base: ONLY P5, the line `open CategoryTheory.CartesianMonoidalCategory` inserted before `namespace` (record step-fix2/FIX_RECORD_STEP_F2.json). Any header below describes the BASE edition.
-/
/-
H5 lane3 Step 1, sub-gap T `TwistSelectionFromSquare` PROVED. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u, any characteristic. Only W07 native tensor/dual/pullback
isomorphisms and Mathlib monoid-object identities are used; there are no Facts.

The proof:
1. Translation identities, at the level of `Over` morphisms and then `.left`:
   `t_x ≫ t_z = t_{x*z}`, `t_1 = 𝟙`, and `t_y ≫ j = j ≫ t_{y ≫ j}` for a monoid hom `j`.
2. The isomorphism-class calculus `Nonempty (L ≅ M)` for W07 invertible sheaves: associativity,
   commutativity, units, cancellation by an invertible sheaf (via `tensorObjDualIsoUnit`), and
   compatibility of pullback with `⊗`, `ᵛ` and `𝟙_` (`pullbackTensorObjIso`, `pullbackDualIso`,
   `pullbackObjUnitIso`, Mathlib `pullbackComp`/`pullbackId`).
3. I5a (the square) gives `t_y^*P_z ≅ P_z`, where `P_z = t_z^*N ⊗ Nᵛ`.
4. `z := 1` if `j^*M` is nontrivial, else `z := j w`. In either case `j^*(M ⊗ P_z)` is nontrivial.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

open CategoryTheory.CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step1

section Translations

variable {K : Type u} [Field K]

theorem translOver_mul (A : Grp (Over (Spec (CommRingCat.of K)))) (x z : Pt K ⟶ A.X) :
    (lift (𝟙 A.X) (toUnit A.X ≫ x) ≫ μ[A.X]) ≫ (lift (𝟙 A.X) (toUnit A.X ≫ z) ≫ μ[A.X]) =
      lift (𝟙 A.X) (toUnit A.X ≫ (x * z)) ≫ μ[A.X] := by
  rw [← MonObj.Hom.mul_def, ← MonObj.Hom.mul_def, ← MonObj.Hom.mul_def,
    MonObj.comp_mul (𝟙 A.X * (toUnit A.X ≫ x)) (𝟙 A.X) (toUnit A.X ≫ z),
    Category.comp_id, comp_toUnit_assoc, mul_assoc, ← MonObj.comp_mul (toUnit A.X) x z]

theorem transl_mul (A : Grp (Over (Spec (CommRingCat.of K)))) (x z : Pt K ⟶ A.X) :
    transl A x ≫ transl A z = transl A (x * z) := by
  simpa only [transl, Over.comp_left] using congrArg (fun φ => φ.left) (translOver_mul A x z)

theorem transl_one (A : Grp (Over (Spec (CommRingCat.of K)))) :
    transl A 1 = 𝟙 A.X.left := by
  have h : lift (𝟙 A.X) (toUnit A.X ≫ (1 : Pt K ⟶ A.X)) ≫ μ[A.X] = 𝟙 A.X := by
    rw [← MonObj.Hom.mul_def, MonObj.comp_one, mul_one]
  simpa only [transl, Over.id_left] using congrArg (fun φ => φ.left) h

theorem translOver_hom (A Y : Grp (Over (Spec (CommRingCat.of K)))) (j : Y.X ⟶ A.X) [IsMonHom j]
    (y : Pt K ⟶ Y.X) :
    (lift (𝟙 Y.X) (toUnit Y.X ≫ y) ≫ μ[Y.X]) ≫ j =
      j ≫ (lift (𝟙 A.X) (toUnit A.X ≫ (y ≫ j)) ≫ μ[A.X]) := by
  rw [← MonObj.Hom.mul_def, ← MonObj.Hom.mul_def, MonObj.mul_comp,
    MonObj.comp_mul j (𝟙 A.X) (toUnit A.X ≫ (y ≫ j)),
    Category.id_comp, Category.comp_id, Category.assoc, comp_toUnit_assoc]

theorem transl_hom (A Y : Grp (Over (Spec (CommRingCat.of K)))) (j : Y.X ⟶ A.X) [IsMonHom j]
    (y : Pt K ⟶ Y.X) :
    transl Y y ≫ j.left = j.left ≫ transl A (y ≫ j) := by
  simpa only [transl, Over.comp_left] using congrArg (fun φ => φ.left) (translOver_hom A Y j y)

end Translations

section IsoCalculus

variable {X : Scheme.{u}}

/-- Isomorphism of module sheaves, as a Prop. -/
abbrev Iso' (L M : X.Modules) : Prop := Nonempty (L ≅ M)

theorem iso'_refl (L : X.Modules) : Iso' L L := ⟨Iso.refl _⟩
theorem Iso'.symm {L M : X.Modules} (h : Iso' L M) : Iso' M L := ⟨h.some.symm⟩
theorem Iso'.trans {L M N : X.Modules} (h : Iso' L M) (h' : Iso' M N) : Iso' L N :=
  ⟨h.some ≪≫ h'.some⟩
theorem Iso'.tensor {A B C D : X.Modules} (h : Iso' A B) (h' : Iso' C D) :
    Iso' (A ⊗ C) (B ⊗ D) := ⟨tensorIso h.some h'.some⟩
theorem iso'_assoc (A B C : X.Modules) : Iso' ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) := ⟨α_ A B C⟩
theorem iso'_comm (A B : X.Modules) : Iso' (A ⊗ B) (B ⊗ A) := ⟨β_ A B⟩
theorem iso'_unit_left (A : X.Modules) : Iso' (𝟙_ X.Modules ⊗ A) A := ⟨λ_ A⟩
theorem iso'_unit_right (A : X.Modules) : Iso' (A ⊗ 𝟙_ X.Modules) A := ⟨ρ_ A⟩
theorem iso'_dual (A : X.Modules) [A.IsInvertible] : Iso' (A ⊗ Scheme.Modules.dual A) (𝟙_ _) :=
  ⟨Scheme.Modules.tensorObjDualIsoUnit A⟩

/-- `(a ⊗ b) ⊗ (c ⊗ d) ≅ (a ⊗ c) ⊗ (b ⊗ d)`. -/
theorem iso'_interchange (a b c d : X.Modules) :
    Iso' ((a ⊗ b) ⊗ (c ⊗ d)) ((a ⊗ c) ⊗ (b ⊗ d)) :=
  (iso'_assoc a b (c ⊗ d)).trans <|
    ((iso'_refl a).tensor ((iso'_assoc b c d).symm)).trans <|
      ((iso'_refl a).tensor ((iso'_comm b c).tensor (iso'_refl d))).trans <|
        ((iso'_refl a).tensor (iso'_assoc c b d)).trans (iso'_assoc a c (b ⊗ d)).symm

/-- Cancellation of an invertible factor. -/
theorem Iso'.cancel_right {A B : X.Modules} (C : X.Modules) [C.IsInvertible]
    (h : Iso' (A ⊗ C) (B ⊗ C)) : Iso' A B :=
  (iso'_unit_right A).symm.trans <|
    ((iso'_refl A).tensor (iso'_dual C).symm).trans <|
      (iso'_assoc A C _).symm.trans <|
        (h.tensor (iso'_refl _)).trans <|
          (iso'_assoc B C _).trans <|
            ((iso'_refl B).tensor (iso'_dual C)).trans (iso'_unit_right B)

/-- `T ⊗ Dᵛ ≅ 𝟙` forces `T ≅ D`, for an invertible `D`. -/
theorem Iso'.of_tensor_dual_unit {T D : X.Modules} [D.IsInvertible]
    (h : Iso' (T ⊗ Scheme.Modules.dual D) (𝟙_ X.Modules)) : Iso' T D :=
  Iso'.cancel_right (Scheme.Modules.dual D) <|
    h.trans ((iso'_dual D).symm)

end IsoCalculus

section Pullbacks

variable {X Z W : Scheme.{u}}

theorem iso'_pb_comp (f : W ⟶ Z) (g : Z ⟶ X) (F : X.Modules) :
    Iso' ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj F))
      ((Scheme.Modules.pullback (f ≫ g)).obj F) := ⟨(Scheme.Modules.pullbackComp f g).app F⟩

theorem iso'_pb_congr {f g : Z ⟶ X} (h : f = g) (F : X.Modules) :
    Iso' ((Scheme.Modules.pullback f).obj F) ((Scheme.Modules.pullback g).obj F) := by
  subst h; exact iso'_refl _

theorem iso'_pb_tensor (f : Z ⟶ X) (M N : X.Modules) :
    Iso' ((Scheme.Modules.pullback f).obj (M ⊗ N))
      ((Scheme.Modules.pullback f).obj M ⊗ (Scheme.Modules.pullback f).obj N) :=
  ⟨Scheme.Modules.pullbackTensorObjIso f M N⟩

theorem iso'_pb_dual (f : Z ⟶ X) (M : X.Modules) [M.IsInvertible] :
    Iso' ((Scheme.Modules.pullback f).obj (Scheme.Modules.dual M))
      (Scheme.Modules.dual ((Scheme.Modules.pullback f).obj M)) :=
  ⟨Scheme.Modules.pullbackDualIso f M⟩

theorem Iso'.pb (f : Z ⟶ X) {M N : X.Modules} (h : Iso' M N) :
    Iso' ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ⟨(Scheme.Modules.pullback f).mapIso h.some⟩

theorem iso'_pb_unit (f : Z ⟶ X) :
    Iso' ((Scheme.Modules.pullback f).obj (𝟙_ X.Modules)) (𝟙_ Z.Modules) :=
  ⟨Scheme.Modules.pullbackObjUnitIso f⟩

theorem iso'_pb_id (F : X.Modules) : Iso' ((Scheme.Modules.pullback (𝟙 X)).obj F) F :=
  ⟨(Scheme.Modules.pullbackId X).app F⟩

end Pullbacks

/-- T, PROVED from I5a. -/
theorem twistSelectionFromSquare : TwistSelectionFromSquare.{u} := by
  intro hsq K _ _ A Y _ _ j _ M N _ _ w hw hM
  -- (3) translation invariance of `P_z`
  have hP : ∀ (z y : Pt K ⟶ A.X),
      Iso' ((Scheme.Modules.pullback (transl A y)).obj
          ((Scheme.Modules.pullback (transl A z)).obj N ⊗ Scheme.Modules.dual N))
        ((Scheme.Modules.pullback (transl A z)).obj N ⊗ Scheme.Modules.dual N) := by
    intro z y
    -- LHS ≅ t_{y*z}^*N ⊗ (t_y^*N)ᵛ
    have h1 : Iso' ((Scheme.Modules.pullback (transl A y)).obj
          ((Scheme.Modules.pullback (transl A z)).obj N ⊗ Scheme.Modules.dual N))
        ((Scheme.Modules.pullback (transl A (y * z))).obj N ⊗
          Scheme.Modules.dual ((Scheme.Modules.pullback (transl A y)).obj N)) :=
      (iso'_pb_tensor _ _ _).trans <|
        (((iso'_pb_comp _ _ N).trans (iso'_pb_congr (transl_mul A y z) N)).tensor
          (iso'_pb_dual _ N))
    refine h1.trans ?_
    -- cancel `C := t_y^*N ⊗ N`, using the square `t_{y*z}^*N ⊗ N ≅ t_y^*N ⊗ t_z^*N`
    have sq := hsq A N y z
    refine Iso'.cancel_right ((Scheme.Modules.pullback (transl A y)).obj N ⊗ N) ?_
    have hL : Iso' (((Scheme.Modules.pullback (transl A (y * z))).obj N ⊗
          Scheme.Modules.dual ((Scheme.Modules.pullback (transl A y)).obj N)) ⊗
          ((Scheme.Modules.pullback (transl A y)).obj N ⊗ N))
        ((Scheme.Modules.pullback (transl A y)).obj N ⊗ (Scheme.Modules.pullback (transl A z)).obj N) :=
      ((iso'_refl _).tensor (iso'_comm _ _)).trans <|
        (iso'_interchange _ _ _ _).trans <|
          ((iso'_refl _).tensor ((iso'_comm _ _).trans (iso'_dual _))).trans <|
            (iso'_unit_right _).trans sq
    have hR : Iso' (((Scheme.Modules.pullback (transl A z)).obj N ⊗ Scheme.Modules.dual N) ⊗
          ((Scheme.Modules.pullback (transl A y)).obj N ⊗ N))
        ((Scheme.Modules.pullback (transl A y)).obj N ⊗ (Scheme.Modules.pullback (transl A z)).obj N) :=
      (iso'_interchange _ _ _ _).trans <|
        ((iso'_refl _).tensor ((iso'_comm _ _).trans (iso'_dual N))).trans <|
          (iso'_unit_right _).trans (iso'_comm _ _)
    exact hL.trans hR.symm
  -- (2) `L' = M ⊗ P_z` is invariant under translations by points of `Y`
  have hL' : ∀ (z : Pt K ⟶ A.X) (y : Pt K ⟶ Y.X),
      Iso' ((Scheme.Modules.pullback (transl A (y ≫ j))).obj (twist A M N z)) (twist A M N z) :=
    fun z y => (iso'_pb_tensor _ _ _).trans ((hM y).tensor (hP z (y ≫ j)))
  -- restriction to `Y` commutes with translation
  have hres : ∀ (F : A.X.left.Modules) (y : Pt K ⟶ Y.X),
      Iso' ((Scheme.Modules.pullback (transl Y y)).obj ((Scheme.Modules.pullback j.left).obj F))
        ((Scheme.Modules.pullback j.left).obj ((Scheme.Modules.pullback (transl A (y ≫ j))).obj F)) :=
    fun F y => (iso'_pb_comp _ _ F).trans <|
      (iso'_pb_congr (transl_hom A Y j y) F).trans (iso'_pb_comp _ _ F).symm
  have hYinv : ∀ (z : Pt K ⟶ A.X) (y : Pt K ⟶ Y.X),
      Iso' ((Scheme.Modules.pullback (transl Y y)).obj
          ((Scheme.Modules.pullback j.left).obj (twist A M N z)))
        ((Scheme.Modules.pullback j.left).obj (twist A M N z)) :=
    fun z y => (hres _ y).trans ((hL' z y).pb _)
  -- (4) choice of `z`
  by_cases hMtriv : Iso' ((Scheme.Modules.pullback j.left).obj M) (𝟙_ Y.X.left.Modules)
  · -- `z := j w`
    refine ⟨w ≫ j, hL' (w ≫ j), hYinv (w ≫ j), ?_⟩
    intro htriv
    apply hw
    -- `j^*L' ≅ t_w^*(j^*N) ⊗ (j^*N)ᵛ`
    have hP' : Iso' ((Scheme.Modules.pullback j.left).obj (twist A M N (w ≫ j)))
        ((Scheme.Modules.pullback (transl Y w)).obj ((Scheme.Modules.pullback j.left).obj N) ⊗
          Scheme.Modules.dual ((Scheme.Modules.pullback j.left).obj N)) :=
      (iso'_pb_tensor _ _ _).trans <|
        (hMtriv.tensor (iso'_pb_tensor _ _ _)).trans <|
          (iso'_unit_left _).trans <|
            ((hres N w).symm.tensor (iso'_pb_dual _ N))
    exact Iso'.of_tensor_dual_unit (hP'.symm.trans (Nonempty.intro htriv.some))
  · -- `z := 1`: `P_1 ≅ 𝟙`, so `j^*L' ≅ j^*M` is nontrivial
    refine ⟨1, hL' 1, hYinv 1, ?_⟩
    intro htriv
    apply hMtriv
    have hP1 : Iso' ((Scheme.Modules.pullback (transl A 1)).obj N ⊗ Scheme.Modules.dual N)
        (𝟙_ A.X.left.Modules) :=
      (((iso'_pb_congr (transl_one A) N).trans (iso'_pb_id N)).tensor (iso'_refl _)).trans
        (iso'_dual N)
    have hj : Iso' ((Scheme.Modules.pullback j.left).obj (twist A M N 1))
        ((Scheme.Modules.pullback j.left).obj M) :=
      (iso'_pb_tensor _ _ _).trans <|
        ((iso'_refl _).tensor ((hP1.pb _).trans (iso'_pb_unit _))).trans (iso'_unit_right _)
    exact hj.symm.trans (Nonempty.intro htriv.some)

end ZInQ.Contrib.CloudR2NOS.Step1
