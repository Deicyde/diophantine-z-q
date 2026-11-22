import ZInQKernel.Contrib.CloudR2Poincare.L6.SquareReduction

/-!
# The ACTUAL native cube class and its three face restrictions

Pure native Picard/group-object computations. These prove the faces of the
actual seven-factor class are trivial; they DO NOT assume a HasCube model or
prove global triviality until the geometric opening/gluing argument is supplied.
The certified SquareReduction source is imported unchanged.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L6

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

abbrev nativeCubeObj : Over (Spec (.of k)) := (A ⊗ A) ⊗ A

def nativeCubeProj₁ : nativeCubeObj A ⟶ A := fst (A ⊗ A) A ≫ fst A A
def nativeCubeProj₂ : nativeCubeObj A ⟶ A := fst (A ⊗ A) A ≫ snd A A
def nativeCubeProj₃ : nativeCubeObj A ⟶ A := snd (A ⊗ A) A

def nativeCubeFace₁ : A ⊗ A ⟶ nativeCubeObj A := lift (lift 1 (fst A A)) (snd A A)
def nativeCubeFace₂ : A ⊗ A ⟶ nativeCubeObj A := lift (lift (fst A A) 1) (snd A A)
def nativeCubeFace₃ : A ⊗ A ⟶ nativeCubeObj A := lift (lift (fst A A) (snd A A)) 1

@[simp] theorem nativeCubeFace₁_proj₁ : nativeCubeFace₁ A ≫ nativeCubeProj₁ A = 1 := by
  simp [nativeCubeFace₁, nativeCubeProj₁]
@[simp] theorem nativeCubeFace₁_proj₂ : nativeCubeFace₁ A ≫ nativeCubeProj₂ A = fst A A := by
  simp [nativeCubeFace₁, nativeCubeProj₂]
@[simp] theorem nativeCubeFace₁_proj₃ : nativeCubeFace₁ A ≫ nativeCubeProj₃ A = snd A A := by
  simp [nativeCubeFace₁, nativeCubeProj₃]
@[simp] theorem nativeCubeFace₂_proj₁ : nativeCubeFace₂ A ≫ nativeCubeProj₁ A = fst A A := by
  simp [nativeCubeFace₂, nativeCubeProj₁]
@[simp] theorem nativeCubeFace₂_proj₂ : nativeCubeFace₂ A ≫ nativeCubeProj₂ A = 1 := by
  simp [nativeCubeFace₂, nativeCubeProj₂]
@[simp] theorem nativeCubeFace₂_proj₃ : nativeCubeFace₂ A ≫ nativeCubeProj₃ A = snd A A := by
  simp [nativeCubeFace₂, nativeCubeProj₃]
@[simp] theorem nativeCubeFace₃_proj₁ : nativeCubeFace₃ A ≫ nativeCubeProj₁ A = fst A A := by
  simp [nativeCubeFace₃, nativeCubeProj₁]
@[simp] theorem nativeCubeFace₃_proj₂ : nativeCubeFace₃ A ≫ nativeCubeProj₂ A = snd A A := by
  simp [nativeCubeFace₃, nativeCubeProj₂]
@[simp] theorem nativeCubeFace₃_proj₃ : nativeCubeFace₃ A ≫ nativeCubeProj₃ A = 1 := by
  simp [nativeCubeFace₃, nativeCubeProj₃]

/-- Actual Picard pullback by the constant unit map factors through the field spectrum. -/
theorem nativePic_map_one {B : Over (Spec (.of k))} (L : A.left.Pic) :
    Scheme.Pic.map (1 : B ⟶ A).left L = 1 := by
  letI : Subsingleton (𝟙_ (Over (Spec (.of k)))).left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of k)).Pic)
  change Scheme.Pic.map ((toUnit B).left ≫ η[A].left) L = 1
  exact pic_map_comp_eq_one (toUnit B).left η[A].left L

/-- The literal seven-factor native class on A³; no geometric premise is encoded. -/
def nativeCubeClass (L : A.left.Pic) : (nativeCubeObj A).left.Pic :=
  Scheme.Pic.map (nativeCubeProj₁ A * nativeCubeProj₂ A * nativeCubeProj₃ A).left L *
    Scheme.Pic.map (nativeCubeProj₁ A).left L *
    Scheme.Pic.map (nativeCubeProj₂ A).left L *
    Scheme.Pic.map (nativeCubeProj₃ A).left L *
    (Scheme.Pic.map (nativeCubeProj₁ A * nativeCubeProj₂ A).left L *
      Scheme.Pic.map (nativeCubeProj₁ A * nativeCubeProj₃ A).left L *
      Scheme.Pic.map (nativeCubeProj₂ A * nativeCubeProj₃ A).left L)⁻¹

/-- Actual triviality on e×A×A, by the genuine coordinate/group/Picard identities. -/
theorem nativeCubeClass_face₁ (L : A.left.Pic) :
    Scheme.Pic.map (nativeCubeFace₁ A).left (nativeCubeClass A L) = 1 := by
  simp only [nativeCubeClass, Scheme.Pic.map_mul, ZInQ.Contrib.CloudR2Poincare.L1.pic_map_inv,
    ← Scheme.Pic.map_comp, ← Over.comp_left, MonObj.comp_mul,
    nativeCubeFace₁_proj₁, nativeCubeFace₁_proj₂, nativeCubeFace₁_proj₃,
    _root_.one_mul, nativePic_map_one]
  simp [_root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]

/-- Actual triviality on A×e×A, without a supplied cube/square premise. -/
theorem nativeCubeClass_face₂ (L : A.left.Pic) :
    Scheme.Pic.map (nativeCubeFace₂ A).left (nativeCubeClass A L) = 1 := by
  simp only [nativeCubeClass, Scheme.Pic.map_mul, ZInQ.Contrib.CloudR2Poincare.L1.pic_map_inv,
    ← Scheme.Pic.map_comp, ← Over.comp_left, MonObj.comp_mul,
    nativeCubeFace₂_proj₁, nativeCubeFace₂_proj₂, nativeCubeFace₂_proj₃,
    _root_.one_mul, _root_.mul_one, nativePic_map_one]
  simp [_root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]

/-- Actual triviality on A×A×e, without assuming O_A has vanishing positive cohomology. -/
theorem nativeCubeClass_face₃ (L : A.left.Pic) :
    Scheme.Pic.map (nativeCubeFace₃ A).left (nativeCubeClass A L) = 1 := by
  simp only [nativeCubeClass, Scheme.Pic.map_mul, ZInQ.Contrib.CloudR2Poincare.L1.pic_map_inv,
    ← Scheme.Pic.map_comp, ← Over.comp_left, MonObj.comp_mul,
    nativeCubeFace₃_proj₁, nativeCubeFace₃_proj₂, nativeCubeFace₃_proj₃,
    _root_.one_mul, _root_.mul_one, nativePic_map_one]
  simp [_root_.mul_assoc, _root_.mul_left_comm, _root_.mul_comm]

/-- Pulling back an ALREADY PROVED zero cube class gives the arbitrary-test class relation.
The only input is triviality of this specific actual class, not a HasCube model. -/
theorem nativeCubeRelation_of_class_eq_one (L : A.left.Pic)
    (hClass : nativeCubeClass A L = 1) (P : Over (Spec (.of k))) (f g h : P ⟶ A) :
    Scheme.Pic.map (f * g * h).left L * Scheme.Pic.map f.left L *
        Scheme.Pic.map g.left L * Scheme.Pic.map h.left L =
      Scheme.Pic.map (f * g).left L * Scheme.Pic.map (f * h).left L *
        Scheme.Pic.map (g * h).left L := by
  let v : P ⟶ nativeCubeObj A := lift (lift f g) h
  have hv₁ : v ≫ nativeCubeProj₁ A = f := by simp [v, nativeCubeProj₁]
  have hv₂ : v ≫ nativeCubeProj₂ A = g := by simp [v, nativeCubeProj₂]
  have hv₃ : v ≫ nativeCubeProj₃ A = h := by simp [v, nativeCubeProj₃]
  have hc := congrArg (Scheme.Pic.map v.left) hClass
  simp only [nativeCubeClass, Scheme.Pic.map_mul,
    ZInQ.Contrib.CloudR2Poincare.L1.pic_map_inv, Scheme.Pic.map_one,
    ← Scheme.Pic.map_comp, ← Over.comp_left, MonObj.comp_mul,
    hv₁, hv₂, hv₃] at hc
  change (Scheme.Pic.map (f * g * h).left L * Scheme.Pic.map f.left L *
      Scheme.Pic.map g.left L * Scheme.Pic.map h.left L) /
      (Scheme.Pic.map (f * g).left L * Scheme.Pic.map (f * h).left L *
        Scheme.Pic.map (g * h).left L) = 1 at hc
  exact _root_.div_eq_one.mp hc

end ZInQ.Contrib.CloudR2Poincare.L6
