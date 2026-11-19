import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageDiagram
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel

/-!
# Lane RC31, round 3, part 3: the stage pairing data and its transport to the finite free model

Manuscript `diophantine_zq.tex`: the retained data "include the integral duality maps, their
homotopy inverses, and the homotopies expressing compatibility of duality with localization"
(tex 4385–4388); Lemma `ex:limits-inner-limit` (tex 4391–4451): "Transport any fixed finite
collection of arithmetic maps by `f ↦ p′fi`" (tex 4439–4440).

At one coefficient stage `A` (in the application `A = A_i`, an Artin local ring), the ARITHMETIC
inputs are a complex `X` (the stage global cochains with the old local conditions) and
`StagePairingInput X`:
* `res`: the localization at the derivative label, already composed with the comparison to the
  split local model `L = D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]` (tex 4860–4868) — the local pairing
  coordinates at `q_i`;
* `glob`: the trace of the global cup product, `Xᵃ × Xᵇ → A` for `a + b = 3`;
* `loc`: the local pairing of the split model in its coordinates;
* `recip`: chain-level reciprocity `glob(dx, y) + (−1)^a glob(x, dy) = −loc(res x, res y)` (the
  trace of the Leibniz rule and of cup-product compatibility).
From these the stage global duality map `stageDualityMap : X → Hom(Cone(res)[−1], A)[−3]` is
defined (`x ↦ ((b, y) ↦ glob(x, b) + (−1)^a loc(res x, y))`, the form of Nekovář's global duality
map, *Selmer complexes* 5.4.3; its quasi-isomorphy at `A_i` is an arithmetic input).

This file is GENERIC: for a graded finite free model `R` of `X` it transports the pairing data to
the model (`modelRes`, `modelGlob`; `modelRecip`, `modelRes_comm` PROVED), i.e. the first half of
`StageMatrixDiagram`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex splitLocalTerms Vec2 Coords)
open ZInQ.Manuscript.RC.Limits (GRetract GradedModel matCx matCx_d_apply)

/-! ### Coordinates over a commutative ring -/

section Coordinates

variable (A : Type) [CommRing A]

/-- **The coordinates of the split model over a commutative ring**: `Lⁿ ≃ (lIdx n → A)` (tex 4860;
the ring-generic form of `lCoord`). Kind: definition. -/
def lCoordR : ∀ n : ℤ, (splitLocalComplex A).X n ≃ₗ[A] (lIdx n → A)
  | .ofNat 0 => LinearEquiv.refl A (Fin 2 → A)
  | .ofNat 1 => (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) A A).symm
  | .ofNat 2 => LinearEquiv.refl A (Fin 2 → A)
  | .ofNat (m + 3) => by
    haveI : Subsingleton ((splitLocalComplex A).X (.ofNat (m + 3))) :=
      inferInstanceAs (Subsingleton PUnit)
    haveI : Subsingleton (lIdx (.ofNat (m + 3)) → A) := inferInstanceAs (Subsingleton (Empty → A))
    exact LinearEquiv.ofSubsingleton _ _
  | .negSucc m => by
    haveI : Subsingleton ((splitLocalComplex A).X (.negSucc m)) :=
      inferInstanceAs (Subsingleton PUnit)
    haveI : Subsingleton (lIdx (.negSucc m) → A) := inferInstanceAs (Subsingleton (Empty → A))
    exact LinearEquiv.ofSubsingleton _ _

variable {A}

/-- The local pairing of a matrix in the coordinates of the split model,
`(u, v) ↦ lCoord u ⬝ (M (lCoord v))`. Kind: definition. -/
def locForm (M : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) A) (a b : ℤ) :
    (splitLocalComplex A).X a →ₗ[A] (splitLocalComplex A).X b →ₗ[A] A :=
  LinearMap.mk₂ A (fun u v => lCoordR A a u ⬝ᵥ (M a b *ᵥ lCoordR A b v))
    (fun u u' v => by rw [map_add, add_dotProduct])
    (fun c u v => by rw [map_smul, smul_dotProduct, smul_eq_mul])
    (fun u v v' => by rw [map_add, mulVec_add, dotProduct_add])
    (fun c u v => by rw [map_smul, mulVec_smul, dotProduct_smul, smul_eq_mul])

/-- Evaluation of the local pairing of a matrix. Kind: PROVED (definitional). -/
theorem locForm_apply (M : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) A) (a b : ℤ)
    (u : (splitLocalComplex A).X a) (v : (splitLocalComplex A).X b) :
    locForm M a b u v = lCoordR A a u ⬝ᵥ (M a b *ᵥ lCoordR A b v) :=
  rfl

end Coordinates

/-! ### The stage pairing data (arithmetic inputs) -/

section Stage

variable {A : Type} [CommRing A]

/-- **The stage pairing data** (ELLIOT / arithmetic inputs, tex 4385–4388, 4860–4868, 5037): the
localization at the derivative label in the coordinates of the split model, the trace of the global
cup product, the local pairing, and chain-level reciprocity. Kind: definition (hypothesis
structure; supplied by the arithmetic half). -/
structure StagePairingInput (X : GCx A) where
  /-- The localization at the derivative label, composed with the split local comparison. -/
  res : GHom X (splitLocalComplex A)
  /-- The trace of the global cup product. -/
  glob : ∀ a b : ℤ, a + b = 3 → X.X a →ₗ[A] X.X b →ₗ[A] A
  /-- The local pairing of the split model, in its coordinates. -/
  loc : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) A
  /-- Chain-level reciprocity. -/
  recip : ∀ (a b : ℤ) (h : a + b = 2) (x : X.X a) (y : X.X b),
    glob (a + 1) b (by omega) (X.d a (a + 1) rfl x) y +
        sgn a • glob a (b + 1) (by omega) x (X.d b (b + 1) rfl y) =
      -(locForm loc a b (res.f a a rfl x) (res.f b b rfl y))

variable {X : GCx A}

/-- The split model has zero differentials. Kind: PROVED. -/
theorem splitLocal_d_eq_zero (a b : ℤ) (h : a + 1 = b) (u : (splitLocalComplex A).X a) :
    (splitLocalComplex A).d a b h u = 0 :=
  rfl

/-- The localization kills boundaries (the split model has zero differential). Kind: PROVED. -/
theorem StagePairingInput.res_d (P : StagePairingInput X) (a b : ℤ) (h : a + 1 = b)
    (x : X.X a) : P.res.f b b rfl (X.d a b h x) = 0 := by
  subst h
  exact (P.res.comm a (a + 1) a (a + 1) rfl rfl rfl rfl x).trans (splitLocal_d_eq_zero _ _ _ _)

end Stage

/-! ### The stage global duality map -/

section Map

variable {A : Type} [CommRing A] {X : GCx A} (P : StagePairingInput X)

/-- The linear form of the stage duality map on `Cone(res)[−1]` in degree `n`:
`(b, y) ↦ glob(x, b) + (−1)^a loc(res x, y)` (Nekovář, *Selmer complexes*, 5.4.3: the global duality
map `x ↦ tr(x ∪ ·)` on the compactly supported cone). Kind: definition. -/
def stageDualForm (a n : ℤ) (h : a + n = 3) :
    X.X a →ₗ[A] (X.X n × (splitLocalComplex A).X (n - 1)) →ₗ[A] A :=
  LinearMap.mk₂ A (fun x z => P.glob a n h x z.1 +
      sgn a • locForm P.loc a (n - 1) (P.res.f a a rfl x) z.2)
    (fun x x' z => by simp only [map_add, LinearMap.add_apply, smul_add]; abel)
    (fun c x z => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, zsmul_eq_mul]; ring)
    (fun x z z' => by simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add]; abel)
    (fun c x z => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, zsmul_eq_mul]; ring)

/-- Evaluation of the linear form of the stage duality map. Kind: PROVED (definitional). -/
theorem stageDualForm_apply (a n : ℤ) (h : a + n = 3) (x : X.X a)
    (z : X.X n × (splitLocalComplex A).X (n - 1)) :
    stageDualForm P a n h x z =
      P.glob a n h x z.1 + sgn a • locForm P.loc a (n - 1) (P.res.f a a rfl x) z.2 :=
  rfl

/-- Reciprocity with a general target degree. Kind: PROVED. -/
theorem StagePairingInput.recip' (a b c : ℤ) (hab : a + b = 2) (hbc : b + 1 = c)
    (hac : a + c = 3) (x : X.X a) (y : X.X b) :
    P.glob (a + 1) b (by omega) (X.d a (a + 1) rfl x) y +
        sgn a • P.glob a c hac x (X.d b c hbc y) =
      -(locForm P.loc a b (P.res.f a a rfl x) (P.res.f b b rfl y)) := by
  subst hbc
  exact P.recip a b hab x y

/-- The localization along an index equality. Kind: PROVED. -/
theorem StagePairingInput.locForm_res_cast (a m n : ℤ) (h : m = n) (u : (splitLocalComplex A).X a)
    (y : X.X m) :
    locForm P.loc a n u (P.res.f m n h y) = locForm P.loc a m u (P.res.f m m rfl y) := by
  subst h
  rfl

/-- The chain-map identity of the stage duality map, in clean form. Kind: PROVED. -/
theorem stageDualForm_comm (a : ℤ) (x : X.X a) (b : X.X (3 - (a + 1)))
    (y : (splitLocalComplex A).X (3 - (a + 1) - 1)) :
    stageDualForm P (a + 1) (3 - (a + 1)) (by omega) (X.d a (a + 1) rfl x) (b, y) =
      (-(sgn a)) • stageDualForm P a (3 - a) (by omega) x
        (X.d (3 - (a + 1)) (3 - a) (by omega) b,
          P.res.f (3 - (a + 1)) (3 - a - 1) (by omega) b -
            (splitLocalComplex A).d (3 - (a + 1) - 1) (3 - a - 1) (by omega) y) := by
  have e := P.recip' a (3 - (a + 1)) (3 - a) (by omega) (by omega) (by omega) x b
  have hres := P.res_d a (a + 1) rfl x
  have hcast := P.locForm_res_cast a (3 - (a + 1)) (3 - a - 1) (by omega) (P.res.f a a rfl x) b
  rw [stageDualForm_apply, stageDualForm_apply]
  dsimp only
  rw [hres, map_zero, LinearMap.zero_apply, smul_zero, add_zero, splitLocal_d_eq_zero, sub_zero,
    hcast]
  have hs : ((sgn a : ℤ) : A) * (sgn a : A) = 1 := by
    rw [← Int.cast_mul, sgn_mul_self, Int.cast_one]
  simp only [zsmul_eq_mul, Int.cast_neg] at e ⊢
  linear_combination e + (locForm P.loc a (3 - (a + 1)) (P.res.f a a rfl x)
    (P.res.f (3 - (a + 1)) (3 - (a + 1)) rfl b)) * hs

/-- **The stage global duality map** `X → Hom_A(Cone(res)[−1], A)[−3]`,
`x ↦ ((b, y) ↦ glob(x, b) + (−1)^a loc(res x, y))` (Nekovář, *Selmer complexes*, 5.4.3; tex
4385–4388). A chain map by reciprocity. Kind: definition (PROVED chain property). -/
def stageDualityMap : GHom X (dualCx (coneCx P.res) 3) where
  f a b h := by
    subst h
    exact stageDualForm P a (3 - a) (by omega)
  comm a a₁ b b₁ hab h₁ h₂ hb x := by
    subst hab hb h₁
    refine dualCx_ext fun z => ?_
    obtain ⟨b, y⟩ := z
    exact stageDualForm_comm P a x b y

end Map


/-! ### Transport to the finite free model -/

section Model

variable {A : Type} [CommRing A] {X : GCx A} (R : GradedModel X) (P : StagePairingInput X)

/-- The inclusion of the model in degree `n`, with its plain source type. Kind: definition. -/
def modelIncl (n : ℤ) : (Fin (R.rank n) → A) →ₗ[A] X.X n := R.retract.i.f n n rfl

/-- **The localization of the model in coordinates**: the matrix of `lCoord ∘ res ∘ i`
(tex 4439–4440: `f ↦ p′ f i`, with the split model as its own model). Kind: definition. -/
def modelRes (n : ℤ) : Matrix (lIdx n) (Fin (R.rank n)) A :=
  LinearMap.toMatrix' ((lCoordR A n).toLinearMap ∘ₗ P.res.f n n rfl ∘ₗ modelIncl R n)

/-- **The trace pairing of the model**: the matrix of `glob(i ·, i ·)`. Kind: definition. -/
def modelGlob (a b : ℤ) (h : a + b = 3) : Matrix (Fin (R.rank a)) (Fin (R.rank b)) A :=
  Matrix.of fun x y => P.glob a b h (modelIncl R a (Pi.single x 1)) (modelIncl R b (Pi.single y 1))

/-- The model localization applied to a vector. Kind: PROVED. -/
theorem modelRes_mulVec (n : ℤ) (x : Fin (R.rank n) → A) :
    modelRes R P n *ᵥ x = lCoordR A n (P.res.f n n rfl (modelIncl R n x)) := by
  rw [modelRes, LinearMap.toMatrix'_mulVec]
  rfl

/-- Moving a matrix across the dot product, over a commutative ring. Kind: PROVED. -/
theorem mulVec_dotProduct_eqR {n m : Type} [Fintype n] [Fintype m] (D : Matrix m n A) (x : n → A)
    (u : m → A) : (D *ᵥ x) ⬝ᵥ u = x ⬝ᵥ (Dᵀ *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- A matrix is zero if its bilinear form vanishes. Kind: PROVED. -/
theorem matrix_eq_zero_of_form {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix m n A) (h : ∀ v w, v ⬝ᵥ (M *ᵥ w) = 0) : M = 0 := by
  ext x y
  have e := h (Pi.single x 1) (Pi.single y 1)
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul] at e
  exact e

/-- Expansion of a coordinate vector in the standard basis. Kind: PROVED. -/
theorem coord_expandR {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → A) :
    w = ∑ i, w i • Pi.single i (1 : A) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- The bilinear form of the model trace pairing is `glob(i ·, i ·)`. Kind: PROVED. -/
theorem modelGlob_form (a b : ℤ) (h : a + b = 3) (v : Fin (R.rank a) → A)
    (w : Fin (R.rank b) → A) :
    v ⬝ᵥ (modelGlob R P a b h *ᵥ w) = P.glob a b h (modelIncl R a v) (modelIncl R b w) := by
  conv_rhs => rw [coord_expandR v, coord_expandR w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [dotProduct, Matrix.mulVec, modelGlob, Matrix.of_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- The model differential and the inclusion: `i (d_C x) = d (i x)`. Kind: PROVED. -/
theorem model_i_dC (a b : ℤ) (h : a + 1 = b) (x : Fin (R.rank a) → A) :
    modelIncl R b (R.dC a b h *ᵥ x) = X.d a b h (modelIncl R a x) := by
  subst h
  exact R.retract.i.comm a (a + 1) a (a + 1) rfl rfl rfl rfl x

/-- **The model localization is a chain map**: `res_C (n + 1) ⋅ d_C = 0`. Kind: PROVED. -/
theorem modelRes_comm (n : ℤ) : modelRes R P (n + 1) * R.dC n (n + 1) rfl = 0 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, modelRes_mulVec, model_i_dC, P.res_d,
    map_zero, map_zero, LinearMap.zero_apply]

/-- The model localization form. Kind: PROVED. -/
theorem modelLoc_form (a b : ℤ) (v : Fin (R.rank a) → A) (w : Fin (R.rank b) → A) :
    v ⬝ᵥ (((modelRes R P a)ᵀ * P.loc a b * modelRes R P b) *ᵥ w) =
      locForm P.loc a b (P.res.f a a rfl (modelIncl R a v))
        (P.res.f b b rfl (modelIncl R b w)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← mulVec_dotProduct_eqR, modelRes_mulVec,
    modelRes_mulVec, locForm_apply]

/-- **Chain-level reciprocity on the model** (the transported reciprocity, tex 4439–4442).
Kind: PROVED. -/
theorem modelRecip (a b : ℤ) (h : a + b = 2) :
    (R.dC a (a + 1) rfl)ᵀ * modelGlob R P (a + 1) b (by omega) +
        sgn a • (modelGlob R P a (b + 1) (by omega) * R.dC b (b + 1) rfl) +
        (modelRes R P a)ᵀ * P.loc a b * modelRes R P b = 0 := by
  apply matrix_eq_zero_of_form
  intro v w
  rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, ← Matrix.mulVec_mulVec, ← mulVec_dotProduct_eqR, ← Matrix.mulVec_mulVec,
    modelGlob_form, modelGlob_form, modelLoc_form, model_i_dC, model_i_dC]
  rw [P.recip a b h]
  abel

end Model

end ZInQ.Manuscript.RC.FibreDuality
