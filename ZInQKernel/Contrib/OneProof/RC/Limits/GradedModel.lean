import ZInQKernel.Contrib.OneProof.RC.Limits.FiniteFreeModel
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Dual

/-!
# Lane RC31, round 3, part 1: graded deformation retracts and graded finite free models

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451): "Let `A` be an Artin
local ring with nilpotent maximal ideal, and let a complex of flat `A`-modules have finite bounded
residual cohomology. … It admits a bounded finite free model with actual inclusion, projection and
contraction homotopy. Every fixed finite diagram of maps and homotopies, including the duality and
local-condition data used here, transports to these models."

The existing development (`FiniteFreeModel`, `Perturbation`) works on the total module. This file
fixes the GRADED interface used by the graded construction and the transport:

* `GRetract X Y`: normalized deformation retract data of a relation-indexed complex `X` onto `Y`,
  degreewise: chain maps `i : Y → X`, `p : X → Y`, a homotopy `h` of degree `−1`, with `p i = 1`,
  `1 − i p = d h + h d`, `h² = 0`, `h i = 0`, `p h = 0` (tex 4423–4437).
* `matCx rank dC`: the degreewise finite free complex `A^{rank n}` with matrix differentials.
* `GradedModel X`: a graded finite free model of `X`: ranks, model differential matrices, and a
  `GRetract` of `X` onto `matCx`.
* `GRetract.homotopyEquiv`: the retract is a homotopy equivalence of cochain complexes, hence
  `i` and `p` are quasi-isomorphisms.
* `residualCohomologyAt X n`: the residual cohomology `Hⁿ(k ⊗_A X)` in degree `n` (tex 4392–4394).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory TensorProduct IsLocalRing Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section Retract

variable {A : Type} [CommRing A]

/-- **Normalized graded deformation retract data** of `X` onto `Y` (tex 4423–4437, degreewise):
chain maps `i : Y → X` and `p : X → Y`, a homotopy `h : Xᵃ → X^{a−1}`, with `p i = 1`,
`1 − i p = d h + h d` in every degree, and the normalizations `h² = 0`, `h i = 0`, `p h = 0`.
Kind: definition (data with identities). -/
structure GRetract (X Y : GCx A) where
  /-- The inclusion of the model. -/
  i : GHom Y X
  /-- The projection onto the model. -/
  p : GHom X Y
  /-- The contraction homotopy, of degree `−1`. -/
  h : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X.X b
  /-- `p i = 1`. -/
  p_i : ∀ n (y : Y.X n), p.f n n rfl (i.f n n rfl y) = y
  /-- `1 − i p = d h + h d`. -/
  homotopy : ∀ n (x : X.X n), x - i.f n n rfl (p.f n n rfl x) =
    X.d (n - 1) n (by omega) (h n (n - 1) (by omega) x) + h (n + 1) n rfl (X.d n (n + 1) rfl x)
  /-- `h² = 0`. -/
  h_h : ∀ a b c (hab : b + 1 = a) (hbc : c + 1 = b) (x : X.X a), h b c hbc (h a b hab x) = 0
  /-- `h i = 0`. -/
  h_i : ∀ a b (hab : b + 1 = a) (y : Y.X a), h a b hab (i.f a a rfl y) = 0
  /-- `p h = 0`. -/
  p_h : ∀ a b (hab : b + 1 = a) (x : X.X a), p.f b b rfl (h a b hab x) = 0

/-- Assemble an actual cochain homotopy from relation-indexed linear identities
(`f = h ∘ d + d ∘ h + g` in every degree). Kind: definition. -/
def homotopyOfIdentities {C D : CochainComplex (ModuleCat A) ℤ} (f g : C ⟶ D)
    (h : ∀ a b : ℤ, b + 1 = a → C.X a →ₗ[A] D.X b)
    (heq : ∀ a, (f.f a).hom = h (a + 1) a rfl ∘ₗ (C.d a (a + 1)).hom +
      (D.d (a - 1) a).hom ∘ₗ h a (a - 1) (by omega) + (g.f a).hom) : Homotopy f g where
  hom a b := if hab : b + 1 = a then ModuleCat.ofHom (h a b hab) else 0
  zero a b hab := dite_eq_right hab
  comm a := by
    have hprev : (a - 1) + 1 = a := by omega
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (a - 1) a from hprev)]
    simp only [dite_eq_left hprev]
    apply ModuleCat.hom_ext
    exact heq a

variable {X Y : GCx A}

/-- The differential of `toCC` is the relation-indexed differential. Kind: PROVED. -/
theorem toCC_d_hom_eq (C : GCx A) (a b : ℤ) (h : a + 1 = b) : (C.toCC.d a b).hom = C.d a b h :=
  LinearMap.ext fun x => GCx.toCC_d_hom C a b h x


/-- **A graded deformation retract is a homotopy equivalence** `Y ≃ X` of cochain complexes, with
`hom = i` and `inv = p` (tex 4437: "Substitution using `d² = 0` gives `pi = 1` and
`1 − ip = dh + hd`"). Kind: definition (PROVED identities). -/
def GRetract.homotopyEquiv (R : GRetract X Y) : HomotopyEquiv Y.toCC X.toCC where
  hom := GHom.toCC R.i
  inv := GHom.toCC R.p
  homotopyHomInvId := Homotopy.ofEq (by
    ext n y
    exact R.p_i n y)
  homotopyInvHomId := homotopyOfIdentities _ _ (fun a b hab => -(R.h a b hab)) (by
    intro a
    erw [toCC_d_hom_eq X a (a + 1) rfl, toCC_d_hom_eq X (a - 1) a (by omega)]
    apply LinearMap.ext
    intro (x : X.X a)
    change R.i.f a a rfl (R.p.f a a rfl x) = -(R.h (a + 1) a rfl (X.d a (a + 1) rfl x)) +
      X.d (a - 1) a (by omega) (-(R.h a (a - 1) (by omega) x)) + x
    rw [map_neg]
    linear_combination (norm := abel) -(R.homotopy a x))

/-- The inclusion of a graded deformation retract is a quasi-isomorphism. Kind: PROVED. -/
theorem GRetract.quasiIso_i (R : GRetract X Y) : QuasiIso (GHom.toCC R.i) :=
  R.homotopyEquiv.quasiIso_hom

/-- The projection of a graded deformation retract is a quasi-isomorphism. Kind: PROVED. -/
theorem GRetract.quasiIso_p (R : GRetract X Y) : QuasiIso (GHom.toCC R.p) :=
  R.homotopyEquiv.quasiIso_inv

end Retract

/-! ### The degreewise finite free model complex and graded models -/

section Model

variable {A : Type} [CommRing A]

/-- **The degreewise finite free complex** `A^{rank n}` with matrix differentials `dC` (tex 4395:
"a bounded finite free model"). Kind: definition. -/
def matCx (rank : ℤ → ℕ) (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0) : GCx A where
  X n := ModuleCat.of A (Fin (rank n) → A)
  d a b h := Matrix.toLin' (dC a b h)
  d_d a b c hab hbc x := by
    change Matrix.toLin' (dC b c hbc) (Matrix.toLin' (dC a b hab) x) = 0
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hsq]
    simp

/-- The differential of `matCx` is multiplication by the matrix. Kind: PROVED (definitional). -/
theorem matCx_d_apply (rank : ℤ → ℕ)
    (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0)
    (a b : ℤ) (h : a + 1 = b) (x : Fin (rank a) → A) :
    (matCx rank dC hsq).d a b h x = dC a b h *ᵥ x :=
  rfl

/-- **A graded finite free model** of `X` (Lemma `ex:limits-inner-limit`, tex 4391–4399): ranks,
model differential matrices with `d_C² = 0`, and a normalized graded deformation retract of `X`
onto the matrix complex. Kind: definition (data). -/
structure GradedModel (X : GCx A) where
  /-- The ranks of the model. -/
  rank : ℤ → ℕ
  /-- The model differential matrices. -/
  dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A
  /-- `d_C² = 0`. -/
  dC_sq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0
  /-- The retract data. -/
  retract : GRetract X (matCx rank dC dC_sq)

/-- The model complex of a graded model. Kind: definition. -/
abbrev GradedModel.modelCx {X : GCx A} (R : GradedModel X) : GCx A :=
  matCx R.rank R.dC R.dC_sq

end Model

/-! ### Residual cohomology in a degree -/

section Residual

variable {A : Type} [CommRing A] [IsLocalRing A]

/-- The residual differential `d ⊗ k : k ⊗_A Xᵃ → k ⊗_A Xᵇ`, `k = A/𝔪`. Kind: definition. -/
abbrev residualDiff (X : GCx A) (a b : ℤ) (h : a + 1 = b) :
    ResidueField A ⊗[A] X.X a →ₗ[ResidueField A] ResidueField A ⊗[A] X.X b :=
  (X.d a b h).baseChange (ResidueField A)

/-- The subquotient `ker g / im f` of two composable linear maps. Kind: definition. -/
abbrev subquotientOf {k V W Z : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [AddCommGroup Z] [Module k Z] (f : V →ₗ[k] W) (g : W →ₗ[k] Z) : Type _ :=
  LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype

/-- **The residual cohomology in degree `n`**, `Hⁿ(k ⊗_A X)` (tex 4392–4394: "finite bounded
residual cohomology"): the kernel of `d ⊗ k` in degree `n` modulo the image from degree `n − 1`.
Kind: definition. -/
abbrev residualCohomologyAt (X : GCx A) (n : ℤ) : Type _ :=
  subquotientOf (residualDiff X (n - 1) n (by omega)) (residualDiff X n (n + 1) rfl)

end Residual

end ZInQ.Manuscript.RC.Limits
