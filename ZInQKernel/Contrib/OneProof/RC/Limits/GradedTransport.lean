import ZInQKernel.Contrib.OneProof.RC.Limits.GradedModel
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality

/-!
# Lane RC31, round 3, part 2: transport of a fixed finite diagram to graded finite free models

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit`. The statement (tex 4397–4399):
"Every fixed finite diagram of maps and homotopies, including the duality and local-condition
data used here, transports to these models." The proof (tex 4438–4442): "Transport any fixed
finite collection of arithmetic maps by `f ↦ p′fi`. The identity `1 − ip = dh + hd` transports
their compatibility homotopies as well, including the second homotopies in the cup-product
diagrams."

This file is the GRADED, relation-indexed analogue of the total-module section `Transport` of
`Perturbation`. For graded deformation retracts `R : GRetract X Y`, `R' : GRetract X' Y'`,
`R'' : GRetract X'' Y''` (`GradedModel`):

* `GRetract.transport`: chain maps `f : X → X'` transport to chain maps `p′ f i : Y → Y'`.
* `IsHomotopy`, `GRetract.transport_isHomotopy`: homotopies transport by `H ↦ p′ H i`.
* `IsSecondHomotopy`, `GRetract.transport_isSecondHomotopy`: second homotopies transport.
* `GRetract.transport_comp`: transport preserves composition up to the explicit homotopy
  `K = p″ g h′ f i` (this uses `1 − i′p′ = d h′ + h′ d`).
* `GRetract.transport_square`: homotopy-commutative squares transport.
* `GRetract.restrictPair`, `GRetract.transportPair`: pairings of complexes transport; bilinear
  forms with a Leibniz defect (`IsLeibnizDefect`) transport by restriction
  (`GRetract.restrictForm_isLeibnizDefect`, `GRetract.restrictForm_cupDefect`).
* Matrix forms over `matCx`: `matHom`, `ghomMatrix`, `famMatrix`, `formMatrix` and the exact
  matrix identities satisfied by transported maps, homotopies, second homotopies, composites,
  squares and forms.
* Non-vacuity: `GRetract.refl` (identity retract), `transport_refl`, `matCx.gradedModel`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

section Transport

variable {A : Type} [CommRing A] {X Y X' Y' X'' Y'' X₁ Y₁ : GCx A}

/-- A chain map commutes with the differential, stated with a single relation.
Kind: PROVED (auxiliary for tex 4438–4442). -/
theorem ghom_comm_d {X Y : GCx A} (f : GHom X Y) (a b : ℤ) (h : a + 1 = b) (x : X.X a) :
    f.f b b rfl (X.d a b h x) = Y.d a b h (f.f a a rfl x) :=
  f.comm a b a b rfl h h rfl x

/-- **Transport of a chain map** `f : X → X'` to the models (tex 4438–4440, "Transport any fixed
finite collection of arithmetic maps by `f ↦ p′fi`"): the components are `p′ ∘ f ∘ i`, and the
result is a chain map. Kind: definition (chain-map property PROVED). -/
def GRetract.transport (R : GRetract X Y) (R' : GRetract X' Y') (f : GHom X X') :
    GHom Y Y' where
  f a b hab := (R'.p.f b b rfl).comp ((f.f a b hab).comp (R.i.f a a rfl))
  comm i i₁ j j₁ hij h₁ h₂ hj y := by
    subst hij hj
    change R'.p.f i₁ i₁ rfl (f.f i₁ i₁ rfl (R.i.f i₁ i₁ rfl (Y.d i i₁ h₁ y))) =
      Y'.d i i₁ h₂ (R'.p.f i i rfl (f.f i i rfl (R.i.f i i rfl y)))
    rw [ghom_comm_d R.i, ghom_comm_d f, ghom_comm_d R'.p]

/-- The transported map is `p′ f i` in every degree (tex 4438–4440).
Kind: PROVED (definitional). -/
theorem GRetract.transport_apply (R : GRetract X Y) (R' : GRetract X' Y') (f : GHom X X')
    (n : ℤ) (y : Y.X n) :
    (R.transport R' f).f n n rfl y = R'.p.f n n rfl (f.f n n rfl (R.i.f n n rfl y)) :=
  rfl

/-- **Transport of a family of maps of degree `−k`** (tex 4440–4442): `H ↦ p′ H i`, used for
homotopies (`k = 1`) and second homotopies (`k = 2`). Kind: definition. -/
def GRetract.transportFam (R : GRetract X Y) (R' : GRetract X' Y') (k : ℤ)
    (H : ∀ a b : ℤ, b + k = a → X.X a →ₗ[A] X'.X b) (a b : ℤ) (hab : b + k = a) :
    Y.X a →ₗ[A] Y'.X b :=
  (R'.p.f b b rfl).comp ((H a b hab).comp (R.i.f a a rfl))

/-- **A relation-indexed homotopy** `H` from `f` to `g` (tex 4440–4442): in every degree,
`f − g = d H + H d`. Kind: definition. -/
def IsHomotopy {X X' : GCx A} (f g : GHom X X')
    (H : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X'.X b) : Prop :=
  ∀ n (x : X.X n), f.f n n rfl x - g.f n n rfl x =
    X'.d (n - 1) n (by omega) (H n (n - 1) (by omega) x) + H (n + 1) n rfl (X.d n (n + 1) rfl x)

/-- **Homotopies transport** (tex 4440–4442, "transports their compatibility homotopies"): if
`H` is a homotopy from `f` to `g`, then `p′ H i` is a homotopy from `p′ f i` to `p′ g i`.
Kind: PROVED. -/
theorem GRetract.transport_isHomotopy (R : GRetract X Y) (R' : GRetract X' Y')
    {f g : GHom X X'} {H : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X'.X b}
    (hH : IsHomotopy f g H) :
    IsHomotopy (R.transport R' f) (R.transport R' g) (R.transportFam R' 1 H) := by
  intro n y
  change R'.p.f n n rfl (f.f n n rfl (R.i.f n n rfl y)) -
      R'.p.f n n rfl (g.f n n rfl (R.i.f n n rfl y)) =
    Y'.d (n - 1) n (by omega)
        (R'.p.f (n - 1) (n - 1) rfl (H n (n - 1) (by omega) (R.i.f n n rfl y))) +
      R'.p.f n n rfl (H (n + 1) n rfl (R.i.f (n + 1) (n + 1) rfl (Y.d n (n + 1) rfl y)))
  rw [← map_sub, hH n, map_add, ghom_comm_d R'.p, ghom_comm_d R.i]

/-- **A relation-indexed second homotopy** `G` (of degree `−2`) between homotopies `H` and `H'`
(tex 4441–4442, "the second homotopies in the cup-product diagrams"): `H − H' = d G − G d`.
Kind: definition. -/
def IsSecondHomotopy {X X' : GCx A} (H H' : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X'.X b)
    (G : ∀ a b : ℤ, b + 2 = a → X.X a →ₗ[A] X'.X b) : Prop :=
  ∀ n (x : X.X n), H n (n - 1) (by omega) x - H' n (n - 1) (by omega) x =
    X'.d (n - 2) (n - 1) (by omega) (G n (n - 2) (by omega) x) -
      G (n + 1) (n - 1) (by omega) (X.d n (n + 1) rfl x)

/-- **Second homotopies transport** (tex 4441–4442): if `H − H' = d G − G d`, then
`p′Hi − p′H′i = d (p′Gi) − (p′Gi) d`. Kind: PROVED. -/
theorem GRetract.transport_isSecondHomotopy (R : GRetract X Y) (R' : GRetract X' Y')
    {H H' : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X'.X b}
    {G : ∀ a b : ℤ, b + 2 = a → X.X a →ₗ[A] X'.X b} (hG : IsSecondHomotopy H H' G) :
    IsSecondHomotopy (R.transportFam R' 1 H) (R.transportFam R' 1 H')
      (R.transportFam R' 2 G) := by
  intro n y
  change R'.p.f (n - 1) (n - 1) rfl (H n (n - 1) (by omega) (R.i.f n n rfl y)) -
      R'.p.f (n - 1) (n - 1) rfl (H' n (n - 1) (by omega) (R.i.f n n rfl y)) =
    Y'.d (n - 2) (n - 1) (by omega)
        (R'.p.f (n - 2) (n - 2) rfl (G n (n - 2) (by omega) (R.i.f n n rfl y))) -
      R'.p.f (n - 1) (n - 1) rfl
        (G (n + 1) (n - 1) (by omega) (R.i.f (n + 1) (n + 1) rfl (Y.d n (n + 1) rfl y)))
  rw [← map_sub, hG n, map_sub, ghom_comm_d R'.p, ghom_comm_d R.i]

/-- **The composition homotopy** `K = p″ g h′ f i` (tex 4440–4442). Kind: definition. -/
def GRetract.compHomotopy (R : GRetract X Y) (R' : GRetract X' Y') (R'' : GRetract X'' Y'')
    (f : GHom X X') (g : GHom X' X'') (a b : ℤ) (hab : b + 1 = a) : Y.X a →ₗ[A] Y''.X b :=
  (R''.p.f b b rfl).comp ((g.f b b rfl).comp ((R'.h a b hab).comp
    ((f.f a a rfl).comp (R.i.f a a rfl))))

/-- **Transport preserves composition up to an explicit homotopy** (tex 4440–4442, using
`1 − i′p′ = d h′ + h′ d`): `K = p″ g h′ f i` is a homotopy from the transport of `g ∘ f` to the
composite of the transports, i.e. `p″ g f i − (p″ g i′)(p′ f i) = d K + K d`. Kind: PROVED. -/
theorem GRetract.transport_comp (R : GRetract X Y) (R' : GRetract X' Y')
    (R'' : GRetract X'' Y'') (f : GHom X X') (g : GHom X' X'') :
    IsHomotopy (R.transport R'' (ghomComp f g))
      (ghomComp (R.transport R' f) (R'.transport R'' g)) (R.compHomotopy R' R'' f g) := by
  intro n y
  change R''.p.f n n rfl (g.f n n rfl (f.f n n rfl (R.i.f n n rfl y))) -
      R''.p.f n n rfl (g.f n n rfl (R'.i.f n n rfl
        (R'.p.f n n rfl (f.f n n rfl (R.i.f n n rfl y))))) =
    Y''.d (n - 1) n (by omega) (R''.p.f (n - 1) (n - 1) rfl (g.f (n - 1) (n - 1) rfl
        (R'.h n (n - 1) (by omega) (f.f n n rfl (R.i.f n n rfl y))))) +
      R''.p.f n n rfl (g.f n n rfl (R'.h (n + 1) n rfl (f.f (n + 1) (n + 1) rfl
        (R.i.f (n + 1) (n + 1) rfl (Y.d n (n + 1) rfl y)))))
  rw [← map_sub, ← map_sub, R'.homotopy n, map_add, map_add, ghom_comm_d g,
    ghom_comm_d R''.p, ghom_comm_d R.i, ghom_comm_d f]

/-- **The transported square homotopy** `p″ H i − p″ g h′ f i + p″ k h₁ l i` (tex 4440–4442).
Kind: definition. -/
def GRetract.squareHomotopy (R : GRetract X Y) (R₁ : GRetract X₁ Y₁) (R' : GRetract X' Y')
    (R'' : GRetract X'' Y'') (f : GHom X X') (g : GHom X' X'') (l : GHom X X₁)
    (k : GHom X₁ X'') (H : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X''.X b) (a b : ℤ)
    (hab : b + 1 = a) : Y.X a →ₗ[A] Y''.X b :=
  R.transportFam R'' 1 H a b hab - R.compHomotopy R' R'' f g a b hab +
    R.compHomotopy R₁ R'' l k a b hab

/-- **Homotopy-commutative squares transport** (tex 4440–4442; graded form of
`retractTransport_square`): if `H` is a homotopy from `g ∘ f` to `k ∘ l`, then
`p″ H i − p″ g h′ f i + p″ k h₁ l i` is a homotopy from `g_C ∘ f_C` to `k_C ∘ l_C`.
Kind: PROVED. -/
theorem GRetract.transport_square (R : GRetract X Y) (R₁ : GRetract X₁ Y₁)
    (R' : GRetract X' Y') (R'' : GRetract X'' Y'') {f : GHom X X'} {g : GHom X' X''}
    {l : GHom X X₁} {k : GHom X₁ X''} {H : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X''.X b}
    (hH : IsHomotopy (ghomComp f g) (ghomComp l k) H) :
    IsHomotopy (ghomComp (R.transport R' f) (R'.transport R'' g))
      (ghomComp (R.transport R₁ l) (R₁.transport R'' k))
      (R.squareHomotopy R₁ R' R'' f g l k H) := by
  intro n y
  have e1 := R.transport_comp R' R'' f g n y
  have e2 := R.transport_comp R₁ R'' l k n y
  have e3 := R.transport_isHomotopy R'' hH n y
  simp only [GRetract.squareHomotopy, LinearMap.add_apply, LinearMap.sub_apply, map_add,
    map_sub]
  linear_combination (norm := abel) e3 + e2 - e1

/-! ### Pairings and bilinear forms -/

variable {T T' : GCx A}

/-- **Restriction of a pairing of complexes to the models** (tex 4397–4399, the duality data;
tex 4438–4440): a pairing `P : X × X' → T` into a FIXED target `T` restricts along the
inclusions to the pairing `(y, y') ↦ P(i y, i′ y')` of `Y × Y'` into `T`, with the Leibniz rule
holding exactly. Kind: definition (Leibniz rule PROVED). -/
def GRetract.restrictPair (R : GRetract X Y) (R' : GRetract X' Y') (P : GPair X X' T) :
    GPair Y Y' T where
  P a b k h := (P.P a b k h).compl₁₂ (R.i.f a a rfl) (R'.i.f b b rfl)
  leib a a₁ b b₁ k k₁ h ha hb hk y y' := by
    change T.d k k₁ hk (P.P a b k h (R.i.f a a rfl y) (R'.i.f b b rfl y')) =
      P.P a₁ b k₁ (by omega) (R.i.f a₁ a₁ rfl (Y.d a a₁ ha y)) (R'.i.f b b rfl y') +
        sgn a • P.P a b₁ k₁ (by omega) (R.i.f a a rfl y) (R'.i.f b₁ b₁ rfl (Y'.d b b₁ hb y'))
    rw [ghom_comm_d R.i, ghom_comm_d R'.i]
    exact P.leib a a₁ b b₁ k k₁ h ha hb hk _ _

/-- The restricted pairing is `P(i y, i′ y')` (tex 4438–4440). Kind: PROVED (definitional). -/
theorem GRetract.restrictPair_apply (R : GRetract X Y) (R' : GRetract X' Y') (P : GPair X X' T)
    (a b k : ℤ) (h : a + b = k) (y : Y.X a) (y' : Y'.X b) :
    (R.restrictPair R' P).P a b k h y y' = P.P a b k h (R.i.f a a rfl y) (R'.i.f b b rfl y') :=
  rfl

/-- **Transport of a pairing of complexes to the models, target included** (tex 4397–4399,
4438–4440): for a retract `RT` of the target `T` onto `T'`, `(y, y') ↦ p_T P(i y, i′ y')` is a
pairing `Y × Y' → T'`, with the Leibniz rule holding exactly. Kind: definition (Leibniz rule
PROVED). -/
def GRetract.transportPair (R : GRetract X Y) (R' : GRetract X' Y') (RT : GRetract T T')
    (P : GPair X X' T) : GPair Y Y' T' where
  P a b k h := ((P.P a b k h).compl₁₂ (R.i.f a a rfl) (R'.i.f b b rfl)).compr₂ (RT.p.f k k rfl)
  leib a a₁ b b₁ k k₁ h ha hb hk y y' := by
    change T'.d k k₁ hk (RT.p.f k k rfl (P.P a b k h (R.i.f a a rfl y) (R'.i.f b b rfl y'))) =
      RT.p.f k₁ k₁ rfl (P.P a₁ b k₁ (by omega) (R.i.f a₁ a₁ rfl (Y.d a a₁ ha y))
          (R'.i.f b b rfl y')) +
        sgn a • RT.p.f k₁ k₁ rfl (P.P a b₁ k₁ (by omega) (R.i.f a a rfl y)
          (R'.i.f b₁ b₁ rfl (Y'.d b b₁ hb y')))
    rw [← ghom_comm_d RT.p, P.leib a a₁ b b₁ k k₁ h ha hb hk, map_add, map_zsmul,
      ghom_comm_d R.i, ghom_comm_d R'.i]

/-- **A Leibniz rule with defect** for a family of bilinear forms `B` on `X × X'`
(tex 4441–4442, the cup-product diagrams): `B(dx, y) + (−1)^a B(x, dy) = Q(x, y)` for
`x ∈ Xᵃ`, `y ∈ X'ᵇ`. Kind: definition. -/
def IsLeibnizDefect {X X' : GCx A} (B Q : ∀ a b : ℤ, X.X a →ₗ[A] X'.X b →ₗ[A] A) : Prop :=
  ∀ (a a₁ b b₁ : ℤ) (ha : a + 1 = a₁) (hb : b + 1 = b₁) (x : X.X a) (y : X'.X b),
    B a₁ b (X.d a a₁ ha x) y + sgn a • B a b₁ x (X'.d b b₁ hb y) = Q a b x y

/-- **Restriction of a family of bilinear forms** along the inclusions (tex 4438–4442):
`B_C(x, y) = B(i x, i′ y)`. Kind: definition. -/
def GRetract.restrictForm (R : GRetract X Y) (R' : GRetract X' Y')
    (B : ∀ a b : ℤ, X.X a →ₗ[A] X'.X b →ₗ[A] A) (a b : ℤ) : Y.X a →ₗ[A] Y'.X b →ₗ[A] A :=
  (B a b).compl₁₂ (R.i.f a a rfl) (R'.i.f b b rfl)

/-- **Forms with Leibniz defect transport** (tex 4441–4442): if `B` has defect `Q`, then
`B(i x, i′ y)` has defect `Q(i x, i′ y)`. Kind: PROVED. -/
theorem GRetract.restrictForm_isLeibnizDefect (R : GRetract X Y) (R' : GRetract X' Y')
    {B Q : ∀ a b : ℤ, X.X a →ₗ[A] X'.X b →ₗ[A] A} (hB : IsLeibnizDefect B Q) :
    IsLeibnizDefect (R.restrictForm R' B) (R.restrictForm R' Q) := by
  intro a a₁ b b₁ ha hb y y'
  change B a₁ b (R.i.f a₁ a₁ rfl (Y.d a a₁ ha y)) (R'.i.f b b rfl y') +
      sgn a • B a b₁ (R.i.f a a rfl y) (R'.i.f b₁ b₁ rfl (Y'.d b b₁ hb y')) =
    Q a b (R.i.f a a rfl y) (R'.i.f b b rfl y')
  rw [ghom_comm_d R.i, ghom_comm_d R'.i]
  exact hB a a₁ b b₁ ha hb _ _

/-- **The cup-product defect** `−β(r x, r′ y)` for chain maps `r : X → L`, `r′ : X' → L'` and
forms `β` on `L × L'` (tex 4441–4442). Kind: definition. -/
def cupDefect {L L' : GCx A} (β : ∀ a b : ℤ, L.X a →ₗ[A] L'.X b →ₗ[A] A) (r : GHom X L)
    (r' : GHom X' L') (a b : ℤ) : X.X a →ₗ[A] X'.X b →ₗ[A] A :=
  -((β a b).compl₁₂ (r.f a a rfl) (r'.f b b rfl))

/-- **Cup-product defects transport** (tex 4441–4442): if `B` has defect `−β(r x, r′ y)`, then
`B(i x, i′ y)` has defect `−β((r ∘ i) x, (r′ ∘ i′) y)`. Kind: PROVED. -/
theorem GRetract.restrictForm_cupDefect (R : GRetract X Y) (R' : GRetract X' Y')
    {L L' : GCx A} {B : ∀ a b : ℤ, X.X a →ₗ[A] X'.X b →ₗ[A] A}
    {β : ∀ a b : ℤ, L.X a →ₗ[A] L'.X b →ₗ[A] A} {r : GHom X L} {r' : GHom X' L'}
    (hB : IsLeibnizDefect B (cupDefect β r r')) :
    IsLeibnizDefect (R.restrictForm R' B) (cupDefect β (ghomComp R.i r) (ghomComp R'.i r')) := by
  intro a a₁ b b₁ ha hb y y'
  exact R.restrictForm_isLeibnizDefect R' hB a a₁ b b₁ ha hb y y'

end Transport

/-! ### Matrix forms over the finite free models -/

section MatrixForms

variable {A : Type} [CommRing A] {rk rk' rk'' rk₁ : ℤ → ℕ}
  {dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rk b)) (Fin (rk a)) A}
  {dC' : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rk' b)) (Fin (rk' a)) A}
  {dC'' : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rk'' b)) (Fin (rk'' a)) A}
  {dC₁ : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rk₁ b)) (Fin (rk₁ a)) A}
  {hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0}
  {hsq' : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC' b c hbc * dC' a b hab = 0}
  {hsq'' : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC'' b c hbc * dC'' a b hab = 0}
  {hsq₁ : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC₁ b c hbc * dC₁ a b hab = 0}

/-- Matrices commuting with the differentials commute as linear maps (tex 4397–4399).
Kind: PROVED (auxiliary). -/
theorem matHom_comm_aux (F : ∀ n : ℤ, Matrix (Fin (rk' n)) (Fin (rk n)) A)
    (hF : ∀ a b (h : a + 1 = b), F b * dC a b h = dC' a b h * F a) (a b : ℤ) (h : a + 1 = b)
    (x : Fin (rk a) → A) :
    Matrix.toLin' (F b) (Matrix.toLin' (dC a b h) x) =
      Matrix.toLin' (dC' a b h) (Matrix.toLin' (F a) x) := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hF]

variable (hsq hsq') in
/-- **The chain map of matrix complexes given by matrices** `F n` with
`F (n+1) d_C = d_C' F n` (tex 4397–4399, "preserving its matrix identities").
Kind: definition (chain-map property PROVED). -/
def matHom (F : ∀ n : ℤ, Matrix (Fin (rk' n)) (Fin (rk n)) A)
    (hF : ∀ a b (h : a + 1 = b), F b * dC a b h = dC' a b h * F a) :
    GHom (matCx rk dC hsq) (matCx rk' dC' hsq') where
  f a b hab := by
    subst hab
    exact Matrix.toLin' (F a)
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    exact matHom_comm_aux F hF i i₁ h₁ x

/-- The component of a chain map of matrix complexes as a linear map of coordinate spaces
(tex 4397–4399). Kind: definition. -/
def ghomLin (φ : GHom (matCx rk dC hsq) (matCx rk' dC' hsq')) (n : ℤ) :
    (Fin (rk n) → A) →ₗ[A] (Fin (rk' n) → A) :=
  φ.f n n rfl

/-- **The matrix of a chain map of matrix complexes** in degree `n` (tex 4397–4399).
Kind: definition. -/
def ghomMatrix (φ : GHom (matCx rk dC hsq) (matCx rk' dC' hsq')) (n : ℤ) :
    Matrix (Fin (rk' n)) (Fin (rk n)) A :=
  LinearMap.toMatrix' (ghomLin φ n)

/-- A chain map of matrix complexes commutes with the matrix differentials, as linear maps
(tex 4397–4399). Kind: PROVED. -/
theorem ghomLin_comm (φ : GHom (matCx rk dC hsq) (matCx rk' dC' hsq')) (a b : ℤ)
    (h : a + 1 = b) :
    ghomLin φ b ∘ₗ Matrix.toLin' (dC a b h) = Matrix.toLin' (dC' a b h) ∘ₗ ghomLin φ a :=
  LinearMap.ext fun x => φ.comm a b a b rfl h h rfl x

/-- **The matrices of a chain map of matrix complexes satisfy** `F (n+1) d_C = d_C' F n`
(tex 4397–4399). Kind: PROVED. -/
theorem ghomMatrix_comm (φ : GHom (matCx rk dC hsq) (matCx rk' dC' hsq')) (a b : ℤ)
    (h : a + 1 = b) : ghomMatrix φ b * dC a b h = dC' a b h * ghomMatrix φ a := by
  have e := congrArg (fun ψ => LinearMap.toMatrix' ψ) (ghomLin_comm φ a b h)
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at e
  exact e

/-- The matrices of `matHom F` are `F` (tex 4397–4399). Kind: PROVED. -/
theorem ghomMatrix_matHom (F : ∀ n : ℤ, Matrix (Fin (rk' n)) (Fin (rk n)) A)
    (hF : ∀ a b (h : a + 1 = b), F b * dC a b h = dC' a b h * F a) (n : ℤ) :
    ghomMatrix (matHom hsq hsq' F hF) n = F n :=
  LinearMap.toMatrix'_toLin' (F n)

/-- A chain map of matrix complexes is `matHom` of its matrices (tex 4397–4399): the two
descriptions are inverse to each other. Kind: PROVED. -/
theorem ghomLin_matHom_ghomMatrix (φ : GHom (matCx rk dC hsq) (matCx rk' dC' hsq'))
    (n : ℤ) :
    ghomLin (matHom hsq hsq' (ghomMatrix φ) (ghomMatrix_comm φ)) n = ghomLin φ n :=
  Matrix.toLin'_toMatrix' (ghomLin φ n)

/-- The matrix of a composite of chain maps of matrix complexes is the product of matrices
(tex 4397–4399). Kind: PROVED. -/
theorem ghomMatrix_comp (φ : GHom (matCx rk dC hsq) (matCx rk' dC' hsq'))
    (ψ : GHom (matCx rk' dC' hsq') (matCx rk'' dC'' hsq'')) (n : ℤ) :
    ghomMatrix (ghomComp φ ψ) n = ghomMatrix ψ n * ghomMatrix φ n :=
  LinearMap.toMatrix'_comp (ghomLin ψ n) (ghomLin φ n)

/-- A family of maps of degree `−k` between matrix complexes as linear maps of coordinate
spaces (tex 4440–4442). Kind: definition. -/
def famLin (k : ℤ)
    (H : ∀ a b : ℤ, b + k = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b)
    (a b : ℤ) (hab : b + k = a) : (Fin (rk a) → A) →ₗ[A] (Fin (rk' b) → A) :=
  H a b hab

/-- **The matrices of a family of maps of degree `−k`** (homotopies, second homotopies) between
matrix complexes (tex 4440–4442). Kind: definition. -/
def famMatrix (k : ℤ)
    (H : ∀ a b : ℤ, b + k = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b)
    (a b : ℤ) (hab : b + k = a) : Matrix (Fin (rk' b)) (Fin (rk a)) A :=
  LinearMap.toMatrix' (famLin k H a b hab)

/-- A homotopy between matrix complexes, as identities of linear maps (tex 4440–4442).
Kind: PROVED. -/
theorem isHomotopy_iff_lin (f g : GHom (matCx rk dC hsq) (matCx rk' dC' hsq'))
    (H : ∀ a b : ℤ, b + 1 = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b) :
    IsHomotopy f g H ↔ ∀ n, ghomLin f n - ghomLin g n =
      Matrix.toLin' (dC' (n - 1) n (by omega)) ∘ₗ famLin 1 H n (n - 1) (by omega) +
        famLin 1 H (n + 1) n rfl ∘ₗ Matrix.toLin' (dC n (n + 1) rfl) :=
  forall_congr' fun _ => ⟨fun h => LinearMap.ext h, fun h x => LinearMap.congr_fun h x⟩

/-- **A homotopy between matrix complexes, as exact matrix identities** (tex 4440–4442):
`F n − G n = d_C' K_n + K_{n+1} d_C`. Kind: PROVED. -/
theorem isHomotopy_iff_matrix (f g : GHom (matCx rk dC hsq) (matCx rk' dC' hsq'))
    (H : ∀ a b : ℤ, b + 1 = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b) :
    IsHomotopy f g H ↔ ∀ n, ghomMatrix f n - ghomMatrix g n =
      dC' (n - 1) n (by omega) * famMatrix 1 H n (n - 1) (by omega) +
        famMatrix 1 H (n + 1) n rfl * dC n (n + 1) rfl := by
  rw [isHomotopy_iff_lin]
  refine forall_congr' fun n => ⟨fun h => ?_, fun h => ?_⟩
  · have e := congrArg (fun ψ => LinearMap.toMatrix' ψ) h
    simp only [map_sub, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at e
    exact e
  · apply LinearMap.toMatrix'.injective
    simp only [map_sub, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
    exact h

/-- A second homotopy between matrix complexes, as identities of linear maps (tex 4441–4442).
Kind: PROVED. -/
theorem isSecondHomotopy_iff_lin
    (H H' : ∀ a b : ℤ, b + 1 = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b)
    (G : ∀ a b : ℤ, b + 2 = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b) :
    IsSecondHomotopy H H' G ↔ ∀ n, famLin 1 H n (n - 1) (by omega) -
        famLin 1 H' n (n - 1) (by omega) =
      Matrix.toLin' (dC' (n - 2) (n - 1) (by omega)) ∘ₗ famLin 2 G n (n - 2) (by omega) -
        famLin 2 G (n + 1) (n - 1) (by omega) ∘ₗ Matrix.toLin' (dC n (n + 1) rfl) :=
  forall_congr' fun _ => ⟨fun h => LinearMap.ext h, fun h x => LinearMap.congr_fun h x⟩

/-- **A second homotopy between matrix complexes, as exact matrix identities** (tex 4441–4442):
`K_n − K'_n = d_C' G_n − G_{n+1} d_C`. Kind: PROVED. -/
theorem isSecondHomotopy_iff_matrix
    (H H' : ∀ a b : ℤ, b + 1 = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b)
    (G : ∀ a b : ℤ, b + 2 = a → (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b) :
    IsSecondHomotopy H H' G ↔ ∀ n, famMatrix 1 H n (n - 1) (by omega) -
        famMatrix 1 H' n (n - 1) (by omega) =
      dC' (n - 2) (n - 1) (by omega) * famMatrix 2 G n (n - 2) (by omega) -
        famMatrix 2 G (n + 1) (n - 1) (by omega) * dC n (n + 1) rfl := by
  rw [isSecondHomotopy_iff_lin]
  refine forall_congr' fun n => ⟨fun h => ?_, fun h => ?_⟩
  · have e := congrArg (fun ψ => LinearMap.toMatrix' ψ) h
    simp only [map_sub, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at e
    exact e
  · apply LinearMap.toMatrix'.injective
    simp only [map_sub, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
    exact h

variable {X X' X'' X₁ : GCx A}

/-- **Transported maps satisfy the exact matrix chain identity** `F (n+1) d_C = d_C' F n`
(tex 4397–4399, 4438–4440). Kind: PROVED. -/
theorem transport_matrix_comm (R : GRetract X (matCx rk dC hsq))
    (R' : GRetract X' (matCx rk' dC' hsq')) (f : GHom X X') (a b : ℤ) (h : a + 1 = b) :
    ghomMatrix (R.transport R' f) b * dC a b h = dC' a b h * ghomMatrix (R.transport R' f) a :=
  ghomMatrix_comm _ a b h

/-- **Transported homotopies satisfy exact matrix identities** (tex 4440–4442):
`F_C n − G_C n = d_C' K_n + K_{n+1} d_C` with `K = p′ H i`. Kind: PROVED. -/
theorem transport_matrix_homotopy (R : GRetract X (matCx rk dC hsq))
    (R' : GRetract X' (matCx rk' dC' hsq')) {f g : GHom X X'}
    {H : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X'.X b} (hH : IsHomotopy f g H) (n : ℤ) :
    ghomMatrix (R.transport R' f) n - ghomMatrix (R.transport R' g) n =
      dC' (n - 1) n (by omega) * famMatrix 1 (R.transportFam R' 1 H) n (n - 1) (by omega) +
        famMatrix 1 (R.transportFam R' 1 H) (n + 1) n rfl * dC n (n + 1) rfl :=
  (isHomotopy_iff_matrix _ _ _).1 (R.transport_isHomotopy R' hH) n

/-- **Transported second homotopies satisfy exact matrix identities** (tex 4441–4442).
Kind: PROVED. -/
theorem transport_matrix_secondHomotopy (R : GRetract X (matCx rk dC hsq))
    (R' : GRetract X' (matCx rk' dC' hsq'))
    {H H' : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X'.X b}
    {G : ∀ a b : ℤ, b + 2 = a → X.X a →ₗ[A] X'.X b} (hG : IsSecondHomotopy H H' G) (n : ℤ) :
    famMatrix 1 (R.transportFam R' 1 H) n (n - 1) (by omega) -
        famMatrix 1 (R.transportFam R' 1 H') n (n - 1) (by omega) =
      dC' (n - 2) (n - 1) (by omega) * famMatrix 2 (R.transportFam R' 2 G) n (n - 2) (by omega) -
        famMatrix 2 (R.transportFam R' 2 G) (n + 1) (n - 1) (by omega) * dC n (n + 1) rfl :=
  (isSecondHomotopy_iff_matrix _ _ _).1 (R.transport_isSecondHomotopy R' hG) n

/-- **Composition of transported maps, as an exact matrix identity** (tex 4440–4442):
`(g f)_C n − g_C n f_C n = d_C″ K_n + K_{n+1} d_C` with `K = p″ g h′ f i`. Kind: PROVED. -/
theorem transport_matrix_comp (R : GRetract X (matCx rk dC hsq))
    (R' : GRetract X' (matCx rk' dC' hsq')) (R'' : GRetract X'' (matCx rk'' dC'' hsq''))
    (f : GHom X X') (g : GHom X' X'') (n : ℤ) :
    ghomMatrix (R.transport R'' (ghomComp f g)) n -
        ghomMatrix (R'.transport R'' g) n * ghomMatrix (R.transport R' f) n =
      dC'' (n - 1) n (by omega) * famMatrix 1 (R.compHomotopy R' R'' f g) n (n - 1) (by omega) +
        famMatrix 1 (R.compHomotopy R' R'' f g) (n + 1) n rfl * dC n (n + 1) rfl := by
  rw [← ghomMatrix_comp]
  exact (isHomotopy_iff_matrix _ _ _).1 (R.transport_comp R' R'' f g) n

/-- **Transported homotopy-commutative squares, as exact matrix identities** (tex 4440–4442).
Kind: PROVED. -/
theorem transport_matrix_square (R : GRetract X (matCx rk dC hsq))
    (R₁ : GRetract X₁ (matCx rk₁ dC₁ hsq₁)) (R' : GRetract X' (matCx rk' dC' hsq'))
    (R'' : GRetract X'' (matCx rk'' dC'' hsq'')) {f : GHom X X'} {g : GHom X' X''}
    {l : GHom X X₁} {k : GHom X₁ X''} {H : ∀ a b : ℤ, b + 1 = a → X.X a →ₗ[A] X''.X b}
    (hH : IsHomotopy (ghomComp f g) (ghomComp l k) H) (n : ℤ) :
    ghomMatrix (R'.transport R'' g) n * ghomMatrix (R.transport R' f) n -
        ghomMatrix (R₁.transport R'' k) n * ghomMatrix (R.transport R₁ l) n =
      dC'' (n - 1) n (by omega) *
          famMatrix 1 (R.squareHomotopy R₁ R' R'' f g l k H) n (n - 1) (by omega) +
        famMatrix 1 (R.squareHomotopy R₁ R' R'' f g l k H) (n + 1) n rfl * dC n (n + 1) rfl := by
  rw [← ghomMatrix_comp, ← ghomMatrix_comp]
  exact (isHomotopy_iff_matrix _ _ _).1 (R.transport_square R₁ R' R'' hH) n

/-- A family of bilinear forms on matrix complexes as bilinear forms on coordinate spaces
(tex 4441–4442). Kind: definition. -/
def formLin
    (B : ∀ a b : ℤ, (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b →ₗ[A] A)
    (a b : ℤ) : (Fin (rk a) → A) →ₗ[A] (Fin (rk' b) → A) →ₗ[A] A :=
  B a b

/-- **The Gram matrices of a family of bilinear forms** on matrix complexes (tex 4441–4442).
Kind: definition. -/
def formMatrix
    (B : ∀ a b : ℤ, (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b →ₗ[A] A)
    (a b : ℤ) : Matrix (Fin (rk a)) (Fin (rk' b)) A :=
  LinearMap.toMatrix₂' A (formLin B a b)

/-- **The dot-product form**: `B(x, y) = x ⬝ᵥ (M *ᵥ y)` for the Gram matrix `M`
(tex 4441–4442). Kind: PROVED. -/
theorem formLin_apply_dotProduct
    (B : ∀ a b : ℤ, (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b →ₗ[A] A)
    (a b : ℤ) (x : Fin (rk a) → A) (y : Fin (rk' b) → A) :
    formLin B a b x y = x ⬝ᵥ (formMatrix B a b *ᵥ y) := by
  rw [← Matrix.toLinearMap₂'_apply', formMatrix, Matrix.toLinearMap₂'_toMatrix']

/-- A Leibniz rule with defect on matrix complexes, as identities of bilinear maps
(tex 4441–4442). Kind: PROVED. -/
theorem isLeibnizDefect_iff_lin
    (B Q : ∀ a b : ℤ, (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b →ₗ[A] A) :
    IsLeibnizDefect B Q ↔ ∀ (a a₁ b b₁ : ℤ) (ha : a + 1 = a₁) (hb : b + 1 = b₁),
      (formLin B a₁ b).comp (Matrix.toLin' (dC a a₁ ha)) +
          sgn a • (formLin B a b₁).compl₂ (Matrix.toLin' (dC' b b₁ hb)) = formLin Q a b :=
  ⟨fun h a a₁ b b₁ ha hb => LinearMap.ext₂ (h a a₁ b b₁ ha hb),
    fun h a a₁ b b₁ ha hb x y => LinearMap.congr_fun₂ (h a a₁ b b₁ ha hb) x y⟩

/-- **A Leibniz rule with defect on matrix complexes, as exact matrix identities**
(tex 4441–4442): `d_Cᵀ M_{a+1,b} + (−1)^a M_{a,b+1} d_C' = N_{a,b}` for the Gram matrices `M`
of `B` and `N` of `Q`. Kind: PROVED. -/
theorem isLeibnizDefect_iff_matrix
    (B Q : ∀ a b : ℤ, (matCx rk dC hsq).X a →ₗ[A] (matCx rk' dC' hsq').X b →ₗ[A] A) :
    IsLeibnizDefect B Q ↔ ∀ (a a₁ b b₁ : ℤ) (ha : a + 1 = a₁) (hb : b + 1 = b₁),
      (dC a a₁ ha)ᵀ * formMatrix B a₁ b + sgn a • (formMatrix B a b₁ * dC' b b₁ hb) =
        formMatrix Q a b := by
  rw [isLeibnizDefect_iff_lin]
  refine forall_congr' fun a => forall_congr' fun a₁ => forall_congr' fun b =>
    forall_congr' fun b₁ => forall_congr' fun ha => forall_congr' fun hb =>
      ⟨fun h => ?_, fun h => ?_⟩
  · have e := congrArg (fun ψ => LinearMap.toMatrix₂' A ψ) h
    simp only [map_add, map_zsmul, LinearMap.toMatrix₂'_comp, LinearMap.toMatrix₂'_compl₂,
      LinearMap.toMatrix'_toLin'] at e
    exact e
  · apply (LinearMap.toMatrix₂' A).injective
    simp only [map_add, map_zsmul, LinearMap.toMatrix₂'_comp, LinearMap.toMatrix₂'_compl₂,
      LinearMap.toMatrix'_toLin']
    exact h

/-- **The Gram matrix of a cup-product defect** `−β(r x, r′ y)` on matrix complexes is
`−(Rᵀ M_β R′)` (tex 4441–4442). Kind: PROVED. -/
theorem formMatrix_cupDefect
    (β : ∀ a b : ℤ, (matCx rk'' dC'' hsq'').X a →ₗ[A] (matCx rk₁ dC₁ hsq₁).X b →ₗ[A] A)
    (ρ : GHom (matCx rk dC hsq) (matCx rk'' dC'' hsq''))
    (ρ' : GHom (matCx rk' dC' hsq') (matCx rk₁ dC₁ hsq₁)) (a b : ℤ) :
    formMatrix (cupDefect β ρ ρ') a b =
      -((ghomMatrix ρ a)ᵀ * formMatrix β a b * ghomMatrix ρ' b) := by
  have e := LinearMap.toMatrix₂'_compl₁₂ (formLin β a b) (ghomLin ρ a) (ghomLin ρ' b)
  change _ = -((LinearMap.toMatrix' (ghomLin ρ a))ᵀ * LinearMap.toMatrix₂' A (formLin β a b) *
    LinearMap.toMatrix' (ghomLin ρ' b))
  rw [← e]
  ext i j
  rfl

/-- **Transported forms with Leibniz defect satisfy exact matrix identities** (tex 4441–4442):
the Gram matrices `M` of `B(i x, i′ y)` satisfy `d_Cᵀ M + (−1)^a M d_C' = N` with `N` the Gram
matrix of `Q(i x, i′ y)`. Kind: PROVED. -/
theorem transport_matrix_form (R : GRetract X (matCx rk dC hsq))
    (R' : GRetract X' (matCx rk' dC' hsq')) {B Q : ∀ a b : ℤ, X.X a →ₗ[A] X'.X b →ₗ[A] A}
    (hB : IsLeibnizDefect B Q) (a a₁ b b₁ : ℤ) (ha : a + 1 = a₁) (hb : b + 1 = b₁) :
    (dC a a₁ ha)ᵀ * formMatrix (R.restrictForm R' B) a₁ b +
        sgn a • (formMatrix (R.restrictForm R' B) a b₁ * dC' b b₁ hb) =
      formMatrix (R.restrictForm R' Q) a b :=
  (isLeibnizDefect_iff_matrix _ _).1 (R.restrictForm_isLeibnizDefect R' hB) a a₁ b b₁ ha hb

/-- **Transported cup-product forms, as exact matrix identities** (tex 4441–4442): if `B` has
defect `−β(r x, r′ y)` with `r`, `r′` into matrix complexes, the Gram matrices `M` of
`B(i x, i′ y)` satisfy `d_Cᵀ M + (−1)^a M d_C' = −(Rᵀ M_β R′)` with `R`, `R′` the matrices of
`r ∘ i`, `r′ ∘ i′`. Kind: PROVED. -/
theorem transport_matrix_cupDefect (R : GRetract X (matCx rk dC hsq))
    (R' : GRetract X' (matCx rk' dC' hsq')) {B : ∀ a b : ℤ, X.X a →ₗ[A] X'.X b →ₗ[A] A}
    {β : ∀ a b : ℤ, (matCx rk'' dC'' hsq'').X a →ₗ[A] (matCx rk₁ dC₁ hsq₁).X b →ₗ[A] A}
    {r : GHom X (matCx rk'' dC'' hsq'')} {r' : GHom X' (matCx rk₁ dC₁ hsq₁)}
    (hB : IsLeibnizDefect B (cupDefect β r r')) (a a₁ b b₁ : ℤ) (ha : a + 1 = a₁)
    (hb : b + 1 = b₁) :
    (dC a a₁ ha)ᵀ * formMatrix (R.restrictForm R' B) a₁ b +
        sgn a • (formMatrix (R.restrictForm R' B) a b₁ * dC' b b₁ hb) =
      -((ghomMatrix (ghomComp R.i r) a)ᵀ * formMatrix β a b *
        ghomMatrix (ghomComp R'.i r') b) := by
  rw [← formMatrix_cupDefect]
  exact (isLeibnizDefect_iff_matrix _ _).1 (R.restrictForm_cupDefect R' hB) a a₁ b b₁ ha hb

end MatrixForms

/-! ### Non-vacuity: the identity retract -/

section Refl

variable {A : Type} [CommRing A]

/-- The identity chain map of a relation-indexed complex (tex 4397–4399, non-vacuity).
Kind: definition. -/
def gHomId (X : GCx A) : GHom X X where
  f a b h := by
    subst h
    exact LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    rfl

/-- **The identity retract** of any complex: `i = p = 1`, `h = 0` (tex 4397–4399, non-vacuity).
Kind: definition (identities PROVED). -/
def GRetract.refl (X : GCx A) : GRetract X X where
  i := gHomId X
  p := gHomId X
  h _ _ _ := 0
  p_i _ _ := rfl
  homotopy n x := by
    change x - x = X.d (n - 1) n (by omega) ((0 : X.X n →ₗ[A] X.X (n - 1)) x) +
      (0 : X.X (n + 1) →ₗ[A] X.X n) (X.d n (n + 1) rfl x)
    rw [sub_self, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero]
  h_h _ _ _ _ _ _ := rfl
  h_i _ _ _ _ := rfl
  p_h _ _ _ _ := rfl

/-- **Transport along identity retracts is the identity** (tex 4438–4440, non-vacuity).
Kind: PROVED (definitional). -/
theorem transport_refl {X X' : GCx A} (f : GHom X X') (n : ℤ) (x : X.X n) :
    ((GRetract.refl X).transport (GRetract.refl X') f).f n n rfl x = f.f n n rfl x :=
  rfl

/-- **Non-vacuity**: transporting the identity of the constant complex `ℤ` along identity
retracts gives a nonzero map (tex 4438–4440). Kind: PROVED. -/
theorem transport_refl_constId_ne_zero :
    ((GRetract.refl (constCx ℤ)).transport (GRetract.refl (constCx ℤ)) (constId ℤ)).f 0 0 rfl
      (show (constCx ℤ).X 0 from (1 : ℤ)) ≠ 0 := by
  change (1 : ℤ) ≠ 0
  exact one_ne_zero

/-- **Non-vacuity of graded models**: every matrix complex is a graded finite free model of
itself via the identity retract (tex 4397–4399). Kind: definition. -/
def matCx.gradedModel (rank : ℤ → ℕ)
    (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0) :
    GradedModel (matCx rank dC hsq) :=
  ⟨rank, dC, hsq, GRetract.refl _⟩

end Refl

end ZInQ.Manuscript.RC.Limits
