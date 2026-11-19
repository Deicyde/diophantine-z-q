import ZInQKernel.Contrib.OneProof.RC.Limits.GradedTransport
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality

/-!
# Lane RC31, round 3: graded models of cones and of duals

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451): "Every fixed
finite diagram of maps and homotopies, including the duality and local-condition data used here,
transports to these models", and tex 4385–4388: "The same retained data include the integral
duality maps, their homotopy inverses, and the homotopies expressing compatibility of duality with
localization". To transport the global duality map `G → Hom(G'_c, S)[−3]` (Nekovář, Selmer
complexes, 5.4.3) to the finite free models one needs models of cones and of duals.

* `GRetract.cone R f`: a retract `R` of `X` onto `Y` and a chain map `f : X → L` give a retract
  of `Cone(f)[−1]` onto `Cone(f ∘ i)[−1]`, with inclusion `(b, y) ↦ (i b, y)`, projection
  `(x, y) ↦ (p x, y − f (h x))` and homotopy `(x, y) ↦ (h x, 0)`.
* `GRetract.dual R m`: a retract of `Hom(X, A)[−m]` onto `Hom(Y, A)[−m]`, with inclusion `p^∨`,
  projection `i^∨` and homotopy `φ ↦ (−1)^a φ ∘ h` in degree `a`.
* `GRetract.transportMap`: the transported map `p' Φ i`, a quasi-isomorphism when `Φ` is.
* Finiteness, freeness and boundedness of the matrix complexes and of the duals of their cones,
  and `exists_homotopyEquiv_of_quasiIso_matCx`: a quasi-isomorphism from a bounded matrix complex
  to the dual of a bounded finite free cone is a homotopy equivalence.
* Non-vacuity: the identity retract, its cone and its dual.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Limits

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {A : Type} [CommRing A]

/-! ### General index lemmas -/

section Index

variable {X Y : GCx A}

/-- The homotopy identity `1 − i p = d h + h d` with arbitrary index expressions for the
neighbouring degrees (tex 4437). Kind: PROVED. -/
theorem GRetract.homotopy_of (R : GRetract X Y) (n a b : ℤ) (ha : a + 1 = n) (hb : n + 1 = b)
    (x : X.X n) :
    x - R.i.f n n rfl (R.p.f n n rfl x) =
      X.d a n ha (R.h n a ha x) + R.h b n hb (X.d n b hb x) := by
  obtain rfl : a = n - 1 := by omega
  obtain rfl : b = n + 1 := by omega
  exact R.homotopy n x

/-- Components of a composite of chain maps may be read off at either index (tex 4440:
"transport by `f ↦ p' f i`"). Kind: PROVED. -/
theorem GHom.comp_congr {L : GCx A} (u : GHom Y X) (v : GHom X L) (i j : ℤ) (h : i = j)
    (b : Y.X i) : v.f j j rfl (u.f i j h b) = v.f i j h (u.f i i rfl b) := by
  subst h
  rfl

end Index

/-! ### The model of a cone -/

section Cone

variable {X Y L : GCx A}

/-- The inclusion `(b, y) ↦ (i b, y)` of `Cone(f i)[−1]` into `Cone(f)[−1]` in degree `n`
(tex 4440). Kind: definition. -/
def coneInclFun (R : GRetract X Y) (f : GHom X L) (n : ℤ) :
    (coneCx (ghomComp R.i f)).X n →ₗ[A] (coneCx f).X n :=
  LinearMap.prodMap (R.i.f n n rfl) (LinearMap.id : L.X (n - 1) →ₗ[A] L.X (n - 1))

/-- The projection `(x, y) ↦ (p x, y − f (h x))` of `Cone(f)[−1]` onto `Cone(f i)[−1]` in
degree `n` (tex 4440). Kind: definition. -/
def coneProjFun (R : GRetract X Y) (f : GHom X L) (n : ℤ) :
    (coneCx f).X n →ₗ[A] (coneCx (ghomComp R.i f)).X n :=
  LinearMap.prod (R.p.f n n rfl ∘ₗ LinearMap.fst A (X.X n) (L.X (n - 1)))
    (LinearMap.snd A (X.X n) (L.X (n - 1)) -
      f.f (n - 1) (n - 1) rfl ∘ₗ R.h n (n - 1) (by omega) ∘ₗ LinearMap.fst A (X.X n) (L.X (n - 1)))

/-- The homotopy `(x, y) ↦ (h x, 0)` on `Cone(f)[−1]`, of degree `−1` (tex 4440). Kind:
definition. -/
def coneHtpy (R : GRetract X Y) (f : GHom X L) (a b : ℤ) (hab : b + 1 = a) :
    (coneCx f).X a →ₗ[A] (coneCx f).X b :=
  LinearMap.prod (R.h a b hab ∘ₗ LinearMap.fst A (X.X a) (L.X (a - 1))) 0

/-- The key identity behind the chain map property of the cone projection: applying `f` to
`1 − i p = d h + h d` (tex 4437, 4440). Kind: PROVED. -/
theorem cone_proj_aux (R : GRetract X Y) (f : GHom X L) (n n₁ k : ℤ) (h₁ : n + 1 = n₁)
    (hk : n = k) (e : X.X n) :
    f.f n k hk e - f.f k k rfl (R.h n₁ k (by omega) (X.d n n₁ h₁ e)) =
      f.f k k rfl (R.i.f n k hk (R.p.f n n rfl e)) +
        L.d (n - 1) k (by omega) (f.f (n - 1) (n - 1) rfl (R.h n (n - 1) (by omega) e)) := by
  subst hk h₁
  have H := congrArg (f.f n n rfl) (R.homotopy n e)
  have c := f.comm (n - 1) n (n - 1) n rfl (by omega) (by omega) rfl (R.h n (n - 1) (by omega) e)
  rw [map_sub, map_add, c] at H
  linear_combination (norm := abel) H

/-- **The model of a cone** (tex 4391–4451, 4385–4388): a normalized graded deformation retract
`R` of `X` onto `Y` and a chain map `f : X → L` give a normalized graded deformation retract of
`Cone(f)[−1]` onto `Cone(f ∘ i)[−1]`, with inclusion `(b, y) ↦ (i b, y)`, projection
`(x, y) ↦ (p x, y − f (h x))` and homotopy `(x, y) ↦ (h x, 0)`. Kind: definition (PROVED
identities). -/
def GRetract.cone (R : GRetract X Y) (f : GHom X L) :
    GRetract (coneCx f) (coneCx (ghomComp R.i f)) where
  i :=
    { f := fun i j h => by subst h; exact coneInclFun R f i
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj x
        subst hij hj
        obtain ⟨b, y⟩ := x
        refine Prod.ext ?_ ?_
        · exact R.i.comm i i₁ i i₁ rfl h₁ h₂ rfl b
        · change f.f (i₁ - 1) (i₁ - 1) rfl (R.i.f i (i₁ - 1) (by omega) b) -
              L.d (i - 1) (i₁ - 1) (by omega) y =
            f.f i (i₁ - 1) (by omega) (R.i.f i i rfl b) - L.d (i - 1) (i₁ - 1) (by omega) y
          rw [GHom.comp_congr] }
  p :=
    { f := fun i j h => by subst h; exact coneProjFun R f i
      comm := by
        intro i i₁ j j₁ hij h₁ h₂ hj x
        subst hij hj
        obtain ⟨e, z⟩ := x
        refine Prod.ext ?_ ?_
        · exact R.p.comm i i₁ i i₁ rfl h₁ h₂ rfl e
        · change (f.f i (i₁ - 1) (by omega) e - L.d (i - 1) (i₁ - 1) (by omega) z) -
              f.f (i₁ - 1) (i₁ - 1) rfl (R.h i₁ (i₁ - 1) (by omega) (X.d i i₁ h₁ e)) =
            f.f (i₁ - 1) (i₁ - 1) rfl (R.i.f i (i₁ - 1) (by omega) (R.p.f i i rfl e)) -
              L.d (i - 1) (i₁ - 1) (by omega)
                (z - f.f (i - 1) (i - 1) rfl (R.h i (i - 1) (by omega) e))
          have H := cone_proj_aux R f i i₁ (i₁ - 1) h₁ (by omega) e
          rw [map_sub]
          linear_combination (norm := abel) H }
  h := coneHtpy R f
  p_i := by
    intro n y
    obtain ⟨b, z⟩ := y
    change (R.p.f n n rfl (R.i.f n n rfl b),
      z - f.f (n - 1) (n - 1) rfl (R.h n (n - 1) (by omega) (R.i.f n n rfl b))) = (b, z)
    rw [R.p_i, R.h_i, map_zero, sub_zero]
  homotopy := by
    intro n x
    obtain ⟨e, z⟩ := x
    refine Prod.ext ?_ ?_
    · exact R.homotopy n e
    · change z - (z - f.f (n - 1) (n - 1) rfl (R.h n (n - 1) (by omega) e)) =
        (f.f (n - 1) (n - 1) (by omega) (R.h n (n - 1) (by omega) e) -
          L.d (n - 1 - 1) (n - 1) (by omega) 0) + 0
      rw [map_zero, sub_zero, add_zero, sub_sub_cancel]
  h_h := by
    intro a b c hab hbc x
    obtain ⟨e, z⟩ := x
    change (R.h b c hbc (R.h a b hab e), (0 : L.X (c - 1))) = (0, 0)
    rw [R.h_h]
  h_i := by
    intro a b hab y
    obtain ⟨e, z⟩ := y
    change (R.h a b hab (R.i.f a a rfl e), (0 : L.X (b - 1))) = (0, 0)
    rw [R.h_i]
  p_h := by
    intro a b hab x
    obtain ⟨e, z⟩ := x
    change (R.p.f b b rfl (R.h a b hab e),
      (0 : L.X (b - 1)) - f.f (b - 1) (b - 1) rfl (R.h b (b - 1) (by omega) (R.h a b hab e))) =
        (0, 0)
    rw [R.p_h, R.h_h, map_zero, sub_zero]

/-- The inclusion of the cone model is `(b, y) ↦ (i b, y)`. Kind: PROVED (definitional). -/
theorem GRetract.cone_i_apply (R : GRetract X Y) (f : GHom X L) (n : ℤ) (b : Y.X n)
    (y : L.X (n - 1)) : (R.cone f).i.f n n rfl (b, y) = (R.i.f n n rfl b, y) :=
  rfl

/-- The projection of the cone model is `(x, y) ↦ (p x, y − f (h x))`. Kind: PROVED
(definitional). -/
theorem GRetract.cone_p_apply (R : GRetract X Y) (f : GHom X L) (n : ℤ) (x : X.X n)
    (y : L.X (n - 1)) : (R.cone f).p.f n n rfl (x, y) =
      (R.p.f n n rfl x, y - f.f (n - 1) (n - 1) rfl (R.h n (n - 1) (by omega) x)) :=
  rfl

/-- The homotopy of the cone model is `(x, y) ↦ (h x, 0)`. Kind: PROVED (definitional). -/
theorem GRetract.cone_h_apply (R : GRetract X Y) (f : GHom X L) (a b : ℤ) (hab : b + 1 = a)
    (x : X.X a) (y : L.X (a - 1)) : (R.cone f).h a b hab (x, y) = (R.h a b hab x, 0) :=
  rfl

end Cone

/-! ### The model of a dual -/

section Dual

variable {X Y : GCx A}

/-- **The model of a dual** (tex 4391–4451, 4385–4388; the dual `Hom(−, A)[−m]` as used for
Nekovář, Selmer complexes, 5.4.3): a normalized graded deformation retract `R` of `X` onto `Y`
gives a normalized graded deformation retract of `Hom(X, A)[−m]` onto `Hom(Y, A)[−m]`, with
inclusion `p^∨`, projection `i^∨`, and homotopy `φ ↦ (−1)^a φ ∘ h` from degree `a` to `a − 1`.
Kind: definition (PROVED identities). -/
def GRetract.dual (R : GRetract X Y) (m : ℤ) : GRetract (dualCx X m) (dualCx Y m) where
  i := dualHom R.p m
  p := dualHom R.i m
  h a b hab := (sgn a) • (R.h (m - b) (m - a) (by omega)).dualMap
  p_i := by
    intro n φ
    refine dualCx_ext fun y => ?_
    change asDual φ (R.p.f (m - n) (m - n) rfl (R.i.f (m - n) (m - n) rfl y)) = asDual φ y
    rw [R.p_i]
  homotopy := by
    intro n φ
    refine dualCx_ext fun x => ?_
    have H := R.homotopy_of (m - n) (m - (n + 1)) (m - (n - 1)) (by omega) (by omega) x
    change asDual φ x - asDual φ (R.i.f (m - n) (m - n) rfl (R.p.f (m - n) (m - n) rfl x)) =
      (-(sgn (n - 1))) • (sgn n • asDual φ
          (R.h (m - (n - 1)) (m - n) (by omega) (X.d (m - n) (m - (n - 1)) (by omega) x))) +
        sgn (n + 1) • ((-(sgn n)) • asDual φ
          (X.d (m - (n + 1)) (m - n) (by omega) (R.h (m - n) (m - (n + 1)) (by omega) x)))
    simp only [sgn_pred, sgn_succ, neg_neg, smul_smul, neg_mul_neg, sgn_mul_self, one_smul]
    rw [← map_sub, H, map_add, add_comm]
  h_h := by
    intro a b c hab hbc φ
    refine dualCx_ext fun x => ?_
    change sgn b • (sgn a • asDual φ (R.h (m - b) (m - a) (by omega)
      (R.h (m - c) (m - b) (by omega) x))) = 0
    rw [R.h_h, map_zero, smul_zero, smul_zero]
  h_i := by
    intro a b hab ψ
    refine dualCx_ext fun x => ?_
    change sgn a • asDual ψ (R.p.f (m - a) (m - a) rfl (R.h (m - b) (m - a) (by omega) x)) = 0
    rw [R.p_h, map_zero, smul_zero]
  p_h := by
    intro a b hab φ
    refine dualCx_ext fun x => ?_
    change sgn a • asDual φ (R.h (m - b) (m - a) (by omega) (R.i.f (m - b) (m - b) rfl x)) = 0
    rw [R.h_i, map_zero, smul_zero]

/-- The homotopy of the dual model is `φ ↦ (−1)^a φ ∘ h`. Kind: PROVED (definitional). -/
theorem GRetract.dual_h_apply (R : GRetract X Y) (m a b : ℤ) (hab : b + 1 = a)
    (φ : (dualCx X m).X a) (x : X.X (m - b)) :
    asDual ((R.dual m).h a b hab φ) x = sgn a • asDual φ (R.h (m - b) (m - a) (by omega) x) :=
  rfl

end Dual

/-! ### Transport of quasi-isomorphisms -/

section Transport

variable {X Y X' Y' : GCx A}

/-- **`GHom.toCC` of a composite is the composite** (tex 4440). Kind: PROVED. -/
theorem toCC_ghomComp {Z : GCx A} (f : GHom X Y) (g : GHom Y Z) :
    GHom.toCC (ghomComp f g) = GHom.toCC f ≫ GHom.toCC g :=
  (GHom.toCC_comp f g).symm

/-- **The transported map** `p' Φ i : Y → Y'` of a chain map `Φ : X → X'` along retracts of `X`
onto `Y` and of `X'` onto `Y'` (tex 4440: "Transport any fixed finite collection of arithmetic
maps by `f ↦ p' f i`"). Kind: definition. -/
def GRetract.transportMap (R : GRetract X Y) (R' : GRetract X' Y') (Φ : GHom X X') : GHom Y Y' :=
  ghomComp (ghomComp R.i Φ) R'.p

/-- The transported map is a composite of three Mathlib chain maps. Kind: PROVED. -/
theorem GRetract.toCC_transportMap (R : GRetract X Y) (R' : GRetract X' Y') (Φ : GHom X X') :
    GHom.toCC (R.transportMap R' Φ) = GHom.toCC R.i ≫ GHom.toCC Φ ≫ GHom.toCC R'.p :=
  rfl

/-- **Transport preserves quasi-isomorphisms** (tex 4440–4442, 4385–4388: the integral duality
maps transport to the models): if `Φ` is a quasi-isomorphism, so is `p' Φ i`. Kind: PROVED. -/
theorem GRetract.quasiIso_transportMap (R : GRetract X Y) (R' : GRetract X' Y')
    (Φ : GHom X X') (hΦ : QuasiIso (GHom.toCC Φ)) :
    QuasiIso (GHom.toCC (R.transportMap R' Φ)) := by
  have := R.quasiIso_i
  have := R'.quasiIso_p
  rw [GRetract.toCC_transportMap]
  infer_instance

end Transport

/-! ### Finiteness, freeness and boundedness -/

section Finite

variable (rank : ℤ → ℕ) (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A)
  (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0)

/-- The terms of the matrix complex are free (tex 4395). Kind: PROVED. -/
instance matCx_free (n : ℤ) : Module.Free A ((matCx rank dC hsq).X n) :=
  inferInstanceAs (Module.Free A (Fin (rank n) → A))

/-- The terms of the matrix complex are finite (tex 4395). Kind: PROVED. -/
instance matCx_finite (n : ℤ) : Module.Finite A ((matCx rank dC hsq).X n) :=
  inferInstanceAs (Module.Finite A (Fin (rank n) → A))

/-- The terms of the Mathlib matrix complex are free (tex 4395). Kind: PROVED. -/
instance matCx_toCC_free (n : ℤ) : Module.Free A ((matCx rank dC hsq).toCC.X n) :=
  inferInstanceAs (Module.Free A (Fin (rank n) → A))

/-- The terms of the Mathlib matrix complex are finite (tex 4395). Kind: PROVED. -/
instance matCx_toCC_finite (n : ℤ) : Module.Finite A ((matCx rank dC hsq).toCC.X n) :=
  inferInstanceAs (Module.Finite A (Fin (rank n) → A))

/-- A matrix complex vanishing below `lo` is strictly `≥ lo` (tex 4395: "bounded"). Kind:
PROVED. -/
theorem matCx_isStrictlyGE (lo : ℤ) (hr : ∀ k, k < lo → rank k = 0) :
    (matCx rank dC hsq).toCC.IsStrictlyGE lo := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have : Subsingleton (Fin (rank i) → A) := by
    rw [hr i hi]
    infer_instance
  exact @ModuleCat.isZero_of_subsingleton A _ ((matCx rank dC hsq).toCC.X i) this

/-- A matrix complex vanishing above `hi` is strictly `≤ hi` (tex 4395: "bounded"). Kind:
PROVED. -/
theorem matCx_isStrictlyLE (hi : ℤ) (hr : ∀ k, hi < k → rank k = 0) :
    (matCx rank dC hsq).toCC.IsStrictlyLE hi := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi'
  have : Subsingleton (Fin (rank i) → A) := by
    rw [hr i hi']
    infer_instance
  exact @ModuleCat.isZero_of_subsingleton A _ ((matCx rank dC hsq).toCC.X i) this

variable {E L : GCx A}

/-- The terms of a cone of complexes with free terms are free. Kind: PROVED. -/
instance coneCx_free [∀ n, Module.Free A (E.X n)] [∀ n, Module.Free A (L.X n)] (f : GHom E L)
    (n : ℤ) : Module.Free A ((coneCx f).X n) :=
  inferInstanceAs (Module.Free A (E.X n × L.X (n - 1)))

/-- The terms of a cone of complexes with finite terms are finite. Kind: PROVED. -/
instance coneCx_finite [∀ n, Module.Finite A (E.X n)] [∀ n, Module.Finite A (L.X n)]
    (f : GHom E L) (n : ℤ) : Module.Finite A ((coneCx f).X n) :=
  inferInstanceAs (Module.Finite A (E.X n × L.X (n - 1)))

/-- The terms of the dual of a complex with finite free terms are free (tex 4385–4388; Nekovář,
Selmer complexes, 5.4.3). Kind: PROVED. -/
instance dualCx_free (C : GCx A) [∀ n, Module.Free A (C.X n)] [∀ n, Module.Finite A (C.X n)]
    (m n : ℤ) : Module.Free A ((dualCx C m).X n) :=
  inferInstanceAs (Module.Free A (Module.Dual A (C.X (m - n))))

/-- The terms of the dual of a complex with finite free terms are finite (tex 4385–4388;
Nekovář, Selmer complexes, 5.4.3). Kind: PROVED. -/
instance dualCx_finite (C : GCx A) [∀ n, Module.Free A (C.X n)] [∀ n, Module.Finite A (C.X n)]
    (m n : ℤ) : Module.Finite A ((dualCx C m).X n) :=
  inferInstanceAs (Module.Finite A (Module.Dual A (C.X (m - n))))

/-- The terms of the Mathlib dual complex of a complex with finite free terms are free (tex
4385–4388). Kind: PROVED. -/
instance dualCx_toCC_free (C : GCx A) [∀ n, Module.Free A (C.X n)]
    [∀ n, Module.Finite A (C.X n)] (m n : ℤ) : Module.Free A ((dualCx C m).toCC.X n) :=
  inferInstanceAs (Module.Free A (Module.Dual A (C.X (m - n))))

/-- The terms of the Mathlib dual complex of a complex with finite free terms are finite (tex
4385–4388). Kind: PROVED. -/
instance dualCx_toCC_finite (C : GCx A) [∀ n, Module.Free A (C.X n)]
    [∀ n, Module.Finite A (C.X n)] (m n : ℤ) : Module.Finite A ((dualCx C m).toCC.X n) :=
  inferInstanceAs (Module.Finite A (Module.Dual A (C.X (m - n))))

variable {rank dC hsq}

/-- A cone term `A^{rank k} × L^{k−1}` vanishes when `rank k = 0` and `L^{k−1}` is zero. Kind:
PROVED. -/
theorem coneCx_matCx_subsingleton (f : GHom (matCx rank dC hsq) L) (k : ℤ) (hr : rank k = 0)
    (hL : Subsingleton (L.X (k - 1))) : Subsingleton ((coneCx f).X k) := by
  have : Subsingleton (Fin (rank k) → A) := by
    rw [hr]
    infer_instance
  exact inferInstanceAs (Subsingleton ((Fin (rank k) → A) × L.X (k - 1)))

/-- The dual of a vanishing cone term vanishes. Kind: PROVED. -/
theorem dualCx_coneCx_subsingleton (f : GHom (matCx rank dC hsq) L) (m n : ℤ)
    (hr : rank (m - n) = 0) (hL : Subsingleton (L.X (m - n - 1))) :
    Subsingleton ((dualCx (coneCx f) m).toCC.X n) := by
  have := coneCx_matCx_subsingleton f (m - n) hr hL
  exact inferInstanceAs (Subsingleton (Module.Dual A ((coneCx f).X (m - n))))

/-- **Lower bound for the dual of a cone** (tex 4385–4388, 4395): if `rank k = 0` for `k > hi`
and `L^k = 0` for `k > hi − 1`, then `Hom(Cone(f)[−1], A)[−m]` is strictly `≥ m − hi`. Kind:
PROVED. -/
theorem dualCx_coneCx_isStrictlyGE (f : GHom (matCx rank dC hsq) L) (m hi : ℤ)
    (hr : ∀ k, hi < k → rank k = 0) (hL : ∀ k, hi - 1 < k → Subsingleton (L.X k)) :
    (dualCx (coneCx f) m).toCC.IsStrictlyGE (m - hi) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi'
  have := dualCx_coneCx_subsingleton f m i (hr _ (by omega)) (hL _ (by omega))
  exact ModuleCat.isZero_of_subsingleton _

/-- **Upper bound for the dual of a cone** (tex 4385–4388, 4395): if `rank k = 0` for `k < lo`
and `L^k = 0` for `k < lo − 1`, then `Hom(Cone(f)[−1], A)[−m]` is strictly `≤ m − lo`. Kind:
PROVED. -/
theorem dualCx_coneCx_isStrictlyLE (f : GHom (matCx rank dC hsq) L) (m lo : ℤ)
    (hr : ∀ k, k < lo → rank k = 0) (hL : ∀ k, k < lo - 1 → Subsingleton (L.X k)) :
    (dualCx (coneCx f) m).toCC.IsStrictlyLE (m - lo) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi'
  have := dualCx_coneCx_subsingleton f m i (hr _ (by omega)) (hL _ (by omega))
  exact ModuleCat.isZero_of_subsingleton _

/-- **Bounds for the dual of a cone, common-interval form** (tex 4385–4388, 4395): if
`rank k = 0` and `L^k = 0` for `k ∉ [lo, hi]`, then `Hom(Cone(f)[−1], A)[−m]` is strictly
concentrated in `[m − hi − 1, m − lo]`. Kind: PROVED. -/
theorem dualCx_coneCx_bounds (f : GHom (matCx rank dC hsq) L) (m lo hi : ℤ)
    (hr : ∀ k, k < lo ∨ hi < k → rank k = 0)
    (hL : ∀ k, k < lo ∨ hi < k → Subsingleton (L.X k)) :
    (dualCx (coneCx f) m).toCC.IsStrictlyGE (m - hi - 1) ∧
      (dualCx (coneCx f) m).toCC.IsStrictlyLE (m - lo) := by
  refine ⟨?_, dualCx_coneCx_isStrictlyLE f m lo (fun k hk => hr k (Or.inl hk))
    (fun k hk => hL k (Or.inl (by omega)))⟩
  have := dualCx_coneCx_isStrictlyGE f m (hi + 1) (fun k hk => hr k (Or.inr (by omega)))
    (fun k hk => hL k (Or.inr (by omega)))
  rwa [sub_add_eq_sub_sub] at this

/-- **A quasi-isomorphism from a bounded matrix complex to the dual of a bounded finite free
cone is a homotopy equivalence** (tex 4385–4388: "the integral duality maps, their homotopy
inverses"; tex 4391–4451; Nekovář, Selmer complexes, 5.4.3). Here `L` has finite free terms, the
source ranks vanish outside `[a, b]`, and the cone data vanish so that the dual is concentrated
in `[a, b]` as well: `rank k = 0` for `k ∉ [m − b, m − a]` and `L^k = 0` for
`k ∉ [m − b − 1, m − a − 1]`. Kind: PROVED. -/
theorem exists_homotopyEquiv_of_quasiIso_matCx {rank' : ℤ → ℕ}
    {dC' : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank' b)) (Fin (rank' a)) A}
    {hsq' : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC' b c hbc * dC' a b hab = 0}
    [∀ n, Module.Free A (L.X n)] [∀ n, Module.Finite A (L.X n)]
    (f : GHom (matCx rank dC hsq) L) (m a b : ℤ)
    (h1 : ∀ k, k < a ∨ b < k → rank' k = 0)
    (hr : ∀ k, k < m - b ∨ m - a < k → rank k = 0)
    (hL : ∀ k, k < m - b - 1 ∨ m - a - 1 < k → Subsingleton (L.X k))
    (Φ : GHom (matCx rank' dC' hsq') (dualCx (coneCx f) m)) (hΦ : QuasiIso (GHom.toCC Φ)) :
    ∃ e : HomotopyEquiv (matCx rank' dC' hsq').toCC (dualCx (coneCx f) m).toCC,
      e.hom = GHom.toCC Φ := by
  have := matCx_isStrictlyGE rank' dC' hsq' a (fun k hk => h1 k (Or.inl hk))
  have := matCx_isStrictlyLE rank' dC' hsq' b (fun k hk => h1 k (Or.inr hk))
  have hge := dualCx_coneCx_isStrictlyGE f m (m - a) (fun k hk => hr k (Or.inr hk))
    (fun k hk => hL k (Or.inr hk))
  have hle := dualCx_coneCx_isStrictlyLE f m (m - b) (fun k hk => hr k (Or.inl hk))
    (fun k hk => hL k (Or.inl hk))
  rw [sub_sub_cancel] at hge hle
  exact homotopyEquiv_of_quasiIso_free a b (GHom.toCC Φ)

end Finite

/-! ### Non-vacuity -/

section NonVacuity

variable {X L : GCx A}

/-- **Non-vacuity of the cone model**: for the identity retract, the projection of the cone
model is the identity. Kind: PROVED. -/
theorem GRetract.refl_cone_p (f : GHom X L) (n : ℤ) (x : (coneCx f).X n) :
    ((GRetract.refl X).cone f).p.f n n rfl x = x := by
  obtain ⟨e, z⟩ := x
  change (e, z - f.f (n - 1) (n - 1) rfl 0) = (e, z)
  rw [map_zero, sub_zero]

/-- **Non-vacuity of the dual model**: for the identity retract, the inclusion and projection
of the dual model are the identity. Kind: PROVED. -/
theorem GRetract.refl_dual (m n : ℤ) (φ : (dualCx X m).X n) :
    ((GRetract.refl X).dual m).i.f n n rfl φ = φ ∧ ((GRetract.refl X).dual m).p.f n n rfl φ = φ :=
  ⟨rfl, rfl⟩

/-- **Non-vacuity of transport**: transporting the identity along identity retracts gives a
quasi-isomorphism. Kind: PROVED. -/
theorem GRetract.refl_transport_quasiIso (X : GCx A) :
    QuasiIso (GHom.toCC ((GRetract.refl X).transportMap (GRetract.refl X) (gHomId X))) :=
  (GRetract.refl X).quasiIso_transportMap _ _ (GRetract.refl X).quasiIso_i

end NonVacuity

end ZInQ.Manuscript.RC.Limits
