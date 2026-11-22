import ZInQKernel.Contrib.OneProof.WeilFormula
import ZInQKernel.Contrib.OneProof.MulEtale

/-! # weil-proof: lifts over endomorphisms, commutators, and the coherences for Mumford §23

Helper for `ZInQKernel/Contrib/OneProof/WeilFormula.lean`'s §23 part (docs/research/weil-proof.md):
lifts `t^*N → N` of a module `N` over endomorphisms `t`, their products (`prod`, associative), the
commutator relation `Comm` (multiplicative in the first variable; a lift commutes with its powers), the
coherence `theta_rho`, the tensor relation `tensor_relation`, and monoidal faithfulness. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace WeilProof.Theta

open Scheme.Modules PicDict.Transport

variable {X : Scheme.{0}} (N : X.Modules)

/-- The product of a lift `α` over `t` and a lift `β` over `s`: a lift over `t ≫ s`. -/
def prod {t s : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) : (Scheme.Modules.pullback (t ≫ s)).obj N ⟶ N :=
  (pullbackComp t s).inv.app N ≫ (Scheme.Modules.pullback t).map β ≫ α

/-- Moving a lift along an equality of morphisms. -/
def mv {t t' : X ⟶ X} (e : t = t') (α : (Scheme.Modules.pullback t).obj N ⟶ N) :
    (Scheme.Modules.pullback t').obj N ⟶ N :=
  eqToHom (by rw [e]) ≫ α

variable {N}

@[simp] lemma mv_rfl {t : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N) : mv N rfl α = α := by
  simp [mv]

lemma mv_mv {t t' t'' : X ⟶ X} (e : t = t') (e' : t' = t'') (α : (Scheme.Modules.pullback t).obj N ⟶ N) :
    mv N e' (mv N e α) = mv N (e.trans e') α := by
  subst e e'; simp

lemma mv_comp_smul {t t' : X ⟶ X} (e : t = t') (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (κ : Γ(X, ⊤)) : mv N e (α ≫ N.smulHom κ) = mv N e α ≫ N.smulHom κ := by
  simp [mv]

lemma prod_mv_left {t t' s : X ⟶ X} (e : t = t') (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) :
    prod N (mv N e α) β = mv N (by rw [e]) (prod N α β) := by
  subst e; simp

lemma prod_mv_right {t s s' : X ⟶ X} (e : s = s') (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) :
    prod N α (mv N e β) = mv N (by rw [e]) (prod N α β) := by
  subst e; simp

lemma prod_smul_left {t s : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (κ : Γ(X, ⊤)) :
    prod N (α ≫ N.smulHom κ) β = prod N α β ≫ N.smulHom κ := by
  simp [prod]

lemma prod_smul_right {t s : X ⟶ X} (ht : ∀ r : Γ(X, ⊤), t.appTop r = r)
    (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (κ : Γ(X, ⊤)) :
    prod N α (β ≫ N.smulHom κ) = prod N α β ≫ N.smulHom κ := by
  simp only [prod, Functor.map_comp, pullback_map_smulHom, ht, Category.assoc]
  rw [smulHom_naturality]

lemma assoc_inv (t s r : X ⟶ X) (M : X.Modules) :
    (pullbackComp (t ≫ s) r).inv.app M ≫ (pullbackComp t s).inv.app ((Scheme.Modules.pullback r).obj M) =
      eqToHom (by rw [Category.assoc]) ≫ (pullbackComp t (s ≫ r)).inv.app M ≫
        (Scheme.Modules.pullback t).map ((pullbackComp s r).inv.app M) := by
  have h := pullbackComp_assoc_app t s r M
  rw [← cancel_mono ((Scheme.Modules.pullback t).map ((pullbackComp s r).hom.app M) ≫
    (pullbackComp t (s ≫ r)).hom.app M)]
  simp only [Category.assoc]
  conv_lhs => rw [h]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]
  simp

/-- **Associativity** of the product of lifts. -/
lemma prod_assoc {t s r : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (γ : (Scheme.Modules.pullback r).obj N ⟶ N) :
    prod N (prod N α β) γ = mv N (Category.assoc t s r).symm (prod N α (prod N β γ)) := by
  have nat := (pullbackComp t s).inv.naturality γ
  simp only [Functor.comp_map] at nat
  have hA := pullbackComp_assoc_inv₁ t s r N
  simp only [prod, mv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat, reassoc_of% (assoc_inv t s r N)]

lemma prod_assoc' {t s r : X ⟶ X} (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (γ : (Scheme.Modules.pullback r).obj N ⟶ N) :
    prod N α (prod N β γ) = mv N (Category.assoc t s r) (prod N (prod N α β) γ) := by
  rw [prod_assoc, mv_mv, mv_rfl]

variable (N) in
/-- `α` (over `t`) and `β` (over `s`) commute up to the scalar `κ`. -/
def Comm {t s : X ⟶ X} (h : s ≫ t = t ≫ s) (α : (Scheme.Modules.pullback t).obj N ⟶ N)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) (κ : Γ(X, ⊤)) : Prop :=
  prod N α β = mv N h (prod N β α) ≫ N.smulHom κ

/-- **Multiplicativity of the commutator in the first variable.** -/
lemma comm_prod_left {t t' s : X ⟶ X} (ht : ∀ r : Γ(X, ⊤), t.appTop r = r)
    {h₁ : s ≫ t = t ≫ s} {h₂ : s ≫ t' = t' ≫ s} (h₃ : s ≫ (t ≫ t') = (t ≫ t') ≫ s)
    {α : (Scheme.Modules.pullback t).obj N ⟶ N} {α' : (Scheme.Modules.pullback t').obj N ⟶ N}
    {β : (Scheme.Modules.pullback s).obj N ⟶ N} {κ κ' : Γ(X, ⊤)}
    (c₁ : Comm N h₁ α β κ) (c₂ : Comm N h₂ α' β κ') : Comm N h₃ (prod N α α') β (κ' * κ) := by
  unfold Comm at *
  rw [prod_assoc, c₂, prod_smul_right ht, prod_mv_right, prod_assoc', mv_comp_smul, mv_mv, mv_mv, c₁,
    prod_smul_left, prod_mv_left, prod_assoc]
  simp only [mv_comp_smul, mv_mv, smulHom_mul, Category.assoc]

/-- `s^{j+1}` as an iterated composite. -/
def powM (s : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => s
  | j + 1 => powM s j ≫ s

variable (N) in
/-- The `(j+1)`-st power of a lift `β` over `s`, a lift over `powM s j`. -/
def pw {s : X ⟶ X} (β : (Scheme.Modules.pullback s).obj N ⟶ N) :
    (j : ℕ) → (Scheme.Modules.pullback (powM s j)).obj N ⟶ N
  | 0 => β
  | j + 1 => prod N (pw β j) β

lemma powM_comm (s : X ⟶ X) : ∀ j, s ≫ powM s j = powM s j ≫ s
  | 0 => rfl
  | j + 1 => by
    change s ≫ (powM s j ≫ s) = (powM s j ≫ s) ≫ s
    rw [← Category.assoc, powM_comm s j]

lemma powM_appTop {s : X ⟶ X} (hs : ∀ r : Γ(X, ⊤), s.appTop r = r) :
    ∀ j, ∀ r : Γ(X, ⊤), (powM s j).appTop r = r
  | 0 => hs
  | j + 1 => fun r => by
    change (powM s j ≫ s).appTop r = r
    rw [Scheme.Hom.comp_appTop]
    change (powM s j).appTop (s.appTop r) = r
    rw [hs, powM_appTop hs j]

/-- **A lift commutes with its powers.** -/
lemma comm_pw {s : X ⟶ X} (hs : ∀ r : Γ(X, ⊤), s.appTop r = r)
    (β : (Scheme.Modules.pullback s).obj N ⟶ N) :
    ∀ j, Comm N (powM_comm s j) (pw N β j) β 1
  | 0 => by
    change prod N β β = mv N rfl (prod N β β) ≫ N.smulHom 1
    simp
  | j + 1 => by
    have h := comm_prod_left (powM_appTop hs j) (powM_comm s (j + 1)) (comm_pw hs β j)
      (show Comm N rfl β β 1 by change prod N β β = mv N rfl (prod N β β) ≫ N.smulHom 1; simp)
    rw [mul_one] at h
    exact h

lemma comm_mv_left {t t' s : X ⟶ X} (e : t = t') {h : s ≫ t = t ≫ s} (h' : s ≫ t' = t' ≫ s)
    {α : (Scheme.Modules.pullback t).obj N ⟶ N} {β : (Scheme.Modules.pullback s).obj N ⟶ N}
    {κ : Γ(X, ⊤)} (c : Comm N h α β κ) : Comm N h' (mv N e α) β κ := by
  subst e
  simpa using c

lemma comm_smul_left {t s : X ⟶ X} (hs : ∀ r : Γ(X, ⊤), s.appTop r = r) {h : s ≫ t = t ≫ s}
    {α : (Scheme.Modules.pullback t).obj N ⟶ N} {β : (Scheme.Modules.pullback s).obj N ⟶ N}
    {κ : Γ(X, ⊤)} (u : Γ(X, ⊤)ˣ) (c : Comm N h (α ≫ N.smulHom u) β κ) : Comm N h α β κ := by
  unfold Comm at *
  rw [prod_smul_left, prod_smul_right hs, mv_comp_smul] at c
  have hiso : N.smulHom (u : Γ(X, ⊤)) ≫ N.smulHom ((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) = 𝟙 N := by
    rw [← smulHom_mul, Units.inv_mul, smulHom_one]
  have hiso' : N.smulHom ((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) ≫ N.smulHom (u : Γ(X, ⊤)) = 𝟙 N := by
    rw [← smulHom_mul, Units.mul_inv, smulHom_one]
  haveI : IsIso (N.smulHom (u : Γ(X, ⊤))) := ⟨⟨_, hiso, hiso'⟩⟩
  rw [← cancel_mono (N.smulHom (u : Γ(X, ⊤))), c, Category.assoc, Category.assoc, ← smulHom_mul,
    ← smulHom_mul, mul_comm]

/-- `θ_t(F) = pullbackComp ≫ pullbackCongr : t^* m^* F → m^* F` for `t ≫ m = m`. -/
def thetaT {t m : X ⟶ X} (h : t ≫ m = m) (F : X.Modules) :
    (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback m).obj F) ⟶ (Scheme.Modules.pullback m).obj F :=
  (pullbackComp t m).hom.app F ≫ (pullbackCongr h).hom.app F

/-! ### The coherence (C**) -/

lemma assoc_hom' (f g h : X ⟶ X) (M : X.Modules) :
    (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫ (pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫ (pullbackComp f (g ≫ h)).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  rw [reassoc_of% (pullbackComp_assoc_app f g h M)]
  simp

section Coherence

variable {a b m : X ⟶ X} (ha : a ≫ m = m) (hb : m ≫ a = b ≫ m) (hab : a ≫ b = b ≫ a)

/-- `ρ : m^*(a^* L) ≅ b^*(m^* L)` from `m ≫ a = b ≫ m`. -/
def rhoAB (L : X.Modules) : (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback a).obj L) ⟶
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback m).obj L) :=
  (pullbackComp m a).hom.app L ≫ (pullbackCongr hb).hom.app L ≫ (pullbackComp b m).inv.app L

/-- The swap `a^* b^* F ≅ b^* a^* F`. -/
def swapAB (F : X.Modules) : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj F) ⟶
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback a).obj F) :=
  (pullbackComp a b).hom.app F ≫ (pullbackCongr hab).hom.app F ≫ (pullbackComp b a).inv.app F

/-- **(C**)**: transporting `θ_a` along `ρ`. -/
lemma theta_rho (L : X.Modules) :
    thetaT ha ((Scheme.Modules.pullback a).obj L) ≫ rhoAB hb L =
      (Scheme.Modules.pullback a).map (rhoAB hb L) ≫ swapAB hab ((Scheme.Modules.pullback m).obj L) ≫
        (Scheme.Modules.pullback b).map (thetaT ha L) := by
  rw [← cancel_mono ((pullbackComp b m).hom.app L)]
  simp only [thetaT, rhoAB, swapAB, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    pullbackCongr_hom_app, Functor.map_comp]
  -- left side
  rw [reassoc_of% (eqToHom_comp_pullbackComp ha a L _), reassoc_of% (assoc_hom' a m a L)]
  -- right side
  rw [map_eqToHom_comp_pullbackComp b ha L _, reassoc_of% (pullbackComp_assoc_inv₂ b a m L),
    reassoc_of% (eqToHom_comp_pullbackComp hab m L _), reassoc_of% (assoc_hom' a b m L)]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback a) ((pullbackComp b m).inv.app L),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (map_eqToHom_comp_pullbackComp a hb L _)]
  simp

end Coherence

/-! ### The tensor relation (G5a) -/

section TensorRel

open MonoidalCategory

/-- **(G5a)** Tensoring a trivialization `ψ` of `m^*Φ` with `N = m^*L`. -/
lemma tensor_relation (hA : PullbackCompMonoidal) {t m : X ⟶ X} (h : t ≫ m = m)
    (hr : (pOU t).inv = Functor.LaxMonoidal.ε (Scheme.Modules.pullback t)) (Φ L : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj Φ) :
    (Scheme.Modules.pullback t).map ((λ_ ((Scheme.Modules.pullback m).obj L)).inv ≫
        (ψ.hom ▷ (Scheme.Modules.pullback m).obj L) ≫ Functor.LaxMonoidal.μ (Scheme.Modules.pullback m) Φ L) ≫
        thetaT h (Φ ⊗ L) =
      thetaT h L ≫ (λ_ ((Scheme.Modules.pullback m).obj L)).inv ≫
        ((alpha t m h Φ ψ ≫ ψ.hom) ▷ (Scheme.Modules.pullback m).obj L) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.pullback m) Φ L := by
  have h4 := hA t m Φ L
  have h5 := congr_mu h Φ L
  have hl := Functor.LaxMonoidal.left_unitality_inv (Scheme.Modules.pullback t)
    ((Scheme.Modules.pullback m).obj L)
  have hn : ((Scheme.Modules.pullback t).map ψ.hom ▷ (Scheme.Modules.pullback t).obj
        ((Scheme.Modules.pullback m).obj L)) ≫ Functor.LaxMonoidal.μ (Scheme.Modules.pullback t)
          ((Scheme.Modules.pullback m).obj Φ) ((Scheme.Modules.pullback m).obj L) =
      Functor.LaxMonoidal.μ (Scheme.Modules.pullback t) (𝟙_ X.Modules) ((Scheme.Modules.pullback m).obj L) ≫
        (Scheme.Modules.pullback t).map (ψ.hom ▷ (Scheme.Modules.pullback m).obj L) :=
    Functor.LaxMonoidal.μ_natural_left (Scheme.Modules.pullback t) ψ.hom ((Scheme.Modules.pullback m).obj L)
  simp only [thetaT, Functor.map_comp, Category.assoc]
  rw [← hl]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, reassoc_of% h4, h5]
  have hal : alpha t m h Φ ψ ≫ ψ.hom = Functor.LaxMonoidal.ε (Scheme.Modules.pullback t) ≫
      (Scheme.Modules.pullback t).map ψ.hom ≫ (pullbackComp t m).hom.app Φ ≫ (pullbackCongr h).hom.app Φ := by
    simp [alpha, ← hr]
  rw [hal]
  simp only [← MonoidalCategory.tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.assoc]
  rw [MonoidalCategory.tensorHom_def', Category.assoc, ← leftUnitor_inv_naturality_assoc]
  simp

end TensorRel

/-! ### Monoidal faithfulness (I5) -/

open MonoidalCategory

lemma unit_endo_eq_id_of_whisker {C : Type*} [Category C] [MonoidalCategory C] (A : 𝟙_ C ⟶ 𝟙_ C)
    {N N' : C} (j : N ⊗ N' ≅ 𝟙_ C) (hA : A ▷ N = 𝟙 (𝟙_ C ⊗ N)) : A = 𝟙 (𝟙_ C) := by
  have h1 : A ▷ (N ⊗ N') = 𝟙 (𝟙_ C ⊗ (N ⊗ N')) := by
    rw [MonoidalCategory.whiskerRight_tensor, hA]; simp
  have h2 : A ▷ 𝟙_ C = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
    have := MonoidalCategory.whisker_exchange A j.hom
    rw [h1, Category.id_comp] at this
    rw [← cancel_epi (𝟙_ C ◁ j.hom), this, Category.comp_id]
  have h3 := MonoidalCategory.rightUnitor_naturality A
  rw [h2, Category.id_comp] at h3
  rw [← cancel_epi (ρ_ (𝟙_ C)).hom, ← h3, Category.comp_id]

end WeilProof.Theta

/-! ## The §23 leaf from divisibility -/

namespace WeilProof.Theta

open PicDict PkgI3 PkgI3.AbVar MonoidalCategory Scheme.Modules PicDict.Transport
open scoped CategoryTheory.MonObj

/-- **Divisibility of `X(k)`** for `n` invertible in `k` (Mumford §4, Application 2: `n_X` is surjective;
UNVERIFIED numbering). -/
def DivisibleAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (n : ℕ), 0 < n → (n : k) ≠ 0 →
    ∀ x : AC.Kpt X, ∃ y : AC.Kpt X, y ^ n = x

variable {k : Type} [Field k]

lemma tr_mul_comm (X : AbVar k) (y : AC.Kpt X) (n : ℕ) :
    AC.tr y ≫ AC.mul X n = AC.mul X n ≫ AC.tr (y ^ n) := by
  simp only [AC.tr, AC.mul, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, MonObj.comp_mul,
    Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (_ ≫ CartesianMonoidalCategory.toUnit X.X)
      (CartesianMonoidalCategory.toUnit X.X)]

lemma powM_tr (X : AbVar k) (y : AC.Kpt X) : ∀ j, powM (AC.tr y).left j = (AC.tr (y ^ (j + 1))).left
  | 0 => by
    change (AC.tr y).left = (AC.tr (y ^ (0 + 1))).left
    rw [zero_add, pow_one]
  | j + 1 => by
    change powM (AC.tr y).left j ≫ (AC.tr y).left = _
    rw [powM_tr X y j, ← Over.comp_left, AC.tr_comp_tr, ← pow_succ]

end WeilProof.Theta

namespace WeilProof.Theta

open PicDict PkgI3 PkgI3.AbVar MonoidalCategory Scheme.Modules PicDict.Transport
open scoped CategoryTheory.MonObj


lemma isIso_pw {X : Scheme.{0}} {N : X.Modules} {s : X ⟶ X} (b : (Scheme.Modules.pullback s).obj N ⟶ N) [IsIso b] :
    ∀ j, IsIso (pw N b j)
  | 0 => by change IsIso b; infer_instance
  | j + 1 => by
    have := isIso_pw b j
    change IsIso (prod N (pw N b j) b)
    simp only [prod]
    infer_instance

/-- **The core of Mumford §23** on a scheme `X`: `t = s^n` (as lifts' base), `t ≫ m = m`,
`m ≫ t = s ≫ m`, translations fixing `Γ(X, 𝒪)`, `L` with `m^*L` invertible, `Φ ⊗ L ≅ t^*L`. -/
theorem alt_core {X : Scheme.{0}} {m t s : X ⟶ X} (h : t ≫ m = m) (hb : m ≫ t = s ≫ m)
    (hab : t ≫ s = s ≫ t) (hs : ∀ r : Γ(X, ⊤), s.appTop r = r)
    (hr : (pOU t).inv = Functor.LaxMonoidal.ε (Scheme.Modules.pullback t)) (j₀ : ℕ) (hpow : powM s j₀ = t)
    (L Φ : X.Modules) [((Scheme.Modules.pullback m).obj L).IsInvertible] {N' : X.Modules}
    (jN : (Scheme.Modules.pullback m).obj L ⊗ N' ≅ 𝟙_ X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj Φ) (w : Φ ⊗ L ≅ (Scheme.Modules.pullback t).obj L) :
    val (alpha t m h Φ ψ) = 1 := by
  let u : (Scheme.Modules.pullback m).obj L ⟶ (Scheme.Modules.pullback m).obj (Φ ⊗ L) :=
    (λ_ ((Scheme.Modules.pullback m).obj L)).inv ≫ (ψ.hom ▷ (Scheme.Modules.pullback m).obj L) ≫ Functor.LaxMonoidal.μ (Scheme.Modules.pullback m) Φ L
  let β : (Scheme.Modules.pullback m).obj L ⟶ (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback m).obj L) := u ≫ (Scheme.Modules.pullback m).map w.hom ≫ rhoAB hb L
  let EA : (Scheme.Modules.pullback m).obj L ⟶ (Scheme.Modules.pullback m).obj L :=
    (λ_ ((Scheme.Modules.pullback m).obj L)).inv ≫ (alpha t m h Φ ψ ▷ (Scheme.Modules.pullback m).obj L) ≫ (λ_ ((Scheme.Modules.pullback m).obj L)).hom
  have R : (Scheme.Modules.pullback t).map β ≫ swapAB hab ((Scheme.Modules.pullback m).obj L) ≫ (Scheme.Modules.pullback s).map (thetaT h L) =
      thetaT h L ≫ EA ≫ β := by
    have trel := tensor_relation pullbackCompMonoidal_proof h hr Φ L ψ
    have nat : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback m).map w.hom) ≫ thetaT h ((Scheme.Modules.pullback t).obj L) =
        thetaT h (Φ ⊗ L) ≫ (Scheme.Modules.pullback m).map w.hom := by
      have n1 := (pullbackComp t m).hom.naturality w.hom
      have n2 := (pullbackCongr h).hom.naturality w.hom
      simp only [Functor.comp_map] at n1 n2
      simp only [thetaT, ← Category.assoc, n1]
      simp only [Category.assoc, n2]
    have tro := theta_rho h hb hab L
    simp only [β, u, EA, Functor.map_comp, Category.assoc]
    rw [← tro, reassoc_of% nat]
    simp only [Functor.map_comp, Category.assoc] at trel
    rw [reassoc_of% trel]
    simp [MonoidalCategory.comp_whiskerRight]
  -- β is an isomorphism
  have : IsIso β := by
    simp only [β, u, rhoAB]
    infer_instance
  have hθ : IsIso (thetaT h L) := by
    simp only [thetaT]
    infer_instance
  set b := inv β with hbdef
  -- (C1): the commutator of `θ` and `b` is `EA⁻¹`
  have C1 : prod ((Scheme.Modules.pullback m).obj L) (thetaT h L) b ≫ EA =
      mv ((Scheme.Modules.pullback m).obj L) hab.symm (prod ((Scheme.Modules.pullback m).obj L) b (thetaT h L)) := by
    have R' : swapAB hab ((Scheme.Modules.pullback m).obj L) ≫ (Scheme.Modules.pullback s).map (thetaT h L) ≫ b =
        (Scheme.Modules.pullback t).map b ≫ thetaT h L ≫ EA := by
      rw [← cancel_epi ((Scheme.Modules.pullback t).map β), reassoc_of% R, hbdef, IsIso.hom_inv_id, Category.comp_id,
        ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [prod, mv, Category.assoc]
    rw [← R']
    simp only [swapAB, pullbackCongr_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  -- (C2): the theta argument
  have cp := comm_pw hs b j₀
  have cm := comm_mv_left hpow hab.symm cp
  have hpwi : IsIso (pw ((Scheme.Modules.pullback m).obj L) b j₀) := isIso_pw b j₀
  have hmvi : IsIso (mv ((Scheme.Modules.pullback m).obj L) hpow (pw ((Scheme.Modules.pullback m).obj L) b j₀)) := by
    simp only [mv]; infer_instance
  obtain ⟨lam, hlam⟩ := exists_eq_smulHom ((Scheme.Modules.pullback m).obj L)
    (inv (thetaT h L) ≫ mv ((Scheme.Modules.pullback m).obj L) hpow (pw ((Scheme.Modules.pullback m).obj L) b j₀))
  have hmv : mv ((Scheme.Modules.pullback m).obj L) hpow (pw ((Scheme.Modules.pullback m).obj L) b j₀) =
      thetaT h L ≫ ((Scheme.Modules.pullback m).obj L).smulHom lam := by
    rw [← hlam, IsIso.hom_inv_id_assoc]
  obtain ⟨mu, hmu⟩ := exists_eq_smulHom ((Scheme.Modules.pullback m).obj L)
    (inv (inv (thetaT h L) ≫ mv ((Scheme.Modules.pullback m).obj L) hpow (pw ((Scheme.Modules.pullback m).obj L) b j₀)))
  have hunit : mu * lam = 1 := by
    apply eq_of_smulHom_eq ((Scheme.Modules.pullback m).obj L)
    rw [smulHom_mul, ← hlam, ← hmu, IsIso.hom_inv_id, smulHom_one]
  rw [hmv] at cm
  have C2 := comm_smul_left hs ⟨lam, mu, by rw [mul_comm, hunit], hunit⟩ cm
  -- combine
  have hEA : EA = 𝟙 _ := by
    unfold Comm at C2
    rw [smulHom_one, Category.comp_id] at C2
    have hpi : IsIso (prod ((Scheme.Modules.pullback m).obj L) (thetaT h L) b) := by simp only [prod]; infer_instance
    rw [← cancel_epi (prod ((Scheme.Modules.pullback m).obj L) (thetaT h L) b), C1, ← C2, Category.comp_id]
  have hAN : alpha t m h Φ ψ ▷ (Scheme.Modules.pullback m).obj L = 𝟙 _ := by
    have := congrArg (fun φ => (λ_ ((Scheme.Modules.pullback m).obj L)).hom ≫ φ ≫ (λ_ ((Scheme.Modules.pullback m).obj L)).inv) hEA
    simp only [EA, Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.id_comp] at this
    exact (Category.comp_id _).symm.trans this
  have hA : alpha t m h Φ ψ = 𝟙 _ := unit_endo_eq_id_of_whisker (C := X.Modules) _ jN hAN
  rw [hA]
  rfl

variable {k : Type} [Field k]

/-- **Mumford §23 (`e_n(x, φ_L(x)) = 1`) from divisibility.** -/
theorem mumfordWeilAltAC_of_div (hdiv : DivisibleAC) : MumfordWeilAltAC := by
  intro k _ _ X n hn hnk c₀ x hx ψ
  obtain ⟨y, rfl⟩ := hdiv k X n hn hnk x
  have h : (AC.tr (y ^ n)).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
    rw [← Over.comp_left, AC.tr_comp_mul _ hx]
  have hb : (AC.mul X n).left ≫ (AC.tr (y ^ n)).left = (AC.tr y).left ≫ (AC.mul X n).left := by
    rw [← Over.comp_left, ← Over.comp_left, tr_mul_comm]
  have hab : (AC.tr (y ^ n)).left ≫ (AC.tr y).left = (AC.tr y).left ≫ (AC.tr (y ^ n)).left := by
    rw [← Over.comp_left, ← Over.comp_left, AC.tr_comp_tr, AC.tr_comp_tr, mul_comm]
  have hr : (pOU (AC.tr (y ^ n)).left).inv = Functor.LaxMonoidal.ε (Scheme.Modules.pullback (AC.tr (y ^ n)).left) := by
    have h1 := unitRatio_tr pullbackCompMonoidal_proof X (y ^ n) hx
    have h2 : unitRatio (AC.tr (y ^ n)).left = 𝟙 _ :=
      (unitHomAddEquiv (unit X.X.left)).injective (h1.trans id_val.symm)
    have h3 := congrArg (· ≫ Functor.LaxMonoidal.ε (Scheme.Modules.pullback (AC.tr (y ^ n)).left)) h2
    simp only [unitRatio, Category.assoc, Category.id_comp] at h3
    rw [← Functor.Monoidal.εIso_hom, Iso.inv_hom_id] at h3
    exact (Category.comp_id _).symm.trans h3
  have hpow : powM (AC.tr y).left (n - 1) = (AC.tr (y ^ n)).left := by
    rw [powM_tr, Nat.sub_add_cancel hn]
  have hcl : AC.phi c₀ (y ^ n) * c₀ = Scheme.Pic.map (AC.tr (y ^ n)).left c₀ := by
    simp only [AC.phi, inv_mul_cancel_right]
  let w : AC.modX (AC.phi c₀ (y ^ n)) ⊗ AC.modX c₀ ≅ (Scheme.Modules.pullback (AC.tr (y ^ n)).left).obj (AC.modX c₀) :=
    (Scheme.Pic.mulIso _ _).symm ≪≫ eqToIso (congrArg (fun c : X.X.left.Pic => (fromSkeleton X.X.left.Modules).obj c.val) hcl) ≪≫
      Scheme.Pic.mkIso _
  let jN : (Scheme.Modules.pullback (AC.mul X n).left).obj (AC.modX c₀) ⊗
      (fromSkeleton X.X.left.Modules).obj ((Scheme.Pic.map (AC.mul X n).left c₀)⁻¹).val ≅ 𝟙_ X.X.left.Modules :=
    ((Scheme.Pic.mkIso _).symm ⊗ᵢ Iso.refl _) ≪≫ (Scheme.Pic.mulIso _ _).symm ≪≫
      eqToIso (congrArg (fun c : X.X.left.Pic => (fromSkeleton X.X.left.Modules).obj c.val) (mul_inv_cancel _)) ≪≫ Scheme.Pic.oneIso
  unfold AC.formula
  rw [wf_eq_alpha]
  exact alt_core h hb hab (tr_appTop X y) hr (n - 1) hpow (AC.modX c₀) (AC.modX (AC.phi c₀ (y ^ n))) jN ψ w

/-- **The field `weilPairingMumford` with Mumford §23 proved**: from four of pic-dict's Mumford leaves
(§6 Cor. 4, §8 (iv), §8 Thm 1, §20 nondegeneracy), divisibility of `X(k)` (Mumford §4, Application 2) and the
open field `phiAmpleIsogeny`. -/
theorem weilPairingMumford_of_div (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20b : MumfordWeilNondegAC) (hdiv : DivisibleAC)
    (h3 : T09Pic.PhiAmpleIsogeny) : T09Pic.WeilPairingMumford :=
  weilPairingMumford_proof hsq h8iv h8 h20b (mumfordWeilAltAC_of_div hdiv) h3

open Limits

/-- Geometrically integral implies geometrically connected (copy of
`FrobPiecesNeron.geometricallyConnected_of_geometricallyIntegral`). -/
theorem geomConn_of_geomInt {X Y : Scheme.{0}} (g : X ⟶ Y) [GeometricallyIntegral g] :
    GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

/-- **Divisibility of `X(k)`** for `n` invertible in `k` (proved: `[n]` is étale (the tree's
`mulEtaleAbelianScheme_proof`), hence open; proper, hence closed; `X` is connected; so `[n]` is surjective,
and the fibre over a `k`-point has a `k`-point). -/
theorem divisibleAC : DivisibleAC := by
  intro k _ _ X n hn hnk x
  have : GeometricallyConnected X.X.hom := geomConn_of_geomInt X.X.hom
  have : PkgI2.IsAbelianScheme (ObjBridge.toGrp X) := ⟨X.proper, X.smooth, inferInstance⟩
  have hE : Etale ((𝟙 (ObjBridge.toGrp X).X ^ n : (ObjBridge.toGrp X).X ⟶ (ObjBridge.toGrp X).X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof k (ObjBridge.toGrp X) n
      (by exact (IsUnit.mk0 _ hnk))
  have hE' : Etale (AC.mul X n).left := hE
  set f := (AC.mul X n).left with hfdef
  have hopen : IsOpenMap f := isOpenMap_of_generalizingMap f (Flat.generalizingMap f)
  have hw : f ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  have : IsProper (f ≫ X.X.hom) := by rw [hw]; infer_instance
  have : IsProper f := IsProper.of_comp f X.X.hom
  have hclosed : IsClosedMap f := f.isClosedMap
  have : IsIntegral X.X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.X.hom
  have hrange : Set.range f = Set.univ := by
    have hne : (Set.range f).Nonempty := by
      obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
      exact ⟨_, ⟨η[X.X].left p, rfl⟩⟩
    exact (IsClopen.eq_univ ⟨hclosed.isClosed_range, hopen.isOpen_range⟩ hne)
  have : Surjective f := ⟨fun y => by
    have : y ∈ Set.range f := by rw [hrange]; trivial
    exact this⟩
  let zl : Spec (CommRingCat.of k) ⟶ X.X.left := x.left
  let s : pullback f zl ⟶ Spec (CommRingCat.of k) := pullback.snd f zl
  have : IsProper s := by dsimp [s]; infer_instance
  have : Surjective s := by dsimp [s]; infer_instance
  have : CompactSpace ((pullback f zl : Scheme) : Type) := QuasiCompact.compactSpace_of_compactSpace s
  have : Nonempty ((pullback f zl : Scheme) : Type) := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    exact ⟨(s.surjective p).choose⟩
  obtain ⟨x0, -, hx0⟩ := IsClosed.exists_closed_singleton (X := ((pullback f zl : Scheme) : Type))
    isClosed_univ Set.univ_nonempty
  let pt := pointOfClosedPoint s x0 hx0
  have hpt : pt ≫ s = 𝟙 _ := pointOfClosedPoint_comp s x0 hx0
  have hz : zl ≫ X.X.hom = 𝟙 _ := Over.w x
  let yy : AC.Kpt X := Over.homMk (pt ≫ pullback.fst f zl) (by
    change (pt ≫ pullback.fst f zl) ≫ X.X.hom = 𝟙 _
    rw [Category.assoc, ← hw, pullback.condition_assoc, hz, Category.comp_id]
    exact hpt)
  refine ⟨yy, ?_⟩
  have hyx : yy ≫ AC.mul X n = x := by
    apply Over.OverMorphism.ext
    change (pt ≫ pullback.fst f zl) ≫ f = zl
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (pt ≫ s) ≫ _ = _
    rw [hpt, Category.id_comp]
  rw [← hyx]
  simp only [AC.mul, MonObj.comp_pow, Category.comp_id]


/-- **Mumford §23 is a theorem**: `e_n(x, φ_L(x)) = 1` for the formula `ē_n`. -/
theorem mumfordWeilAltAC_proof : MumfordWeilAltAC := mumfordWeilAltAC_of_div divisibleAC

/-- **The field `weilPairingMumford`** from four of pic-dict's Mumford leaves (§6 Cor. 4, §8 (iv), §8 Thm 1,
§20 nondegeneracy) and the open field `phiAmpleIsogeny`; Mumford's §20 (definition, bilinear) and §23
displays are proved (`mumfordWeilPairingAC_proof`, `mumfordWeilAltAC_proof`). -/
theorem weilPairingMumford_final (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20b : MumfordWeilNondegAC) (h3 : T09Pic.PhiAmpleIsogeny) :
    T09Pic.WeilPairingMumford :=
  weilPairingMumford_of_div hsq h8iv h8 h20b divisibleAC h3

end WeilProof.Theta
