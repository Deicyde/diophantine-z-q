import ZInQKernel.Contrib.OneProof.WeilFormula

/-! weil-proof, §23 attempt, part 1: lifts over endomorphisms and their commutators (generic). -/

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

/-! ### The coherence (C**) -/

lemma assoc_hom' (f g h : X ⟶ X) (M : X.Modules) :
    (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫ (pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫ (pullbackComp f (g ≫ h)).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  rw [reassoc_of% (pullbackComp_assoc_app f g h M)]
  simp

section Coherence

variable {a b m : X ⟶ X} (ha : a ≫ m = m) (hb : m ≫ a = b ≫ m) (hab : a ≫ b = b ≫ a)

/-- `θ_a(F) : a^* m^* F → m^* F`. -/
def thetaA (F : X.Modules) : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback m).obj F) ⟶
    (Scheme.Modules.pullback m).obj F :=
  (pullbackComp a m).hom.app F ≫ (pullbackCongr ha).hom.app F

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
    thetaA ha ((Scheme.Modules.pullback a).obj L) ≫ rhoAB hb L =
      (Scheme.Modules.pullback a).map (rhoAB hb L) ≫ swapAB hab ((Scheme.Modules.pullback m).obj L) ≫
        (Scheme.Modules.pullback b).map (thetaA ha L) := by
  rw [← cancel_mono ((pullbackComp b m).hom.app L)]
  simp only [thetaA, rhoAB, swapAB, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
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

/-- `θ_t(F) = pullbackComp ≫ pullbackCongr : t^* m^* F → m^* F` for `t ≫ m = m`. -/
def thetaT {t m : X ⟶ X} (h : t ≫ m = m) (F : X.Modules) :
    (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback m).obj F) ⟶ (Scheme.Modules.pullback m).obj F :=
  (pullbackComp t m).hom.app F ≫ (pullbackCongr h).hom.app F

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
