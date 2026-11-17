import ZInQKernel.Contrib.OneProof.PicDictionary

/-! weil-proof, step 1: generic lemmas on the Weil formula `wf t m h M ψ` (any scheme). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace WeilProof

open Scheme.Modules PicDict.Transport

universe u

variable {X : Scheme.{u}}

/-- The value at `1` of an endomorphism of `𝒪_X`, in `Γ(X, ⊤)`. -/
def val (g : unit X ⟶ unit X) : Γ(X, ⊤) := g.app ⊤ (1 : Γ(X, ⊤))

/-- An endomorphism of `𝒪_X` is multiplication by its value at `1`. -/
lemma endo_app_top (g : unit X ⟶ unit X) (r : Γ(X, ⊤)) :
    (show Γ(X, ⊤) from g.app ⊤ r) = r * val g := by
  have h := Hom.app_smul g r (1 : Γ(X, ⊤))
  simp only [smul_eq_mul, mul_one] at h
  exact h

/-- Composition of endomorphisms of `𝒪_X` is multiplication of values. -/
lemma comp_val (f g : unit X ⟶ unit X) : val (f ≫ g) = val f * val g := by
  unfold val
  rw [Hom.comp_app]
  exact endo_app_top g _

lemma id_val : val (𝟙 (unit X)) = 1 := rfl

/-- The automorphism of `𝒪_X` whose value is the Weil formula. -/
def alpha (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : unit X ⟶ unit X :=
  (pOU t).inv ≫ (Scheme.Modules.pullback t).map ψ.hom ≫ (pullbackComp t m).hom.app M ≫
    (pullbackCongr h).hom.app M ≫ ψ.inv

/-- Its inverse. -/
def alphaInv (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : unit X ⟶ unit X :=
  ψ.hom ≫ (pullbackCongr h).inv.app M ≫ (pullbackComp t m).inv.app M ≫
    (Scheme.Modules.pullback t).map ψ.inv ≫ (pOU t).hom

lemma wf_eq_alpha (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t m h M ψ = val (alpha t m h M ψ) := rfl

lemma alpha_alphaInv (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    alpha t m h M ψ ≫ alphaInv t m h M ψ = 𝟙 _ := by
  simp only [alpha, alphaInv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id]

/-- The Weil formula is a unit of `Γ(X, 𝒪)`. -/
lemma wf_isUnit (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : IsUnit (wf t m h M ψ) := by
  refine IsUnit.of_mul_eq_one (val (alphaInv t m h M ψ)) ?_
  rw [wf_eq_alpha, ← comp_val, alpha_alphaInv]
  rfl

lemma wf_congr_t {t t' m : X ⟶ X} (e : t = t') (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : wf t m h M ψ = wf t' m h' M ψ := by
  subst e; rfl

/-- The comparison `θ_t : t^* m^* M ≅ m^* M` for `t ≫ m = m` is a cocycle. -/
lemma theta_comp (t₁ t₂ m : X ⟶ X) (h₁ : t₁ ≫ m = m) (h₂ : t₂ ≫ m = m) (h₁₂ : (t₁ ≫ t₂) ≫ m = m)
    (M : X.Modules) :
    (pullbackComp t₁ t₂).hom.app ((Scheme.Modules.pullback m).obj M) ≫
        (pullbackComp (t₁ ≫ t₂) m).hom.app M ≫ (pullbackCongr h₁₂).hom.app M =
      (Scheme.Modules.pullback t₁).map ((pullbackComp t₂ m).hom.app M ≫ (pullbackCongr h₂).hom.app M) ≫
        (pullbackComp t₁ m).hom.app M ≫ (pullbackCongr h₁).hom.app M := by
  simp only [pullbackCongr_hom_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (map_eqToHom_comp_pullbackComp t₁ h₂ M)]
  rw [reassoc_of% (pullbackComp_assoc_app t₁ t₂ m M)]
  simp

/-- **Cocycle relation for `α`**: `α_{t₁ t₂} = t₁^♯(α_{t₂}) ∘ α_{t₁}`. -/
lemma alpha_comp (t₁ t₂ m : X ⟶ X) (h₁ : t₁ ≫ m = m) (h₂ : t₂ ≫ m = m) (h₁₂ : (t₁ ≫ t₂) ≫ m = m)
    (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    alpha (t₁ ≫ t₂) m h₁₂ M ψ =
      ((pOU t₁).inv ≫ (Scheme.Modules.pullback t₁).map (alpha t₂ m h₂ M ψ) ≫ (pOU t₁).hom) ≫
        alpha t₁ m h₁ M ψ := by
  have nat := (pullbackComp t₁ t₂).hom.naturality ψ.hom
  simp only [Functor.comp_map] at nat
  have hθ := theta_comp t₁ t₂ m h₁ h₂ h₁₂ M
  simp only [alpha, pOU_inv_comp t₁ t₂, Category.assoc]
  rw [← reassoc_of% nat, reassoc_of% hθ]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback t₁) ψ.inv ψ.hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Cocycle relation for the Weil formula**: `wf_{t₁ t₂} = t₁^*(wf_{t₂}) · wf_{t₁}`. -/
theorem wf_comp (t₁ t₂ m : X ⟶ X) (h₁ : t₁ ≫ m = m) (h₂ : t₂ ≫ m = m) (h₁₂ : (t₁ ≫ t₂) ≫ m = m)
    (M : X.Modules) (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf (t₁ ≫ t₂) m h₁₂ M ψ = t₁.appTop (wf t₂ m h₂ M ψ) * wf t₁ m h₁ M ψ := by
  rw [wf_eq_alpha, alpha_comp t₁ t₂ m h₁ h₂ h₁₂ M ψ, comp_val]
  exact congrArg (· * _) (pOU_conj t₁ (alpha t₂ m h₂ M ψ))

/-- `wf_𝟙 = 1`. -/
theorem wf_id (m : X ⟶ X) (h : 𝟙 X ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : wf (𝟙 X) m h M ψ = 1 := by
  have h2 : (𝟙 X ≫ 𝟙 X) ≫ m = m := by simp
  have e := wf_comp (𝟙 X) (𝟙 X) m h h h2 M ψ
  rw [wf_congr_t (Category.id_comp (𝟙 X)) h2 h] at e
  have e' : wf (𝟙 X) m h M ψ * 1 = wf (𝟙 X) m h M ψ * wf (𝟙 X) m h M ψ := by
    rw [mul_one]; exact e.trans (by simp)
  exact ((wf_isUnit _ _ h M ψ).mul_left_cancel e').symm

/-- **Change of trivialization**: if the ratio `a = ψ' ψ⁻¹` has a `t`-invariant value, the Weil
formula does not change. -/
theorem wf_change (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ ψ' : unit X ≅ (Scheme.Modules.pullback m).obj M)
    (ha : t.appTop (val (ψ'.hom ≫ ψ.inv)) = val (ψ'.hom ≫ ψ.inv)) :
    wf t m h M ψ' = wf t m h M ψ := by
  have key : alpha t m h M ψ' =
      ((pOU t).inv ≫ (Scheme.Modules.pullback t).map (ψ'.hom ≫ ψ.inv) ≫ (pOU t).hom) ≫
        alpha t m h M ψ ≫ (ψ.hom ≫ ψ'.inv) := by
    simp only [alpha, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc (Scheme.Modules.pullback t) ψ.inv ψ.hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hab : val (ψ'.hom ≫ ψ.inv) * val (ψ.hom ≫ ψ'.inv) = 1 := by
    rw [← comp_val]; simp [id_val]
  have hc : val ((pOU t).inv ≫ (Scheme.Modules.pullback t).map (ψ'.hom ≫ ψ.inv) ≫ (pOU t).hom) =
      val (ψ'.hom ≫ ψ.inv) := (pOU_conj t _).trans ha
  rw [wf_eq_alpha, key, comp_val, comp_val, hc, wf_eq_alpha]
  calc _ = val (alpha t m h M ψ) * (val (ψ'.hom ≫ ψ.inv) * val (ψ.hom ≫ ψ'.inv)) := by ring
    _ = _ := by rw [hab, mul_one]

end WeilProof

/-! ## Step 2: over an algebraically closed field, parts (i)-(iii) of `MumfordWeilPairingAC` -/

namespace WeilProof

open PicDict PkgI3 PkgI3.AbVar Scheme.Modules PicDict.Transport MonoidalCategory
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k]

/-- Constants `k → Γ(X, 𝒪)` as a ring homomorphism. -/
def constHom (X : AbVar k) : k →+* Γ(X.X.left, ⊤) :=
  X.X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

lemma const_eq (X : AbVar k) (u : k) : AC.const X u = constHom X u := rfl

lemma constHom_bijective (X : AbVar k) : Function.Bijective (constHom X) :=
  (bijective_appTop_of_isProper_of_geometricallyIntegral X.X.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.bijective

/-- Translations act trivially on `Γ(X, 𝒪)` (every global function is constant). -/
lemma tr_appTop (X : AbVar k) (y : AC.Kpt X) (r : Γ(X.X.left, ⊤)) :
    (AC.tr y).left.appTop r = r := by
  obtain ⟨u, rfl⟩ := (constHom_bijective X).2 r
  change ((AC.tr y).left ≫ X.X.hom).appTop.hom _ = _
  rw [Over.w (AC.tr y)]
  rfl

lemma tr_one (X : AbVar k) : AC.tr (1 : AC.Kpt X) = 𝟙 X.X := by
  simp only [AC.tr, ← CategoryTheory.Hom.mul_def]
  rw [MonObj.comp_one, mul_one]


/-- (i) independence of the trivialization. -/
theorem formula_indep (X : AbVar k) {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1) (c : X.X.left.Pic)
    (ψ ψ' : AC.Triv X n c) : AC.formula x hx c ψ = AC.formula x hx c ψ' := by
  have ha := tr_appTop X x (val (ψ.hom ≫ ψ'.inv))
  exact wf_change (AC.tr x).left (AC.mul X n).left _ (AC.modX c) ψ' ψ ha

lemma formula_congr_x (X : AbVar k) {n : ℕ} {y y' : AC.Kpt X} (e : y = y') (hy : y ^ n = 1)
    (hy' : y' ^ n = 1) (c : X.X.left.Pic) (ψ : AC.Triv X n c) :
    AC.formula y hy c ψ = AC.formula y' hy' c ψ := by
  subst e; rfl

lemma formula_one (X : AbVar k) {n : ℕ} (h1 : (1 : AC.Kpt X) ^ n = 1) (c : X.X.left.Pic)
    (ψ : AC.Triv X n c) : AC.formula 1 h1 c ψ = 1 := by
  unfold AC.formula
  have e : (AC.tr (1 : AC.Kpt X)).left = 𝟙 _ := by rw [tr_one]; rfl
  rw [wf_congr_t e _ (by simp), wf_id]

/-- (iii) multiplicativity in `x`. -/
theorem formula_mul (X : AbVar k) {n : ℕ} (x x' : AC.Kpt X) (hx : x ^ n = 1) (hx' : x' ^ n = 1)
    (c : X.X.left.Pic) (ψ : AC.Triv X n c) :
    AC.formula (x * x') (by rw [mul_pow, hx, hx', mul_one]) c ψ =
      AC.formula x hx c ψ * AC.formula x' hx' c ψ := by
  have e : (AC.tr x).left ≫ (AC.tr x').left = (AC.tr (x * x')).left := by
    rw [← Over.comp_left, AC.tr_comp_tr]
  have h₁ : (AC.tr x).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
    rw [← Over.comp_left, AC.tr_comp_mul x hx]
  have h₂ : (AC.tr x').left ≫ (AC.mul X n).left = (AC.mul X n).left := by
    rw [← Over.comp_left, AC.tr_comp_mul x' hx']
  have h₁₂ : ((AC.tr x).left ≫ (AC.tr x').left) ≫ (AC.mul X n).left = (AC.mul X n).left := by
    rw [Category.assoc, h₂, h₁]
  unfold AC.formula
  rw [← wf_congr_t e h₁₂, wf_comp _ _ _ h₁ h₂ h₁₂, tr_appTop, mul_comm]

/-- Powers: `ē(x^j) = ē(x)^j`. -/
theorem formula_pow (X : AbVar k) {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1) (c : X.X.left.Pic)
    (ψ : AC.Triv X n c) (j : ℕ) :
    AC.formula (x ^ j) (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) c ψ =
      AC.formula x hx c ψ ^ j := by
  have hp : ∀ i : ℕ, (x ^ i) ^ n = 1 := fun i => by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
  induction j with
  | zero =>
    rw [formula_congr_x X (pow_zero x) _ (one_pow n), formula_one, pow_zero]
  | succ j ih =>
    have := formula_mul X (x ^ j) x (hp j) hx c ψ
    rw [formula_congr_x X (pow_succ x j) _ (by rw [← pow_succ]; exact hp (j + 1)), this, ih, pow_succ]

/-- (ii) the value is a constant `n`-th root of unity. -/
theorem formula_root (X : AbVar k) {n : ℕ} (hn : 0 < n) (x : AC.Kpt X) (hx : x ^ n = 1)
    (c : X.X.left.Pic) (ψ : AC.Triv X n c) :
    ∃ u : kˣ, u ^ n = 1 ∧ AC.const X (u : k) = AC.formula x hx c ψ := by
  obtain ⟨v, hv⟩ := (constHom_bijective X).2 (AC.formula x hx c ψ)
  have h1 : AC.formula x hx c ψ ^ n = 1 := by
    rw [← formula_pow X x hx c ψ n, formula_congr_x X hx _ (one_pow n), formula_one]
  have hvn : v ^ n = 1 := by
    apply (constHom_bijective X).1
    rw [map_pow, hv, h1, map_one]
  refine ⟨Units.ofPowEqOne v n hvn hn.ne', ?_, ?_⟩
  · ext; simp
  · rw [const_eq]; simpa using hv

end WeilProof

/-! ## Step 3: `MumfordWeilPairingAC` from its fourth part, and the field -/

namespace WeilProof

open PicDict PkgI3 PkgI3.AbVar MonoidalCategory
open scoped CategoryTheory.MonObj

/-- **LEAF (`ē_n` is multiplicative in the class).** Mumford, *Abelian varieties*, §20 (bilinearity of
`ē_n : X_n × X̂_n → μ_n`, here its second variable), for the formula `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹`, `n`
prime to the characteristic, `k` algebraically closed (UNVERIFIED numbering). This is the fourth
conjunct of `PicDict.MumfordWeilPairingAC`; the other three are proved here
(`formula_indep`, `formula_root`, `formula_mul`). -/
def MumfordWeilBilinRightAC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : AbVar k) (n : ℕ), 0 < n → (n : k) ≠ 0 →
    ∀ (x : AC.Kpt X) (hx : x ^ n = 1) (c c' : X.X.left.Pic), AC.IsDT n c → AC.IsDT n c' →
      ∀ (ψ : AC.Triv X n c) (ψ' : AC.Triv X n c') (ψ'' : AC.Triv X n (c * c')),
        AC.formula x hx (c * c') ψ'' = AC.formula x hx c ψ * AC.formula x hx c' ψ'

/-- **`MumfordWeilPairingAC` from its fourth conjunct**: well defined, `μ_n`-valued constant and
multiplicative in `x` are proved. -/
theorem mumfordWeilPairingAC_of_bilinRight (h : MumfordWeilBilinRightAC) : MumfordWeilPairingAC := by
  intro k _ _ X n hn hnk x x' hx hx' c c' hc hc'
  refine ⟨fun ψ ψ' => formula_indep X x hx c ψ ψ', fun ψ => formula_root X hn x hx c ψ,
    fun ψ => formula_mul X x x' hx hx' c ψ, fun ψ ψ' ψ'' => h k X n hn hnk x hx c c' hc hc' ψ ψ' ψ''⟩

/-- **The field `weilPairingMumford`** from six of pic-dict's Mumford leaves and the narrower
`MumfordWeilBilinRightAC` in place of `MumfordWeilPairingAC`. -/
theorem weilPairingMumford_of_bilinRight (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (hbil : MumfordWeilBilinRightAC) (h20b : MumfordWeilNondegAC)
    (h23 : MumfordWeilAltAC) (hKL : MumfordKLFiniteAC) : T09Pic.WeilPairingMumford :=
  PicDict.weilPairingMumford_final hsq h8iv h8 (mumfordWeilPairingAC_of_bilinRight hbil) h20b h23 hKL

end WeilProof


/-! ## Step 4: the fourth part from the monoidality of `pullbackComp` (glue) -/

namespace WeilProof

open Scheme.Modules PicDict.Transport MonoidalCategory

/-- **GLUE (`pullbackComp` is monoidal).** For the monoidal structure of `Scheme.Modules.pullback`
(vendored, `Modules/PullbackMonoidal.lean`, obtained by lifting along sheafification), Mathlib's
`pullbackComp f g : g^* ⋙ f^* ≅ (f ≫ g)^*` is a monoidal natural isomorphism: it commutes with the
tensorators `μ`. A formal property of the library's constructions (pull-back of sheaves of modules is
a monoidal pseudofunctor); no published locator is needed. -/
def PullbackCompMonoidal : Prop :=
  ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules),
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N) ≫
      (Scheme.Modules.pullback f).map (Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M N) ≫
        (pullbackComp f g).hom.app (M ⊗ N) =
      ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app N) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback (f ≫ g)) M N

lemma unitor_tensor {C : Type*} [Category C] [MonoidalCategory C] (a b : 𝟙_ C ⟶ 𝟙_ C) :
    (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom = a ≫ b := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality]
  have h1 : a ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ a := by
    rw [unitors_equal, rightUnitor_naturality]
  rw [← Category.assoc (a ▷ _), h1]
  simp

lemma eps_unitor_gen {C D : Type*} [Category C] [MonoidalCategory C] [Category D]
    [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] :
    Functor.LaxMonoidal.ε F ≫ F.map (λ_ (𝟙_ C)).inv =
      (λ_ (𝟙_ D)).inv ≫ (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
        Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) := by
  rw [← Functor.LaxMonoidal.left_unitality_inv, ← Category.assoc, leftUnitor_inv_naturality,
    Category.assoc, MonoidalCategory.tensorHom_def', Category.assoc]

variable {X : Scheme.{0}}

lemma val_unitor_tensor (a b : unit X ⟶ unit X) :
    val ((λ_ (unit X)).inv ≫ (a ⊗ₘ b) ≫ (λ_ (unit X)).hom) = val a * val b := by
  rw [← comp_val]
  exact congrArg val (unitor_tensor (C := X.Modules) a b)

lemma congr_mu {Y : Scheme.{0}} {s m : X ⟶ Y} (e : s = m) (M N : Y.Modules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback s) M N ≫ (pullbackCongr e).hom.app (M ⊗ N) =
      ((pullbackCongr e).hom.app M ⊗ₘ (pullbackCongr e).hom.app N) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback m) M N := by
  subst e; simp [pullbackCongr]

/-- The ratio of `pullbackObjUnitIso⁻¹` and the unit constraint `ε` of `t^*`. -/
def unitRatio (t : X ⟶ X) : unit X ⟶ unit X :=
  (pOU t).inv ≫ (Functor.Monoidal.εIso (Scheme.Modules.pullback t)).inv

/-- The Weil formula with `ε` in place of `pullbackObjUnitIso⁻¹`. -/
def beta (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : unit X ⟶ unit X :=
  Functor.LaxMonoidal.ε (Scheme.Modules.pullback t) ≫ (Scheme.Modules.pullback t).map ψ.hom ≫
    (pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M ≫ ψ.inv

lemma pOU_inv_eq (t : X ⟶ X) :
    (pOU t).inv = unitRatio t ≫ Functor.LaxMonoidal.ε (Scheme.Modules.pullback t) := by
  simp only [unitRatio, Category.assoc]
  rw [← Functor.Monoidal.εIso_hom, Iso.inv_hom_id, Category.comp_id]

lemma alpha_eq_beta (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    alpha t m h M ψ = unitRatio t ≫ beta t m h M ψ := by
  rw [alpha, beta, pOU_inv_eq, Category.assoc]

/-- **Tensor products of trivializations** (from the glue): `α(ψ ⊗ ψ') = r · λ⁻¹(β ⊗ β')λ`. -/
lemma alpha_tensor (hA : PullbackCompMonoidal) (t m : X ⟶ X) (h : t ≫ m = m) (M M' : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) (ψ' : unit X ≅ (Scheme.Modules.pullback m).obj M') :
    alpha t m h (M ⊗ M') ((λ_ (unit X)).symm ≪≫ (ψ ⊗ᵢ ψ') ≪≫
        Functor.Monoidal.μIso (Scheme.Modules.pullback m) M M') =
      unitRatio t ≫ (λ_ (unit X)).inv ≫ (beta t m h M ψ ⊗ₘ beta t m h M' ψ') ≫ (λ_ (unit X)).hom := by
  rw [alpha_eq_beta]
  congr 1
  have h4 := hA t m M M'
  have h5 := congr_mu h M M'
  have h2 : Functor.LaxMonoidal.ε (Scheme.Modules.pullback t) ≫
      (Scheme.Modules.pullback t).map (λ_ (unit X)).inv =
      (λ_ (unit X)).inv ≫ (Functor.LaxMonoidal.ε (Scheme.Modules.pullback t) ⊗ₘ
        Functor.LaxMonoidal.ε (Scheme.Modules.pullback t)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback t) (unit X) (unit X) :=
    eps_unitor_gen (Scheme.Modules.pullback t)
  have h3 := Functor.LaxMonoidal.μ_natural (Scheme.Modules.pullback t) ψ.hom ψ'.hom
  simp only [beta, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, tensorIso_hom,
    tensorIso_inv, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% h2, ← reassoc_of% h3, reassoc_of% h4, reassoc_of% h5, Functor.Monoidal.μ_δ_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]

/-- **The Weil formula of a tensor product of trivializations**, up to the unit ratio. -/
theorem wf_tensor_ratio (hA : PullbackCompMonoidal) (t m : X ⟶ X) (h : t ≫ m = m) (M M' : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) (ψ' : unit X ≅ (Scheme.Modules.pullback m).obj M') :
    wf t m h (M ⊗ M') ((λ_ (unit X)).symm ≪≫ (ψ ⊗ᵢ ψ') ≪≫
        Functor.Monoidal.μIso (Scheme.Modules.pullback m) M M') * val (unitRatio t) =
      wf t m h M ψ * wf t m h M' ψ' := by
  rw [wf_eq_alpha, wf_eq_alpha, wf_eq_alpha, alpha_tensor hA, alpha_eq_beta, alpha_eq_beta,
    comp_val, val_unitor_tensor, comp_val, comp_val]
  ring

/-- The trivial bundle with its canonical trivialization has Weil formula `1`. -/
lemma wf_unit (t m : X ⟶ X) (h : t ≫ m = m) : wf t m h (unit X) (pOU m).symm = 1 := by
  rw [wf_eq_alpha]
  have : alpha t m h (unit X) (pOU m).symm = 𝟙 _ := by
    simp only [alpha, Iso.symm_hom, Iso.symm_inv]
    have e := pOU_inv_comp t m
    rw [← reassoc_of% e, reassoc_of% (pOU_inv_congr h), Iso.inv_hom_id]
  rw [this, id_val]

end WeilProof

namespace WeilProof

open PicDict PkgI3 PkgI3.AbVar Scheme.Modules PicDict.Transport MonoidalCategory
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k]

/-- On an abelian variety, the unit ratio of a translation is `1` (from the glue, by comparing the
two trivializations of `𝒪 ⊗ 𝒪`). -/
lemma unitRatio_tr (hA : PullbackCompMonoidal) (X : AbVar k) {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1) :
    val (unitRatio (AC.tr x).left) = 1 := by
  have h : (AC.tr x).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
    rw [← Over.comp_left, AC.tr_comp_mul x hx]
  set m := (AC.mul X n).left
  set t := (AC.tr x).left
  have e1 := wf_tensor_ratio hA t m h (unit X.X.left) (unit X.X.left) (pOU m).symm (pOU m).symm
  rw [wf_unit, mul_one] at e1
  have e2 := wf_iso t m h (M₁ := unit X.X.left ⊗ unit X.X.left) (M₂ := unit X.X.left)
    (λ_ (unit X.X.left)) ((λ_ (unit X.X.left)).symm ≪≫ ((pOU m).symm ⊗ᵢ (pOU m).symm) ≪≫
      Functor.Monoidal.μIso (Scheme.Modules.pullback m) (unit X.X.left) (unit X.X.left))
  rw [← e2, wf_change t m h (unit X.X.left) (pOU m).symm _ (tr_appTop X x _), wf_unit, one_mul] at e1
  exact e1

/-- **The fourth part from the glue.** -/
theorem mumfordWeilBilinRightAC_of_pullbackCompMonoidal (hA : PullbackCompMonoidal) :
    MumfordWeilBilinRightAC := by
  intro k _ _ X n _ _ x hx c c' _ _ ψ ψ' ψ''
  let m := (AC.mul X n).left
  let ψ₀ : AC.Triv X n (c * c') :=
    ((λ_ (unit X.X.left)).symm ≪≫ (ψ ⊗ᵢ ψ') ≪≫
      Functor.Monoidal.μIso (Scheme.Modules.pullback m) (AC.modX c) (AC.modX c')) ≪≫
      (Scheme.Modules.pullback m).mapIso (Scheme.Pic.mulIso c c').symm
  rw [formula_indep X x hx (c * c') ψ'' ψ₀]
  unfold AC.formula
  rw [wf_iso, ← mul_one (wf _ _ _ (_ ⊗ _) _), ← unitRatio_tr hA X x hx, wf_tensor_ratio hA]

/-- **The field from six Mumford leaves and the glue `PullbackCompMonoidal`.** -/
theorem weilPairingMumford_of_pullbackCompMonoidal (hsq : MumfordSquareAC)
    (h8iv : MumfordMulNPicZeroAC) (h8 : MumfordPhiSurjectiveAC) (hA : PullbackCompMonoidal)
    (h20b : MumfordWeilNondegAC) (h23 : MumfordWeilAltAC) (hKL : MumfordKLFiniteAC) :
    T09Pic.WeilPairingMumford :=
  weilPairingMumford_of_bilinRight hsq h8iv h8 (mumfordWeilBilinRightAC_of_pullbackCompMonoidal hA)
    h20b h23 hKL

/-- pic-dict's §20 leaf `MumfordWeilPairingAC` from the glue alone. -/
theorem mumfordWeilPairingAC_of_pullbackCompMonoidal (hA : PullbackCompMonoidal) :
    MumfordWeilPairingAC :=
  mumfordWeilPairingAC_of_bilinRight (mumfordWeilBilinRightAC_of_pullbackCompMonoidal hA)

end WeilProof

#print axioms WeilProof.weilPairingMumford_of_pullbackCompMonoidal
#print axioms WeilProof.weilPairingMumford_of_bilinRight
