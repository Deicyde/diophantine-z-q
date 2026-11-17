import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.Contrib.OneProof.PicDictionary

/-! # weil-proof: Mumford's `ē_n` by its formula — well defined, `μ_n`-valued, bilinear

Task weil-proof (docs/research/weil-proof.md). The field `OpenAddedLeaves17.weilPairingMumford :
T09Pic.WeilPairingMumford` (`ZInQKernel/OneProof/H/TailZ24.lean`). pic-dict
(`ZInQKernel/Contrib/OneProof/PicDictionary.lean`, `PicDict.weilPairingMumford_final`) reduced it to seven of
Mumford's displays over an algebraically closed field. This file proves one of them,
`PicDict.MumfordWeilPairingAC` (§20: the formula `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` is independent of `ψ`, is a
constant `n`-th root of unity, and is bilinear) **outright**:

* `formula_indep`, `formula_root`, `formula_mul` (three of the four conjuncts) are proved outright, over any
  field, from the cocycle relation `wf_comp` of the formula and the vendored `Γ(X, 𝒪) = k`;
* the fourth conjunct (multiplicativity in the class) is `mumfordWeilBilinRightAC_of_pullbackCompMonoidal`
  from `PullbackCompMonoidal` (Mathlib's `Scheme.Modules.pullbackComp` commutes with the vendored tensorators of
  `Scheme.Modules.pullback`; the unit constraint is derived, `unitRatio_tr`), and `PullbackCompMonoidal` is proved
  (`pullbackCompMonoidal_proof`, section `PullbackCompMonoidalSec`: reduction to sheafified objects, the
  compatibility (E) of `pullbackComp` with `sheafificationCompPullback`, and (P) the presheaf `pullbackComp` is
  monoidal, from the general mates lemma `Mates.leftAdjointCompIso_δ`).

Main results:
* `WeilProof.mumfordWeilPairingAC_proof : PicDict.MumfordWeilPairingAC`;
* `WeilProof.weilPairingMumford_proof` (the field from five Mumford leaves and the open field `phiAmpleIsogeny`);
* `WeilProof.weilPairingMumford_of_six` (the same with `MumfordKLFiniteAC` for `phiAmpleIsogeny`). -/

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


section PullbackCompMonoidalSec
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory Limits

section MatesSec
open Functor.LaxMonoidal Functor.OplaxMonoidal
namespace WeilProof.Mates

variable {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂]
  {F₁ : C₀ ⥤ C₁} {G₁ : C₁ ⥤ C₀} {F₂ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₁} {F₃ : C₀ ⥤ C₂} {G₃ : C₂ ⥤ C₀}
  (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (adj₃ : F₃ ⊣ G₃)
  [G₁.LaxMonoidal] [G₂.LaxMonoidal] [G₃.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- **The left adjoint comparison of a monoidal right adjoint comparison is oplax monoidal.** -/
theorem leftAdjointCompIso_δ (e : G₂ ⋙ G₁ ≅ G₃)
    (he : ∀ X Y : C₂, μ G₁ (G₂.obj X) (G₂.obj Y) ≫ G₁.map (μ G₂ X Y) ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ G₃ X Y) (X Y : C₀) :
    letI := adj₁.leftAdjointOplaxMonoidal
    letI := adj₂.leftAdjointOplaxMonoidal
    letI := adj₃.leftAdjointOplaxMonoidal
    δ F₃ X Y ≫ ((Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e).inv.app X ⊗ₘ
        (Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e).inv.app Y) =
      (Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e).inv.app (X ⊗ Y) ≫
        F₂.map (δ F₁ X Y) ≫ δ F₂ (F₁.obj X) (F₁.obj Y) := by
  let _ := adj₁.leftAdjointOplaxMonoidal
  let _ := adj₂.leftAdjointOplaxMonoidal
  let _ := adj₃.leftAdjointOplaxMonoidal
  set ψ := Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e
  have hu : ∀ Z : C₀, adj₃.unit.app Z ≫ G₃.map (ψ.inv.app Z) =
      (adj₁.comp adj₂).unit.app Z ≫ e.hom.app ((F₁ ⋙ F₂).obj Z) := by
    intro Z
    rw [← unit_conjugateEquiv (adj₁.comp adj₂) adj₃ ψ.inv Z,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  have hC := Adjunction.unit_app_tensor_comp_map_δ (adj₁.comp adj₂) X Y
  simp only [Functor.comp_map, Functor.OplaxMonoidal.comp_δ] at hC
  apply (adj₃.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    Adjunction.unit_app_tensor_comp_map_δ_assoc, ← μ_natural, tensorHom_comp_tensorHom_assoc, hu, hu,
    ← tensorHom_comp_tensorHom_assoc, ← he, Functor.map_comp, reassoc_of% (hu (X ⊗ Y))]
  have hn := e.hom.naturality (F₂.map (δ F₁ X Y) ≫ δ F₂ (F₁.obj X) (F₁.obj Y))
  simp only [Functor.comp_map] at hn
  rw [← hn, reassoc_of% hC]
  simp [Functor.LaxMonoidal.comp_μ]

end WeilProof.Mates

end MatesSec

namespace WeilProof.PBM
open Scheme.Modules

universe u
variable {X Y Z : Scheme.{u}}

attribute [local instance] Scheme.Modules.presheafPullbackCompSheafificationMonoidal

abbrev PP (f : X ⟶ Y) :=
  PresheafOfModules.pullbackOfCommRingCat (F := TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev GG (f : X ⟶ Y) := PP f ⋙ sheafification X

abbrev ee (f : X ⟶ Y) : Scheme.Modules.sheafification Y ⋙ Scheme.Modules.pullback f ≅
    PP f ⋙ Scheme.Modules.sheafification X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

example (f : X ⟶ Y) : (PP f).Monoidal := inferInstance
example (f : X ⟶ Y) : (GG f).Monoidal := inferInstance
example : (sheafification X).Monoidal := inferInstance

lemma mu_sheafified (f : X ⟶ Y) (A B : Y.PresheafOfModules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((sheafification Y).obj A)
        ((sheafification Y).obj B) =
      ((ee f).hom.app A ⊗ₘ (ee f).hom.app B) ≫
        Functor.LaxMonoidal.μ (sheafification X) ((PP f).obj A) ((PP f).obj B) ≫
        (sheafification X).map (Functor.LaxMonoidal.μ (PP f) A B) ≫
        (ee f).inv.app (A ⊗ B) ≫
        (Scheme.Modules.pullback f).map (Functor.OplaxMonoidal.δ (sheafification Y) A B) := by
  let _ : (GG f).Monoidal := presheafPullbackCompSheafificationMonoidal f
  let _ := Scheme.Modules.pullbackLocalizationLifting f
  exact Localization.Monoidal.functorMonoidalOfComp_μ (sheafification Y) _ (Scheme.Modules.pullback f)
    (GG f) A B

abbrev PF (f : X ⟶ Y) := PresheafOfModules.pushforwardOfCommRingCat
  (F := TopologicalSpace.Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev AD (f : X ⟶ Y) : PP f ⊣ PF f := PresheafOfModules.adjunctionOfCommRingCat
  (F := TopologicalSpace.Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev PFQ (f : X ⟶ Y) := PresheafOfModules.pushforward f.toRingCatSheafHom.hom

def eQ (f : X ⟶ Y) (g : Y ⟶ Z) : PFQ f ⋙ PFQ g ≅ PFQ (f ≫ g) := PresheafOfModules.pushforwardComp _ _

def eF (f : X ⟶ Y) (g : Y ⟶ Z) : PF f ⋙ PF g ≅ PF (f ≫ g) := eQ f g

def pcP (f : X ⟶ Y) (g : Y ⟶ Z) : PP g ⋙ PP f ≅ PP (f ≫ g) :=
  Adjunction.leftAdjointCompIso (AD g) (AD f) (AD (f ≫ g)) (eF f g)


abbrev shA (X : Scheme.{u}) := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

abbrev adjS (f : X ⟶ Y) := Scheme.Modules.pullbackPushforwardAdjunction f

abbrev RS (X : Scheme.{u}) := SheafOfModules.forget X.ringCatSheaf ⋙
  PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)

lemma push_RS (g : Y ⟶ Z) {M N : Y.Modules} (h : M ⟶ N) :
    (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map h)) =
      (PF g).map ((PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Y.ringCatSheaf).map h)) := rfl

lemma push_push (f : X ⟶ Y) (g : Y ⟶ Z) {M N : X.Modules} (h : M ⟶ N) :
    (pushforward g).map ((pushforward f).map h) = (pushforward (f ≫ g)).map h := rfl

lemma PF_PF (f : X ⟶ Y) (g : Y ⟶ Z) {M N : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)}
    (h : M ⟶ N) : (PF g).map ((PF f).map h) = (PF (f ≫ g)).map h := rfl

/-- (U1) -/
lemma unit_ee (f : X ⟶ Y) (P : Y.PresheafOfModules) :
    (shA Y).unit.app P ≫ (RS Y).map ((adjS f).unit.app ((Scheme.Modules.sheafification Y).obj P)) ≫
        (RS Y).map ((pushforward f).map ((ee f).hom.app P)) =
      (AD f).unit.app P ≫ (PF f).map ((shA X).unit.app ((PP f).obj P)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app ((shA Y).comp (adjS f)) ((AD f).comp (shA X)) P
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  exact h

/-- (U3) -/
lemma unit_pcP (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.PresheafOfModules) :
    (AD g).unit.app A ≫ (PF g).map ((AD f).unit.app ((PP g).obj A)) ≫
        (PF g).map ((PF f).map ((pcP f g).hom.app A)) = (AD (f ≫ g)).unit.app A := by
  have h := unit_conjugateEquiv_symm (AD (f ≫ g)) ((AD g).comp (AD f)) (eF f g).inv A
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  rw [← Functor.map_comp]
  exact h.symm

/-- (U2) -/
lemma unit_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (adjS g).unit.app M ≫ (pushforward g).map ((adjS f).unit.app ((Scheme.Modules.pullback g).obj M)) ≫
        (pushforward g).map ((pushforward f).map ((pullbackComp f g).hom.app M)) =
      (adjS (f ≫ g)).unit.app M := by
  have h := unit_conjugateEquiv_symm (adjS (f ≫ g)) ((adjS g).comp (adjS f))
    (Scheme.Modules.pushforwardComp f g).inv M
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  rw [← Functor.map_comp]
  exact h.symm

set_option maxHeartbeats 1000000 in
/-- (E) -/
lemma ee_comp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.PresheafOfModules) :
    (Scheme.Modules.pullback f).map ((ee g).hom.app A) ≫ (ee f).hom.app ((PP g).obj A) ≫
        (Scheme.Modules.sheafification X).map ((pcP f g).hom.app A) =
      (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj A) ≫ (ee (f ≫ g)).hom.app A := by
  apply (((shA Z).comp ((adjS g).comp (adjS f))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc, Functor.comp_map, Functor.comp_obj]
  -- right side
  have u2 := congrArg (fun φ => (RS Z).map φ) (unit_pullbackComp f g ((Scheme.Modules.sheafification Z).obj A))
  simp only [Functor.map_comp, Functor.comp_map] at u2
  dsimp only [Scheme.Modules.sheafification] at u2 ⊢
  rw [reassoc_of% u2, push_push f g ((ee (f ≫ g)).hom.app A)]
  have u1fg := unit_ee (f ≫ g) A
  simp only [Functor.comp_map] at u1fg
  dsimp only [Scheme.Modules.sheafification] at u1fg
  rw [u1fg]
  -- left side
  have nat := (adjS f).unit.naturality ((ee g).hom.app A)
  have n2 : (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map
          ((adjS f).unit.app ((Scheme.Modules.pullback g).obj
            ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj A))))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map ((pushforward f).map
          ((Scheme.Modules.pullback f).map ((ee g).hom.app A))))) =
      (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map ((ee g).hom.app A))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map
          ((adjS f).unit.app ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
            ((PP g).obj A))))) := by
    simp only [← Functor.map_comp]
    congr 3
    exact nat.symm
  rw [reassoc_of% n2]
  have u1g := unit_ee g A
  simp only [Functor.comp_map] at u1g
  dsimp only [Scheme.Modules.sheafification] at u1g
  rw [reassoc_of% u1g]
  rw [push_RS g, push_RS g, push_RS g]
  have u1f := unit_ee f ((PP g).obj A)
  simp only [Functor.comp_map] at u1f
  dsimp only [Scheme.Modules.sheafification] at u1f
  have natX := (shA X).unit.naturality ((pcP f g).hom.app A)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at natX
  have key : (shA Y).unit.app ((PP g).obj A) ≫
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map ((SheafOfModules.forget Y.ringCatSheaf).map
        ((adjS f).unit.app ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj ((PP g).obj A)))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map ((SheafOfModules.forget Y.ringCatSheaf).map
        ((pushforward f).map ((ee f).hom.app ((PP g).obj A)))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map ((SheafOfModules.forget Y.ringCatSheaf).map
        ((pushforward f).map ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((pcP f g).hom.app A)))) =
      (AD f).unit.app ((PP g).obj A) ≫ (PF f).map ((pcP f g).hom.app A) ≫
        (PF f).map ((shA X).unit.app ((PP (f ≫ g)).obj A)) := by
    rw [reassoc_of% u1f, push_RS f, ← Functor.map_comp, ← natX, Functor.map_comp]
  rw [← Functor.map_comp (PF g), ← Functor.map_comp (PF g), ← Functor.map_comp (PF g), key,
    Functor.map_comp, Functor.map_comp, reassoc_of% (unit_pcP f g A), PF_PF f g]

lemma mu_tmul (f : X ⟶ Y) (M N : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
    (U : (TopologicalSpace.Opens Y)ᵒᵖ) (m : M.obj ((TopologicalSpace.Opens.map f.base).op.obj U))
    (n : N.obj ((TopologicalSpace.Opens.map f.base).op.obj U)) :
    ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PF f) M N).app U) (m ⊗ₜ n) = m ⊗ₜ n :=
  PresheafOfModules.pushforward_μ_app_tmul _ M N U m n

/-- presheaf pushforward composition is monoidal -/
lemma eF_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) (M N : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :
    Functor.LaxMonoidal.μ (PF g) ((PF f).obj M) ((PF f).obj N) ≫ (PF g).map (Functor.LaxMonoidal.μ (PF f) M N) ≫
        (eF f g).hom.app (M ⊗ N) =
      ((eF f g).hom.app M ⊗ₘ (eF f g).hom.app N) ≫ Functor.LaxMonoidal.μ (PF (f ≫ g)) M N := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have h1 := mu_tmul g ((PF f).obj M) ((PF f).obj N) U m n
  erw [h1]
  change ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PF f) M N).app _) (m ⊗ₜ n) =
    ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PF (f ≫ g)) M N).app U) (m ⊗ₜ n)
  rw [mu_tmul, mu_tmul]
  rfl

/-- (P), δ-form -/
lemma pcP_delta (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.OplaxMonoidal.δ (PP (f ≫ g)) A B ≫ ((pcP f g).inv.app A ⊗ₘ (pcP f g).inv.app B) =
      (pcP f g).inv.app (A ⊗ B) ≫ (PP f).map (Functor.OplaxMonoidal.δ (PP g) A B) ≫
        Functor.OplaxMonoidal.δ (PP f) ((PP g).obj A) ((PP g).obj B) := by
  exact Mates.leftAdjointCompIso_δ (AD g) (AD f) (AD (f ≫ g)) (eF f g) (eF_monoidal f g) A B

/-- (P) -/
lemma pcP_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.LaxMonoidal.μ (PP f) ((PP g).obj A) ((PP g).obj B) ≫
        (PP f).map (Functor.LaxMonoidal.μ (PP g) A B) ≫ (pcP f g).hom.app (A ⊗ B) =
      ((pcP f g).hom.app A ⊗ₘ (pcP f g).hom.app B) ≫ Functor.LaxMonoidal.μ (PP (f ≫ g)) A B := by
  rw [← cancel_mono (Functor.OplaxMonoidal.δ (PP (f ≫ g)) A B ≫
    ((pcP f g).inv.app A ⊗ₘ (pcP f g).inv.app B))]
  conv_lhs => rw [pcP_delta]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.Monoidal.μ_δ_assoc,
    tensorHom_comp_tensorHom, Iso.hom_inv_id_app]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.Monoidal.μ_δ]
  simp

/-- The main identity on sheafified objects. -/
theorem main_sheafified (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((Scheme.Modules.pullback g).obj ((Scheme.Modules.sheafification Z).obj A))
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.sheafification Z).obj B)) ≫
      (Scheme.Modules.pullback f).map
        (Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) ((Scheme.Modules.sheafification Z).obj A) ((Scheme.Modules.sheafification Z).obj B)) ≫
        (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj A ⊗ (Scheme.Modules.sheafification Z).obj B) =
      ((pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj A) ⊗ₘ (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj B)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback (f ≫ g)) ((Scheme.Modules.sheafification Z).obj A) ((Scheme.Modules.sheafification Z).obj B) := by
  -- precompose with the iso `f^*(e_g⁻¹) ⊗ f^*(e_g⁻¹)`
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((ee g).inv.app A) ⊗ₘ
    (Scheme.Modules.pullback f).map ((ee g).inv.app B))]
  -- LHS: naturality of `μ_f`
  have n1 := Functor.LaxMonoidal.μ_natural (Scheme.Modules.pullback f) ((ee g).inv.app A) ((ee g).inv.app B)
  simp only [Functor.comp_obj] at n1
  rw [reassoc_of% n1]
  rw [mu_sheafified f, mu_sheafified g, mu_sheafified (f ≫ g)]
  simp only [Functor.map_comp, Category.assoc]
  have c1 : (Scheme.Modules.pullback f).map ((ee g).inv.app A ⊗ₘ (ee g).inv.app B) ≫
      (Scheme.Modules.pullback f).map ((ee g).hom.app A ⊗ₘ (ee g).hom.app B) = 𝟙 _ := by
    rw [← Functor.map_comp, tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    simp
  have c2 : (Scheme.Modules.pullback f).map (Functor.OplaxMonoidal.δ (Scheme.Modules.sheafification Y) ((PP g).obj A) ((PP g).obj B)) ≫
      (Scheme.Modules.pullback f).map (Functor.LaxMonoidal.μ (Scheme.Modules.sheafification Y) ((PP g).obj A) ((PP g).obj B)) = 𝟙 _ := by
    rw [← Functor.map_comp, Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id]
  have c3 : (ee f).inv.app ((PP g).obj A ⊗ (PP g).obj B) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.sheafification Y).map (Functor.LaxMonoidal.μ (PP g) A B)) =
      (Scheme.Modules.sheafification X).map ((PP f).map (Functor.LaxMonoidal.μ (PP g) A B)) ≫ (ee f).inv.app ((PP g).obj (A ⊗ B)) :=
    ((ee f).inv.naturality (Functor.LaxMonoidal.μ (PP g) A B)).symm
  have c4 : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (Functor.OplaxMonoidal.δ (Scheme.Modules.sheafification Z) A B)) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj A ⊗ (Scheme.Modules.sheafification Z).obj B) =
      (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj (A ⊗ B)) ≫
        (Scheme.Modules.pullback (f ≫ g)).map (Functor.OplaxMonoidal.δ (Scheme.Modules.sheafification Z) A B) :=
    (pullbackComp f g).hom.naturality (Functor.OplaxMonoidal.δ (Scheme.Modules.sheafification Z) A B)
  have hE : ∀ C : Z.PresheafOfModules, (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj C) =
      (Scheme.Modules.pullback f).map ((ee g).hom.app C) ≫ (ee f).hom.app ((PP g).obj C) ≫
        (Scheme.Modules.sheafification X).map ((pcP f g).hom.app C) ≫ (ee (f ≫ g)).inv.app C := by
    intro C
    rw [reassoc_of% (ee_comp f g C), Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have c5 : (ee f).inv.app ((PP g).obj (A ⊗ B)) ≫ (Scheme.Modules.pullback f).map ((ee g).inv.app (A ⊗ B)) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj (A ⊗ B)) =
      (Scheme.Modules.sheafification X).map ((pcP f g).hom.app (A ⊗ B)) ≫ (ee (f ≫ g)).inv.app (A ⊗ B) := by
    rw [hE]
    simp [← Functor.map_comp_assoc]
  have c6 : ∀ C : Z.PresheafOfModules, (Scheme.Modules.pullback f).map ((ee g).inv.app C) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.sheafification Z).obj C) ≫ (ee (f ≫ g)).hom.app C =
      (ee f).hom.app ((PP g).obj C) ≫ (Scheme.Modules.sheafification X).map ((pcP f g).hom.app C) := by
    intro C
    rw [hE]
    simp [← Functor.map_comp_assoc]
  rw [reassoc_of% c1]
  try simp only [Category.id_comp]
  rw [reassoc_of% c2]
  try simp only [Category.id_comp]
  rw [reassoc_of% c3, c4, reassoc_of% c5]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [c6, c6, ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc]
  have hP := congrArg (fun φ => (Scheme.Modules.sheafification X).map φ) (pcP_monoidal f g A B)
  simp only [Functor.map_comp] at hP
  rw [reassoc_of% hP]

/-- The counit `L(M.val) ≅ M`. -/
abbrev epsM (M : Z.Modules) : (Scheme.Modules.sheafification Z).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).counit).app M

/-- **`pullbackComp` is monoidal**, from (E) and (P). -/
theorem pullbackComp_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N) ≫
      (Scheme.Modules.pullback f).map (Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M N) ≫
        (pullbackComp f g).hom.app (M ⊗ N) =
      ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app N) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback (f ≫ g)) M N := by
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (epsM M).hom) ⊗ₘ
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (epsM N).hom))]
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp_assoc, Functor.LaxMonoidal.μ_natural,
    Functor.map_comp_assoc]
  have nc := (pullbackComp f g).hom.naturality ((epsM M).hom ⊗ₘ (epsM N).hom)
  simp only [Functor.comp_map] at nc
  rw [nc, tensorHom_comp_tensorHom_assoc]
  have nM := (pullbackComp f g).hom.naturality (epsM M).hom
  have nN := (pullbackComp f g).hom.naturality (epsM N).hom
  simp only [Functor.comp_map] at nM nN
  rw [nM, nN, ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural]
  rw [reassoc_of% (main_sheafified f g M.val N.val)]

end WeilProof.PBM

end PullbackCompMonoidalSec

namespace WeilProof

open PicDict

/-- **`PullbackCompMonoidal` is a theorem** (pull-back of sheaves of modules is a monoidal pseudofunctor
for the vendored monoidal structure): `WeilProof.PBM.pullbackComp_monoidal`. -/
theorem pullbackCompMonoidal_proof : PullbackCompMonoidal :=
  fun f g M N => PBM.pullbackComp_monoidal f g M N

/-- **pic-dict's §20 leaf `MumfordWeilPairingAC` is a theorem**: Mumford's `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` is
independent of `ψ`, a constant `n`-th root of unity, and bilinear. -/
theorem mumfordWeilPairingAC_proof : MumfordWeilPairingAC :=
  mumfordWeilPairingAC_of_pullbackCompMonoidal pullbackCompMonoidal_proof

/-- **The field `weilPairingMumford` (fold form).** From five of pic-dict's Mumford leaves (§6 Cor. 4, §8 (iv),
§8 Thm 1, §20 nondegeneracy, §23) and the open field `T09Pic.PhiAmpleIsogeny` (which replaces
`MumfordKLFiniteAC`, its only use; in leaf-fold32 the field is `PicFix.phiAmpleIsogeny_of_printed` of two printed
leaves). pic-dict's §20 leaf `MumfordWeilPairingAC` is proved (`mumfordWeilPairingAC_proof`). -/
theorem weilPairingMumford_proof (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20b : MumfordWeilNondegAC) (h23 : MumfordWeilAltAC)
    (h3 : T09Pic.PhiAmpleIsogeny) : T09Pic.WeilPairingMumford :=
  PicDict.weilPairingMumford_of_mumford hsq h8iv h8 mumfordWeilPairingAC_proof h20b h23 h3

/-- The same with pic-dict's `MumfordKLFiniteAC` in place of the open field `phiAmpleIsogeny`. -/
theorem weilPairingMumford_of_six (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20b : MumfordWeilNondegAC) (h23 : MumfordWeilAltAC)
    (hKL : MumfordKLFiniteAC) : T09Pic.WeilPairingMumford :=
  PicDict.weilPairingMumford_final hsq h8iv h8 mumfordWeilPairingAC_proof h20b h23 hKL

end WeilProof
