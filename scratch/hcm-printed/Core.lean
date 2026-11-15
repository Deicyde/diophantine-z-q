import ZInQKernel.Contrib.OneProof.QMRecPrinted

noncomputable section

namespace HcmPrinted

open CategoryTheory AlgebraicGeometry Limits Complex MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.LeafPush2 (CPts IsUniformization cEvalAt cDom cptObj)
open AvSplit.HomLatticeAN3 (bcC projC ptE ptE_left)

/-! ## Weierstrass curves and points -/

/-- `y² = x³ − (a/4)x − b/4`, Mathlib's form of `y² = 4x³ − ax − b` (`y ↦ 2y`). -/
def wc (a b : ℂ) : WeierstrassCurve ℂ := ⟨0, 0, 0, -a / 4, -b / 4⟩

open Classical in
/-- `z ↦ (℘(z), ℘'(z)/2) ∈ W(ℂ)` (the point at infinity for `z ∈ Λ`; also `0` if the affine
point is singular on `W`, which for `W = wc g₂ g₃` the leaf `WeierstrassParam` excludes). -/
def wPtW (P : PeriodPair) (W : WeierstrassCurve ℂ) (z : ℂ) : W.toAffine.Point :=
  if h : z ∉ P.lattice ∧ W.toAffine.Nonsingular (P.weierstrassP z) (P.derivWeierstrassP z / 2)
  then .some _ _ h.2 else 0

/-- The Weierstrass parametrization `ℂ → E_Λ(ℂ)` of `E_Λ : y² = 4x³ − g₂x − g₃`, in Mathlib's
normal form `wc g₂ g₃`. -/
def wPt (P : PeriodPair) (z : ℂ) : (wc P.g₂ P.g₃).toAffine.Point := wPtW P (wc P.g₂ P.g₃) z

open Classical in
/-- The properties of the Weierstrass parametrization (the content of the leaf). -/
def ParamProps (P : PeriodPair) (W : WeierstrassCurve ℂ) : Prop :=
  (∀ z w, wPtW P W (z + w) = wPtW P W z + wPtW P W w) ∧
  (∀ z, wPtW P W z = 0 ↔ z ∈ P.lattice) ∧ Function.Surjective (wPtW P W)

/-! ## `σ` on points: `W(ℂ) → W^σ(ℂ)` -/

section MapPt

open WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K] (W : WeierstrassCurve F)
  (f : F →+* K)

/-- The group homomorphism `W(F) → W^f(K)` induced by a field homomorphism (Mathlib's `Point.map` is
stated for algebra maps; this is the same proof with `map_addX`, `map_addY`, `map_negY`). -/
def mapPt : W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.left hxy.right]
      exact (Point.add_of_Y_eq (congr_arg _ hxy.left)
        (by rw [hxy.right, ← WeierstrassCurve.Affine.map_negY])).symm
    · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
        rintro ⟨e1, e2⟩
        exact hxy ⟨f.injective e1, f.injective (by rw [e2, WeierstrassCurve.Affine.map_negY])⟩
      rw [Point.add_some hxy]
      show _ = Point.some _ _ _ + Point.some _ _ _
      rw [Point.add_some hxy']
      simp only [Point.some.injEq]
      rw [WeierstrassCurve.Affine.map_slope, WeierstrassCurve.Affine.map_addX,
        WeierstrassCurve.Affine.map_addY]
      exact ⟨rfl, rfl⟩

theorem mapPt_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    mapPt W f (.some x y h) = .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

theorem mapPt_injective : Function.Injective (mapPt W f) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h (by simp [mapPt])
  · exact absurd h (by simp [mapPt])
  · simp only [mapPt_some, Point.some.injEq] at h
    obtain ⟨e1, e2⟩ := h
    have := f.injective e1; subst this
    have := f.injective e2; subst this
    rfl

end MapPt

theorem map_wc (σ : ℂ →+* ℂ) (a b : ℂ) : (wc a b).map σ = wc (σ a) (σ b) := by
  simp only [wc, WeierstrassCurve.map]
  congr 1 <;> simp [map_neg, map_div₀, map_ofNat]

/-! ## The conjugate abelian variety `A^σ = A ×_{ℂ,σ} ℂ` and its points -/

section Conj

/-- `Spec f : Spec ℂ → Spec ℂ`. -/
abbrev sp (f : ℂ →+* ℂ) : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom f)

theorem sp_comp (f g : ℂ →+* ℂ) : sp f ≫ sp g = sp (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem sp_id : sp (RingHom.id ℂ) = 𝟙 _ := by
  rw [sp, CommRingCat.ofHom_id, Spec.map_id]

variable (σ : ℂ ≃+* ℂ)

theorem sp_symm_comp : sp (σ.symm : ℂ →+* ℂ) ≫ sp (σ : ℂ →+* ℂ) = 𝟙 _ := by
  rw [sp_comp, ← sp_id]; congr 1; ext x; simp

theorem sp_comp_symm : sp (σ : ℂ →+* ℂ) ≫ sp (σ.symm : ℂ →+* ℂ) = 𝟙 _ := by
  rw [sp_comp, ← sp_id]; congr 1; ext x; simp

/-- `Spec ℂ → Spec ℂ` over `σ`: `cptObj id ⟶ cptObj σ`. -/
def tau : cptObj (RingHom.id ℂ) ⟶ cptObj (σ : ℂ →+* ℂ) :=
  Over.homMk (sp (σ.symm : ℂ →+* ℂ)) (by
    change sp (σ.symm : ℂ →+* ℂ) ≫ sp (σ : ℂ →+* ℂ) = sp (RingHom.id ℂ)
    rw [sp_symm_comp, sp_id])

/-- Its inverse. -/
def tauInv : cptObj (σ : ℂ →+* ℂ) ⟶ cptObj (RingHom.id ℂ) :=
  Over.homMk (sp (σ : ℂ →+* ℂ)) (by
    change sp (σ : ℂ →+* ℂ) ≫ sp (RingHom.id ℂ) = sp (σ : ℂ →+* ℂ)
    rw [sp_id, Category.comp_id])

theorem tau_tauInv : tau σ ≫ tauInv σ = 𝟙 _ := by
  ext1; exact sp_symm_comp σ

theorem tauInv_tau : tauInv σ ≫ tau σ = 𝟙 _ := by
  ext1; exact sp_comp_symm σ

/-- The underlying morphism `Spec ℂ → X` of a `ℂ`-point. -/
def pl {X : Over (Spec (CommRingCat.of ℂ))} (p : cptObj (RingHom.id ℂ) ⟶ X) :
    Spec (CommRingCat.of ℂ) ⟶ X.left := p.left

theorem pl_ext {X : Over (Spec (CommRingCat.of ℂ))} {p q : cptObj (RingHom.id ℂ) ⟶ X}
    (h : pl p = pl q) : p = q := Over.OverMorphism.ext h

/-- The value at a `ℂ`-point `a` of a section over `U` (`0` if `a ∉ U`). -/
def evS {X : Scheme} (a : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens) (s : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ a ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (a.appLE U ⊤ h s) else 0

theorem cEvalAt_eq {A : PkgI3.AbVar ℂ} (p : CPts A (RingHom.id ℂ)) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) : cEvalAt p U s = evS (pl p) U s := rfl

variable (A : PkgI3.AbVar ℂ)

/-- The pullback square of `A^σ`. -/
theorem isPullback_bc : IsPullback (projC A (σ : ℂ →+* ℂ)) (bcC A (σ : ℂ →+* ℂ)).X.hom A.X.hom
    (sp (σ : ℂ →+* ℂ)) :=
  IsPullback.of_hasPullback _ _

/-- **De-conjugation of points** `A^σ(ℂ) → A(ℂ)`, `p ↦ σ⁻¹(p)`, a group isomorphism. -/
def dd (p : CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)) : CPts A (RingHom.id ℂ) :=
  tau σ ≫ ptE A (σ : ℂ →+* ℂ) p

theorem dd_mul (p q : CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)) :
    dd σ A (p * q) = dd σ A p * dd σ A q := by
  simp only [dd, map_mul, MonObj.comp_mul]

theorem dd_one : dd σ A 1 = 1 := by
  simp only [dd, map_one, MonObj.comp_one]

theorem dd_left (p : CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)) :
    pl (dd σ A p) = sp (σ.symm : ℂ →+* ℂ) ≫ pl p ≫ projC A (σ : ℂ →+* ℂ) := by
  have := ptE_left A (σ : ℂ →+* ℂ) p
  exact congrArg (fun r => sp (σ.symm : ℂ →+* ℂ) ≫ r) this

theorem dd_key (p : CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)) :
    pl p ≫ projC A (σ : ℂ →+* ℂ) = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ A p) := by
  rw [dd_left, ← Category.assoc, sp_comp_symm, Category.id_comp]

theorem dd_unique {p : CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)} {q : CPts A (RingHom.id ℂ)}
    (h : pl p ≫ projC A (σ : ℂ →+* ℂ) = sp (σ : ℂ →+* ℂ) ≫ pl q) : dd σ A p = q := by
  apply pl_ext
  rw [dd_left, h, ← Category.assoc, sp_symm_comp, Category.id_comp]

theorem dd_injective : Function.Injective (dd σ A) := by
  intro p q h
  apply (ptE A (σ : ℂ →+* ℂ)).injective
  have h' := congrArg (fun r => tauInv σ ≫ r) h
  simp only [dd, ← Category.assoc, tauInv_tau, Category.id_comp] at h'
  exact h'

theorem dd_surjective : Function.Surjective (dd σ A) := by
  intro q
  refine ⟨(ptE A (σ : ℂ →+* ℂ)).symm (tauInv σ ≫ q), ?_⟩
  simp only [dd, MulEquiv.apply_symm_apply, ← Category.assoc, tau_tauInv, Category.id_comp]

/-- The identity clause of `MainTheoremCM` for `A^σ`. -/
theorem one_left_bc : pl (1 : CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ)) ≫ projC A (σ : ℂ →+* ℂ) =
    sp (σ : ℂ →+* ℂ) ≫ pl (1 : CPts A (RingHom.id ℂ)) := by
  rw [dd_key, dd_one]

theorem top_le_preimage_iff {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ X) (hgf : g ≫ f = 𝟙 Y)
    (V : Y.Opens) : ⊤ ≤ f ⁻¹ᵁ V ↔ ⊤ ≤ V := by
  constructor
  · intro h y _
    have : y = f (g y) := by rw [← Scheme.Hom.comp_apply, hgf]; rfl
    rw [this]; exact h trivial
  · intro h x _; exact h trivial

theorem appLE_congr_apply {X Y : Scheme} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (s : Γ(Y, U)) : f.appLE U V e s = g.appLE U V (hfg ▸ e) s := by
  subst hfg; rfl

theorem evS_comp {X Y : Scheme} (a : Spec (CommRingCat.of ℂ) ⟶ X) (h : X ⟶ Y) (U : Y.Opens)
    (s : Γ(Y, U)) : evS (a ≫ h) U s = evS a (h ⁻¹ᵁ U) (h.app U s) := by
  unfold evS
  by_cases hp : ⊤ ≤ a ⁻¹ᵁ (h ⁻¹ᵁ U)
  · have hp' : ⊤ ≤ (a ≫ h) ⁻¹ᵁ U := hp
    rw [dif_pos hp', dif_pos hp]
    congr 1
  · have hp' : ¬ ⊤ ≤ (a ≫ h) ⁻¹ᵁ U := hp
    rw [dif_neg hp', dif_neg hp]

theorem evS_congr {X : Scheme} {a b : Spec (CommRingCat.of ℂ) ⟶ X} (hab : a = b) (U : X.Opens)
    (s : Γ(X, U)) : evS a U s = evS b U s := by subst hab; rfl

theorem evS_sp {Y : Scheme} (b : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) (s : Γ(Y, U))
    (hq : ⊤ ≤ b ⁻¹ᵁ U) : evS (sp (σ : ℂ →+* ℂ) ≫ b) U s = σ (evS b U s) := by
  unfold evS
  have hq' : ⊤ ≤ (sp (σ : ℂ →+* ℂ) ≫ b) ⁻¹ᵁ U :=
    le_trans (le_of_eq rfl) (Scheme.Hom.preimage_mono _ hq)
  rw [dif_pos hq', dif_pos hq]
  rw [← Scheme.Hom.appLE_comp_appLE (sp (σ : ℂ →+* ℂ)) b U ⊤ ⊤ hq le_rfl]
  have e2 : (sp (σ : ℂ →+* ℂ)).appLE ⊤ ⊤ le_rfl = (sp (σ : ℂ →+* ℂ)).appTop := by
    exact Scheme.Hom.appLE_eq_app _
  rw [CommRingCat.comp_apply, e2]
  have e3 := congrArg (fun φ => φ (b.appLE U ⊤ hq s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (σ : ℂ →+* ℂ)))
  simp only at e3
  exact e3

/-- **Evaluating a pulled-back regular function at a conjugate point.** -/
theorem eval_conj {X Y : Scheme} (h : X ⟶ Y) {a : Spec (CommRingCat.of ℂ) ⟶ X}
    {b : Spec (CommRingCat.of ℂ) ⟶ Y} (hab : a ≫ h = sp (σ : ℂ →+* ℂ) ≫ b) (U : Y.Opens)
    (s : Γ(Y, U)) :
    (⊤ ≤ a ⁻¹ᵁ (h ⁻¹ᵁ U) ↔ ⊤ ≤ b ⁻¹ᵁ U) ∧
      (⊤ ≤ b ⁻¹ᵁ U → evS a (h ⁻¹ᵁ U) (h.app U s) = σ (evS b U s)) := by
  have hmem : ⊤ ≤ a ⁻¹ᵁ (h ⁻¹ᵁ U) ↔ ⊤ ≤ b ⁻¹ᵁ U := by
    change ⊤ ≤ (a ≫ h) ⁻¹ᵁ U ↔ _
    rw [hab]
    change ⊤ ≤ sp (σ : ℂ →+* ℂ) ⁻¹ᵁ (b ⁻¹ᵁ U) ↔ _
    exact top_le_preimage_iff _ _ (sp_symm_comp σ) _
  refine ⟨hmem, fun hq => ?_⟩
  rw [← evS_comp, evS_congr hab, evS_sp σ b U s hq]

end Conj

end HcmPrinted
