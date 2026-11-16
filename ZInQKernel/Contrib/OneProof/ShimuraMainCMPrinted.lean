import ZInQKernel.Contrib.OneProof.QMRecPrinted

/-!
# hcm-printed: `T5Glue.ShimuraMainCM` (hypothesis `hCM` of `ZInQ.OneProof.frozenTarget`) from printed leaves

Task hcm-printed (2026-11-15). Report: `docs/research/hcm-printed.md`; log: `scratch/hcm-printed/log.md`.

`T5Glue.ShimuraMainCM` (`RingClassLattice.lean`) is the main theorem of complex multiplication in Weierstrass
coordinates; its docstring calls that form "a standard consequence" of Shimura 1971 Thm 5.4. This file proves it:

* `shimuraMainCM_of_printed : MainTheoremCMArith → WeierstrassUniformization → WeierstrassParam →
  WeierstrassAbVar → ZInQ.HomUnify.HomLatticeCorr → T5Glue.ShimuraMainCM`.

Leaves: `MainTheoremCMArith` (qmrec-printed's adelic `MainTheoremCM` with Shimura's sign `ε = 1`;
`mainTheoremCM_of_arith`), `WeierstrassUniformization` (Silverman VI.5.1, gz-weil's statement verbatim),
`WeierstrassParam` (Silverman VI.3.6), `WeierstrassAbVar` (`E_Λ` as a `PkgI3.AbVar` with Weierstrass coordinates
and the uniformization `z ↦ [℘, ℘', 1]`), and the bundles' `HomLatticeCorr`. Glue, all proved here:

* `lin`: a homomorphism `ℂ/Λ' → ℂ/Λ''` with holomorphic Weierstrass coordinates is `z ↦ αz` (inverse function
  theorem for `℘`, discreteness of `Λ''`, additivity);
* `mapPt`, `dd`, `eval_conj`: `σ` on Mathlib's Weierstrass points, points and regular functions of
  `A^σ = A ×_{ℂ,σ} ℂ`;
* `core`: Weierstrass coordinates on `A^σ` (`σ(℘_P(z)) = ν²℘_{P'}(z')`, `σ(g₂) = ν⁴g₂'`, ...);
* `artinCondC_of_artinCond`, `isCMField_QNeg`, `type_inj`, `reflex_range`, `model`, `reflexNorm_rhoQ`, `adelic`,
  `cmLat_eq`, `isOfType_of_corr`: the specialization of the adelic main theorem to `K = ℚ(√−m)`, `g = 1`.

No `sorry`, no `axiom`; only `propext`, `Classical.choice`, `Quot.sound`.
-/

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

/-! ## Glue LIN (verbatim from scratch/hcm-printed/Lin.lean) -/

section LinSec
open Filter Topology Metric Set
section Lin

variable (P' P'' : PeriodPair)

theorem psi_nsmul (ψ₀ : ℂ → ℂ) (h0 : ψ₀ 0 ∈ P''.lattice)
    (hadd : ∀ z w, ψ₀ (z + w) - ψ₀ z - ψ₀ w ∈ P''.lattice) :
    ∀ (n : ℕ) (v : ℂ), ψ₀ (n * v) - n * ψ₀ v ∈ P''.lattice := by
  intro n v
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have e : ψ₀ (((n + 1 : ℕ) : ℂ) * v) - ((n + 1 : ℕ) : ℂ) * ψ₀ v =
        (ψ₀ (n * v + v) - ψ₀ (n * v) - ψ₀ v) + (ψ₀ (n * v) - n * ψ₀ v) := by
      push_cast; ring_nf
    rw [e]
    exact add_mem (hadd _ _) ih

theorem third_not_mem : P''.ω₁ / 3 ∉ P''.lattice := by
  intro h
  have : ((1 / 3 : ℚ) : ℂ) * P''.ω₁ + ((0 : ℚ) : ℂ) * P''.ω₂ ∈ P''.lattice := by
    convert h using 1; push_cast; ring
  rw [PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice] at this
  exact absurd this.1 (by norm_num)

theorem two_third_not_mem : P''.ω₁ / 3 - -(P''.ω₁ / 3) ∉ P''.lattice := by
  intro h
  have : ((2 / 3 : ℚ) : ℂ) * P''.ω₁ + ((0 : ℚ) : ℂ) * P''.ω₂ ∈ P''.lattice := by
    convert h using 1; push_cast; ring
  rw [PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice] at this
  exact absurd this.1 (by norm_num)

theorem neg_not_mem {w : ℂ} (hw : w ∉ P''.lattice) : -w ∉ P''.lattice := fun h =>
  hw (by simpa using neg_mem h)

theorem isOpen_compl_lattice (P : PeriodPair) : IsOpen ((P.lattice : Set ℂ)ᶜ) :=
  P.isClosed_lattice.isOpen_compl

/-- **LIN.** Let `ψ₀ : ℂ → ℂ` induce an injective, surjective homomorphism `ℂ/Λ' → ℂ/Λ''` whose
Weierstrass coordinates `(℘_{Λ''}(ψ₀ z), ℘'_{Λ''}(ψ₀ z)) = (F z, G z)` are holomorphic (resp.
continuous) off `Λ'`, where `(℘_{Λ''}, ℘'_{Λ''})` is injective on `(ℂ/Λ'') ∖ 0`. Then
`ψ₀ z ≡ αz (mod Λ'')` for a constant `α`. -/
theorem lin (ψ₀ F G : ℂ → ℂ)
    (hinj : ∀ a b, a ∉ P''.lattice → b ∉ P''.lattice → P''.weierstrassP a = P''.weierstrassP b →
      P''.derivWeierstrassP a = P''.derivWeierstrassP b → a - b ∈ P''.lattice)
    (hadd : ∀ z w, ψ₀ (z + w) - ψ₀ z - ψ₀ w ∈ P''.lattice)
    (hker : ∀ z, ψ₀ z ∈ P''.lattice ↔ z ∈ P'.lattice)
    (hsurj : ∀ a, ∃ z, ψ₀ z - a ∈ P''.lattice)
    (hF : ∀ z, z ∉ P'.lattice → P''.weierstrassP (ψ₀ z) = F z ∧ P''.derivWeierstrassP (ψ₀ z) = G z)
    (hFd : DifferentiableOn ℂ F (P'.lattice : Set ℂ)ᶜ) (hGc : ContinuousOn G (P'.lattice : Set ℂ)ᶜ) :
    ∃ α : ℂ, ∀ z, ψ₀ z - α * z ∈ P''.lattice := by
  set L := P''.lattice with hL
  set p := P''.weierstrassP with hp
  set dp := P''.derivWeierstrassP with hdp
  have hLo : IsOpen ((L : Set ℂ)ᶜ) := isOpen_compl_lattice P''
  have hL'o : IsOpen ((P'.lattice : Set ℂ)ᶜ) := isOpen_compl_lattice P'
  have hmem : ∀ z, z ∉ P'.lattice → (P'.lattice : Set ℂ)ᶜ ∈ 𝓝 z := fun z hz => hL'o.mem_nhds hz
  -- step a: a point with `℘' ≠ 0`
  set a₀ := P''.ω₁ / 3 with ha₀
  have ha₀L : a₀ ∉ L := third_not_mem P''
  have hda₀ : dp a₀ ≠ 0 := by
    intro h0
    refine two_third_not_mem P'' (hinj a₀ (-a₀) ha₀L (neg_not_mem P'' ha₀L) ?_ ?_)
    · rw [hp, PeriodPair.weierstrassP_neg]
    · rw [hdp, PeriodPair.derivWeierstrassP_neg, ← hdp, h0, neg_zero]
  -- step b: `z₀` with `ψ₀ z₀ ≡ a₀`
  obtain ⟨z₀, hz₀⟩ := hsurj a₀
  set w₀ := ψ₀ z₀ with hw₀
  have hw₀L : w₀ ∉ L := fun h => ha₀L (by simpa using sub_mem h hz₀)
  have hz₀L : z₀ ∉ P'.lattice := fun h => hw₀L ((hker z₀).2 h)
  have hdw₀ : dp w₀ ≠ 0 := by
    have : w₀ = a₀ + ((⟨w₀ - a₀, hz₀⟩ : L) : ℂ) := by simp
    rw [this, hdp, PeriodPair.derivWeierstrassP_add_coe]; exact hda₀
  -- step c: the local inverse of `℘` at `w₀`
  have hdiffp : ∀ w ∉ L, HasStrictDerivAt p (dp w) w := by
    intro w hw
    have h := (P''.analyticOnNhd_weierstrassP w hw).hasStrictDerivAt
    rwa [PeriodPair.deriv_weierstrassP] at h
  have hs := hdiffp w₀ hw₀L
  set φ := (hs.hasStrictFDerivAt_equiv hdw₀).toOpenPartialHomeomorph p with hφ
  have hφc : ∀ w, φ w = p w := fun w => rfl
  have hw₀s : w₀ ∈ φ.source := (hs.hasStrictFDerivAt_equiv hdw₀).mem_toOpenPartialHomeomorph_source
  have hpw₀t : p w₀ ∈ φ.target := (hs.hasStrictFDerivAt_equiv hdw₀).image_mem_toOpenPartialHomeomorph_target
  set ψ : ℂ → ℂ := fun z => φ.symm (F z) with hψ
  have hFz₀ : F z₀ = p w₀ := ((hF z₀ hz₀L).1).symm
  have hGz₀ : G z₀ = dp w₀ := ((hF z₀ hz₀L).2).symm
  have hψz₀ : ψ z₀ = w₀ := by
    simp only [hψ, hFz₀]
    rw [← hφc w₀]; exact φ.left_inv hw₀s
  have hFc : ContinuousAt F z₀ := (hFd.differentiableAt (hmem z₀ hz₀L)).continuousAt
  have hψc : ContinuousAt ψ z₀ := by
    refine (φ.symm.continuousAt ?_).comp hFc
    rw [hFz₀]; exact hpw₀t
  -- the good set near `w₀`
  set Good : Set ℂ := {w | w ∉ L ∧ dp w ≠ 0} with hGood
  have hGoodo : IsOpen Good := by
    have hc : ContinuousOn dp ((L : Set ℂ)ᶜ) :=
      fun w hw => (P''.analyticOnNhd_derivWeierstrassP w hw).continuousAt.continuousWithinAt
    exact hc.isOpen_inter_preimage hLo isOpen_compl_singleton
  have hw₀G : w₀ ∈ Good := ⟨hw₀L, hdw₀⟩
  have hdpc : ContinuousAt dp w₀ := (P''.analyticOnNhd_derivWeierstrassP w₀ hw₀L).continuousAt
  have hGc0 : ContinuousAt G z₀ := hGc.continuousAt (hmem z₀ hz₀L)
  have hsum : ContinuousAt (fun z => dp (ψ z) + G z) z₀ := by
    refine ContinuousAt.add ?_ hGc0
    refine ContinuousAt.comp (g := dp) ?_ hψc
    rw [hψz₀]; exact hdpc
  have hsum0 : dp (ψ z₀) + G z₀ ≠ 0 := by
    rw [hψz₀, hGz₀, ← two_mul]; exact mul_ne_zero two_ne_zero hdw₀
  -- eventually near `z₀`
  have hev : ∀ᶠ z in 𝓝 z₀, z ∉ P'.lattice ∧ F z ∈ φ.target ∧ ψ z ∈ Good ∧
      dp (ψ z) + G z ≠ 0 := by
    have e1 : ∀ᶠ z in 𝓝 z₀, z ∉ P'.lattice := hmem z₀ hz₀L
    have e2 : ∀ᶠ z in 𝓝 z₀, F z ∈ φ.target :=
      hFc.preimage_mem_nhds (by rw [hFz₀]; exact φ.open_target.mem_nhds hpw₀t)
    have e3 : ∀ᶠ z in 𝓝 z₀, ψ z ∈ Good :=
      hψc.preimage_mem_nhds (by rw [hψz₀]; exact hGoodo.mem_nhds hw₀G)
    have e4 : ∀ᶠ z in 𝓝 z₀, dp (ψ z) + G z ≠ 0 :=
      hsum.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hsum0)
    exact e1.and (e2.and (e3.and e4))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- on the ball: `ψ₀ ≡ ψ`, `ψ` holomorphic
  have hkey : ∀ z ∈ ball z₀ r, ψ₀ z - ψ z ∈ L ∧ HasDerivAt ψ (deriv ψ z) z ∧ ContinuousAt ψ z := by
    intro z hz
    obtain ⟨hzL, hFt, ⟨hψL, hdψ⟩, hne⟩ := hball z hz
    have hpψ : p (ψ z) = F z := φ.right_inv hFt
    obtain ⟨h1, h2⟩ := hF z hzL
    have hψ₀L : ψ₀ z ∉ L := fun h => hzL ((hker z).1 h)
    have hsq1 := P''.derivWeierstrassP_sq (ψ z) hψL
    have hsq2 := P''.derivWeierstrassP_sq (ψ₀ z) hψ₀L
    have hsq : (dp (ψ z) - G z) * (dp (ψ z) + G z) = 0 := by
      have e1 : dp (ψ z) ^ 2 = 4 * F z ^ 3 - P''.g₂ * F z - P''.g₃ := by rw [← hpψ]; exact hsq1
      have e2 : G z ^ 2 = 4 * F z ^ 3 - P''.g₂ * F z - P''.g₃ := by rw [← h1, ← h2]; exact hsq2
      linear_combination e1 - e2
    have hdeq : dp (ψ z) = G z := sub_eq_zero.1 ((mul_eq_zero.1 hsq).resolve_right hne)
    refine ⟨hinj _ _ hψ₀L hψL (by rw [h1, hpψ]) (by rw [h2, hdeq]), ?_, ?_⟩
    · have hFd' : HasDerivAt F (deriv F z) z :=
        (hFd.differentiableAt (hmem z hzL)).hasDerivAt
      have hsy : HasDerivAt φ.symm (dp (ψ z))⁻¹ (F z) := by
        refine φ.hasDerivAt_symm hFt hdψ ?_
        exact (hdiffp _ hψL).hasDerivAt
      exact ((hsy.comp z hFd').differentiableAt).hasDerivAt
    · exact (φ.symm.continuousAt hFt).comp
        (hFd.differentiableAt (hmem z hzL)).continuousAt
  -- local increments agree: for `z₁` near `z₀`, `ψ (z₁ + u) - ψ z₁ = ψ (z₀ + u) - ψ z₀`
  have hr2 : (0 : ℝ) < r / 2 := half_pos hr
  have hinc : ∀ z₁ ∈ ball z₀ (r / 2), ∀ u ∈ ball (0 : ℂ) (r / 2),
      ψ (z₁ + u) - ψ z₁ - (ψ (z₀ + u) - ψ z₀) = 0 := by
    intro z₁ hz₁ u hu
    have mem : ∀ {z₂ v : ℂ}, z₂ ∈ ball z₀ (r / 2) → v ∈ ball (0 : ℂ) (r / 2) → z₂ + v ∈ ball z₀ r := by
      intro z₂ v h1 h2
      rw [mem_ball] at h1 h2 ⊢
      rw [dist_zero_right] at h2
      calc dist (z₂ + v) z₀ ≤ dist z₂ z₀ + ‖v‖ := by
            rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
        _ < r / 2 + r / 2 := add_lt_add h1 h2
        _ = r := by ring
    have hz₀b : z₀ ∈ ball z₀ (r / 2) := mem_ball_self hr2
    let D : ℂ → ℂ := fun v => ψ (z₁ + v) - ψ z₁ - (ψ (z₀ + v) - ψ z₀)
    have hDL : MapsTo D (ball (0 : ℂ) (r / 2)) (L : Set ℂ) := by
      intro v hv
      have e : D v = (ψ₀ (z₀ + v) - ψ (z₀ + v)) - (ψ₀ (z₁ + v) - ψ (z₁ + v)) + (ψ₀ z₁ - ψ z₁)
          - (ψ₀ z₀ - ψ z₀) + (ψ₀ (z₁ + v) - ψ₀ z₁ - ψ₀ v) - (ψ₀ (z₀ + v) - ψ₀ z₀ - ψ₀ v) := by
        simp only [D]; ring
      rw [SetLike.mem_coe, show D v = _ from e]
      refine sub_mem (add_mem (sub_mem (add_mem (sub_mem ?_ ?_) ?_) ?_) (hadd _ _)) (hadd _ _)
      · exact (hkey _ (mem hz₀b hv)).1
      · exact (hkey _ (mem hz₁ hv)).1
      · exact (hkey _ (by simpa using mem hz₁ (mem_ball_self hr2))).1
      · exact (hkey _ (by simpa using mem hz₀b (mem_ball_self hr2))).1
    have hDc : ContinuousOn D (ball (0 : ℂ) (r / 2)) := by
      intro v hv
      refine ContinuousAt.continuousWithinAt ?_
      have c1 : ContinuousAt (fun v => ψ (z₁ + v)) v :=
        ((hkey _ (mem hz₁ hv)).2.2).comp (continuous_const.add continuous_id).continuousAt
      have c2 : ContinuousAt (fun v => ψ (z₀ + v)) v :=
        ((hkey _ (mem hz₀b hv)).2.2).comp (continuous_const.add continuous_id).continuousAt
      exact (c1.sub continuousAt_const).sub (c2.sub continuousAt_const)
    have hdisc : IsDiscrete (L : Set ℂ) := by
      rw [isDiscrete_iff_discreteTopology]; exact inferInstanceAs (DiscreteTopology L)
    have := (convex_ball (0 : ℂ) (r / 2)).isPreconnected.constant_of_mapsTo hdisc hDc hDL hu
      (mem_ball_self hr2)
    simpa [D] using this
  -- derivatives agree
  have hderiv : ∀ z₁ ∈ ball z₀ (r / 2), deriv ψ z₁ = deriv ψ z₀ := by
    intro z₁ hz₁
    have hz₁r : z₁ ∈ ball z₀ r := ball_subset_ball (half_le_self hr.le) hz₁
    have hz₀r : z₀ ∈ ball z₀ r := mem_ball_self hr
    have h1 : HasDerivAt (fun u => ψ (z₁ + u)) (deriv ψ z₁) 0 := by
      have := (hkey z₁ hz₁r).2.1
      rw [← add_zero z₁] at this
      simpa using this.comp_const_add z₁ 0
    have h0 : HasDerivAt (fun u => ψ (z₀ + u) - ψ z₀ + ψ z₁) (deriv ψ z₀) 0 := by
      have := (hkey z₀ hz₀r).2.1
      rw [← add_zero z₀] at this
      have h' := this.comp_const_add z₀ 0
      simpa using (h'.sub_const (ψ z₀)).add_const (ψ z₁)
    have heq : (fun u => ψ (z₁ + u)) =ᶠ[𝓝 0] (fun u => ψ (z₀ + u) - ψ z₀ + ψ z₁) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hr2] with u hu
      have := hinc z₁ hz₁ u hu
      linear_combination this
    exact (h1.congr_of_eventuallyEq heq.symm).unique h0 |>.symm ▸ rfl
  -- `ψ` is affine near `z₀`
  set α := deriv ψ z₀ with hα
  have hdiffOn : DifferentiableOn ℂ ψ (ball z₀ (r / 2)) := fun z hz =>
    (hkey z (ball_subset_ball (half_le_self hr.le) hz)).2.1.differentiableAt.differentiableWithinAt
  obtain ⟨c, hc⟩ := (isOpen_ball (x := z₀) (ε := r / 2)).exists_eq_add_of_fderiv_eq
    (convex_ball _ _).isPreconnected hdiffOn
    ((differentiable_id.const_mul α).differentiableOn (s := ball z₀ (r / 2)))
    (fun z hz => by
      have h1 : HasDerivAt ψ α z := by
        rw [← hderiv z hz]
        exact (hkey z (ball_subset_ball (half_le_self hr.le) hz)).2.1
      rw [h1.hasFDerivAt.fderiv, ((hasDerivAt_id z).const_mul α).hasFDerivAt.fderiv]
      simp)
  -- small `u`: `ψ₀ u ≡ α u`
  have hsmall : ∀ u ∈ ball (0 : ℂ) (r / 2), ψ₀ u - α * u ∈ L := by
    intro u hu
    have hzu : z₀ + u ∈ ball z₀ (r / 2) := by
      rw [mem_ball, dist_eq_norm]; simpa using hu
    have e1 := hc hzu
    have e0 := hc (mem_ball_self hr2)
    simp only [id] at e1 e0
    have hψu : ψ (z₀ + u) - ψ z₀ = α * u := by rw [e1, e0]; ring
    have m1 := (hkey (z₀ + u) (ball_subset_ball (half_le_self hr.le) hzu)).1
    have m0 := (hkey z₀ (mem_ball_self hr)).1
    have e : ψ₀ u - α * u = (ψ₀ (z₀ + u) - ψ (z₀ + u)) - (ψ₀ z₀ - ψ z₀)
        - (ψ₀ (z₀ + u) - ψ₀ z₀ - ψ₀ u) := by rw [← hψu]; ring
    rw [e]
    exact sub_mem (sub_mem m1 m0) (hadd _ _)
  -- global
  have h0 : ψ₀ 0 ∈ L := (hker 0).2 (zero_mem _)
  refine ⟨α, fun z => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ / (r / 2))
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr2.le) hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set v := z / n with hv
  have hvb : v ∈ ball (0 : ℂ) (r / 2) := by
    rw [mem_ball, dist_zero_right, hv, norm_div, Complex.norm_natCast, div_lt_iff₀ hn0]
    rwa [div_lt_iff₀ hr2, mul_comm] at hn
  have hz : z = n * v := by rw [hv]; field_simp
  have e : ψ₀ z - α * z = (ψ₀ (n * v) - n * ψ₀ v) + n * (ψ₀ v - α * v) := by rw [hz]; ring
  rw [e]
  refine add_mem (psi_nsmul P'' ψ₀ h0 hadd n v) ?_
  have := hsmall v hvb
  rw [← nsmul_eq_mul]
  exact L.nsmul_mem this n

end Lin
end LinSec

/-! ## The textbook leaves -/

/-- `Λ ⊂ ℂ` as a lattice in `ℂ¹ = Fin 1 → ℂ`. -/
def lat1 (P : PeriodPair) : Submodule ℤ (Fin 1 → ℂ) :=
  P.lattice.comap (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 1 => ℂ) 0)

theorem mem_lat1 (P : PeriodPair) (v : Fin 1 → ℂ) : v ∈ lat1 P ↔ v 0 ∈ P.lattice := Iff.rfl

/-- **LEAF (textbook) `WeierstrassUniformization`.** For `a, b ∈ ℂ` with `a³ − 27b² ≠ 0` there is
a lattice `L` with `g₂(L) = a`, `g₃(L) = b`. J. Silverman, *The Arithmetic of Elliptic Curves*
(GTM 106, 2nd ed., 2009), Thm VI.5.1 (UNVERIFIED number); J.-P. Serre, *A Course in Arithmetic*,
Ch. VII §3 (UNVERIFIED). Verbatim copy of gz-weil's `GrossZagierHeegner.WeierstrassUniformization`
(origin/wip/gz-weil, `ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean`). -/
def WeierstrassUniformization : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b

/-- **LEAF (textbook) `WeierstrassParam`** (the Weierstrass parametrization). For every lattice
`Λ`: `Δ(Λ) = g₂³ − 27g₃² ≠ 0`, and `z ↦ (℘(z), ℘'(z))` is a surjective group homomorphism
`ℂ → E_Λ(ℂ)`, `E_Λ : y² = 4x³ − g₂x − g₃`, with kernel `Λ` (the points written in Mathlib's normal
form `y² = x³ − (g₂/4)x − g₃/4`, i.e. `(℘(z), ℘'(z)/2)`, with Mathlib's group law on
`WeierstrassCurve.Affine.Point`). J. Silverman, *The Arithmetic of Elliptic Curves* (GTM 106,
2nd ed.), Prop. VI.3.6 (a) (`Δ ≠ 0`) and (b) (`ℂ/Λ → E(ℂ)`, `z ↦ [℘(z), ℘'(z), 1]`, is a complex
analytic isomorphism of complex Lie groups); S. Lang, *Elliptic functions*, Ch. 1 §3; Serre,
*A Course in Arithmetic*, Ch. VII §3.2 (numbers UNVERIFIED). Weaker than the print (the analytic
clause is dropped). -/
def WeierstrassParam : Prop :=
  ∀ P : PeriodPair, T5Glue.discL P ≠ 0 ∧ ParamProps P (wc P.g₂ P.g₃)

/-- **LEAF (textbook) `WeierstrassAbVar`** (the curve `E_Λ` as an abelian variety, with its
Weierstrass coordinates). For every lattice `Λ` there is an abelian variety `A/ℂ` of dimension 1
(the project's `PkgI3.AbVar`), an analytic uniformization `θ : ℂ¹/Λ ≅ A(ℂ)`
(`ZInQ.LeafPush2.IsUniformization`), and regular functions `x, y` on a Zariski open `U ⊂ A` with
`θ(z) ∈ U ↔ z ∉ Λ` and `x(θ(z)) = ℘(z)`, `y(θ(z)) = ℘'(z)` there: `A = E_Λ` is the projective cubic
`y²z = 4x³ − g₂xz² − g₃z³` (an elliptic curve, Silverman III.3.1 and Prop. III.3.6 / Example
III.1.? for the group law), `U = E_Λ ∖ {O}` its affine part with coordinates `x, y`, and `θ` the map
`z ↦ [℘(z), ℘'(z), 1]` of Silverman, *The Arithmetic of Elliptic Curves*, Prop. VI.3.6 (b) (a
complex analytic isomorphism of complex Lie groups `ℂ/Λ ≅ E_Λ(ℂ)`); regular functions on opens of
`E_Λ` are rational functions in `x, y`, holomorphic along `θ` where defined. (Numbers UNVERIFIED.)
The abelian variety is existential because Mathlib v4.35.0 cannot construct a projective group
scheme (`PkgI3.AbVar.zero`'s docstring). -/
def WeierstrassAbVar : Prop :=
  ∀ P : PeriodPair, ∃ (A : PkgI3.AbVar ℂ) (θ : (Fin 1 → ℂ) → CPts A (RingHom.id ℂ))
    (U : A.X.left.Opens) (x y : Γ(A.X.left, U)),
    A.dim = ((1 : ℕ) : WithBot ℕ∞) ∧ IsUniformization (RingHom.id ℂ) (lat1 P) θ ∧
    ∀ z : Fin 1 → ℂ, (⊤ ≤ (θ z).left ⁻¹ᵁ U ↔ z 0 ∉ P.lattice) ∧
      (z 0 ∉ P.lattice → cEvalAt (θ z) U x = P.weierstrassP (z 0) ∧
        cEvalAt (θ z) U y = P.derivWeierstrassP (z 0))

/-! ## Helpers -/

section Helpers

theorem hom_sub {G : Type*} [Group G] {Φ : ℂ → G} (h : ∀ z w, Φ (z + w) = Φ z * Φ w) (a b : ℂ) :
    Φ (a - b) = Φ a * (Φ b)⁻¹ := by
  have := h (a - b) b
  rw [sub_add_cancel] at this
  rw [this, mul_inv_cancel_right]

theorem hom_eq_iff {G : Type*} [Group G] {Φ : ℂ → G} {L : Submodule ℤ ℂ} (h : ∀ z w, Φ (z + w) = Φ z * Φ w)
    (hk : ∀ z, Φ z = 1 ↔ z ∈ L) (a b : ℂ) : Φ a = Φ b ↔ a - b ∈ L := by
  rw [← hk, hom_sub h, mul_inv_eq_one]

theorem addHom_eq_iff {G : Type*} [AddGroup G] {Φ : ℂ → G} {L : Submodule ℤ ℂ}
    (h : ∀ z w, Φ (z + w) = Φ z + Φ w) (hk : ∀ z, Φ z = 0 ↔ z ∈ L) (a b : ℂ) :
    Φ a = Φ b ↔ a - b ∈ L := by
  have hs : Φ (a - b) = Φ a - Φ b := by
    have := h (a - b) b; rw [sub_add_cancel] at this; rw [this, add_sub_cancel_right]
  rw [← hk, hs, sub_eq_zero]

open Classical in
theorem wPtW_of_not_mem {P : PeriodPair} {W : WeierstrassCurve ℂ} (hP : ParamProps P W) {z : ℂ}
    (hz : z ∉ P.lattice) : ∃ h : W.toAffine.Nonsingular (P.weierstrassP z) (P.derivWeierstrassP z / 2),
      wPtW P W z = .some _ _ h := by
  have hne : wPtW P W z ≠ 0 := fun e => hz ((hP.2.1 z).1 e)
  unfold wPtW at hne ⊢
  by_cases hc : z ∉ P.lattice ∧ W.toAffine.Nonsingular (P.weierstrassP z) (P.derivWeierstrassP z / 2)
  · exact ⟨hc.2, by rw [dif_pos hc]⟩
  · rw [dif_neg hc] at hne; exact absurd rfl hne

open Classical in
theorem mapPt_surjective (W : WeierstrassCurve ℂ) (σ : ℂ ≃+* ℂ) :
    Function.Surjective (mapPt W (σ : ℂ →+* ℂ)) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · have h' : (W.map (σ : ℂ →+* ℂ)).toAffine.Nonsingular ((σ : ℂ →+* ℂ) (σ.symm x))
        ((σ : ℂ →+* ℂ) (σ.symm y)) := by
      simpa using h
    have h0 := (W.toAffine.map_nonsingular (σ : ℂ →+* ℂ).injective (σ.symm x) (σ.symm y)).mp h'
    refine ⟨.some _ _ h0, ?_⟩
    rw [mapPt_some]
    simp

end Helpers

/-! ## CORE: Weierstrass coordinates on `A^σ` -/

section CoreSec

open Classical

/-- **CORE (glue, proved).** Let `A` be the curve of `WeierstrassAbVar` for `Λ = Λ_P` (with `θ`,
`U`, `x`, `y`), `σ ∈ Aut(ℂ)`, and `θ'` an analytic uniformization of `A^σ = A ×_{ℂ,σ} ℂ` with
kernel `Λ_{P'}`. Then there is `μ ∈ ℂˣ` with `σ(g₂(P)) = μ⁴g₂(P')`, `σ(g₃(P)) = μ⁶g₃(P')`, and
whenever `θ'(z')` is the conjugate of `θ(z)` (`z ∉ Λ_P`): `σ(℘_P(z)) = μ²℘_{P'}(z')`,
`σ(℘'_P(z)) = μ³℘'_{P'}(z')`. -/
theorem core (hWP : WeierstrassParam) (hWU : WeierstrassUniformization) (σ : ℂ ≃+* ℂ)
    (P P' : PeriodPair) (A : PkgI3.AbVar ℂ) (θ : (Fin 1 → ℂ) → CPts A (RingHom.id ℂ))
    (U : A.X.left.Opens) (x y : Γ(A.X.left, U))
    (hθ : IsUniformization (RingHom.id ℂ) (lat1 P) θ)
    (hθU : ∀ z : Fin 1 → ℂ, (⊤ ≤ (θ z).left ⁻¹ᵁ U ↔ z 0 ∉ P.lattice) ∧
      (z 0 ∉ P.lattice → cEvalAt (θ z) U x = P.weierstrassP (z 0) ∧
        cEvalAt (θ z) U y = P.derivWeierstrassP (z 0)))
    (θ' : (Fin 1 → ℂ) → CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ))
    (hθ' : IsUniformization (RingHom.id ℂ) (lat1 P') θ') :
    ∃ ν : ℂ, T5Glue.IsConjModel (σ : ℂ →+* ℂ) P P' ν ∧
      ∀ z z' : ℂ, z ∉ P.lattice →
        pl (θ' (fun _ => z')) ≫ projC A (σ : ℂ →+* ℂ) = sp (σ : ℂ →+* ℂ) ≫ pl (θ (fun _ => z)) →
        σ (P.weierstrassP z) = ν ^ 2 * P'.weierstrassP z' ∧
        σ (P.derivWeierstrassP z) = ν ^ 3 * P'.derivWeierstrassP z' := by
  set h := projC A (σ : ℂ →+* ℂ) with hh
  set c : ℂ → (Fin 1 → ℂ) := fun z _ => z with hc
  have hc_add : ∀ z w, c (z + w) = c z + c w := fun _ _ => rfl
  have hc_surj : ∀ v : Fin 1 → ℂ, c (v 0) = v := fun v => funext fun i => by
    rw [Subsingleton.elim i 0]
  set Θ : ℂ → CPts A (RingHom.id ℂ) := fun z => θ (c z) with hΘ
  set Θ' : ℂ → CPts (bcC A (σ : ℂ →+* ℂ)) (RingHom.id ℂ) := fun z => θ' (c z) with hΘ'
  have hΘm : ∀ z w, Θ (z + w) = Θ z * Θ w := fun z w => by simp only [hΘ, hc_add]; exact hθ.1 _ _
  have hΘ'm : ∀ z w, Θ' (z + w) = Θ' z * Θ' w := fun z w => by
    simp only [hΘ', hc_add]; exact hθ'.1 _ _
  have hΘk : ∀ z, Θ z = 1 ↔ z ∈ P.lattice := fun z => hθ.2.1 (c z)
  have hΘ'k : ∀ z, Θ' z = 1 ↔ z ∈ P'.lattice := fun z => hθ'.2.1 (c z)
  have hΘs : ∀ q, ∃ z, Θ z = q := fun q => by
    obtain ⟨v, hv⟩ := hθ.2.2.1 q; exact ⟨v 0, by rw [hΘ]; simp only; rw [hc_surj]; exact hv⟩
  have hΘ's : ∀ q, ∃ z, Θ' z = q := fun q => by
    obtain ⟨v, hv⟩ := hθ'.2.2.1 q; exact ⟨v 0, by rw [hΘ']; simp only; rw [hc_surj]; exact hv⟩
  have hΘeq := hom_eq_iff hΘm hΘk
  -- the de-conjugated parameter `w`
  choose w hw using fun z => hΘs (dd σ A (Θ' z))
  have hw_add : ∀ z z', w (z + z') - (w z + w z') ∈ P.lattice := fun z z' => by
    rw [← hΘeq, hΘm, hw, hw, hw, hΘ'm, dd_mul]
  have hw_ker : ∀ z, w z ∈ P.lattice ↔ z ∈ P'.lattice := fun z => by
    rw [← hΘk, hw, ← hΘ'k, ← dd_one σ A]
    exact (dd_injective σ A).eq_iff
  have hw_surj : ∀ a, ∃ z, w z - a ∈ P.lattice := fun a => by
    obtain ⟨p, hp⟩ := dd_surjective σ A (Θ a)
    obtain ⟨z, hz⟩ := hΘ's p
    exact ⟨z, by rw [← hΘeq, hw, hz, hp]⟩
  have hw_rel : ∀ z, pl (Θ' z) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (Θ (w z)) := fun z => by
    rw [hw]; exact dd_key σ A _
  -- coordinates on `A^σ`
  set F : ℂ → ℂ := fun z => evS (pl (Θ' z)) (h ⁻¹ᵁ U) (h.app U x) with hF
  set G : ℂ → ℂ := fun z => evS (pl (Θ' z)) (h ⁻¹ᵁ U) (h.app U y) with hG
  have hwmem : ∀ z, z ∉ P'.lattice → ⊤ ≤ pl (Θ (w z)) ⁻¹ᵁ U := fun z hz =>
    ((hθU (c (w z))).1).2 (fun hm => hz ((hw_ker z).1 hm))
  have hFval : ∀ z, z ∉ P'.lattice →
      F z = σ (P.weierstrassP (w z)) ∧ G z = σ (P.derivWeierstrassP (w z)) := fun z hz => by
    have hv := (hθU (c (w z))).2 (fun hm => hz ((hw_ker z).1 hm))
    refine ⟨?_, ?_⟩
    · rw [hF]; simp only
      rw [(eval_conj σ h (hw_rel z) U x).2 (hwmem z hz)]
      rw [← cEvalAt_eq, hv.1]
    · rw [hG]; simp only
      rw [(eval_conj σ h (hw_rel z) U y).2 (hwmem z hz)]
      rw [← cEvalAt_eq, hv.2]
  have hdom : Set.MapsTo c ((P'.lattice : Set ℂ)ᶜ) (cDom θ' (h ⁻¹ᵁ U)) := fun z hz =>
    ((eval_conj σ h (hw_rel z) U x).1).2 (hwmem z hz)
  have hcd : DifferentiableOn ℂ c ((P'.lattice : Set ℂ)ᶜ) :=
    (differentiable_pi.2 fun _ => differentiable_id).differentiableOn
  have hFd : DifferentiableOn ℂ F ((P'.lattice : Set ℂ)ᶜ) :=
    (hθ'.2.2.2.2 (h ⁻¹ᵁ U) (h.app U x)).comp hcd hdom
  have hGc : ContinuousOn G ((P'.lattice : Set ℂ)ᶜ) :=
    ((hθ'.2.2.2.2 (h ⁻¹ᵁ U) (h.app U y)).comp hcd hdom).continuousOn
  -- the auxiliary lattice `Λ''` of `E_P^σ`
  obtain ⟨hΔ, hpar⟩ := hWP P
  have hΔσ : σ P.g₂ ^ 3 - 27 * σ P.g₃ ^ 2 ≠ 0 := by
    have := (map_ne_zero (σ : ℂ →+* ℂ)).2 hΔ
    simpa [T5Glue.discL, map_sub, map_mul, map_pow, map_ofNat] using this
  obtain ⟨P'', h2, h3⟩ := hWU _ _ hΔσ
  set W'' := (wc P.g₂ P.g₃).map (σ : ℂ →+* ℂ) with hW''
  have hW : W'' = wc P''.g₂ P''.g₃ := by rw [hW'', map_wc, h2, h3]; rfl
  have hpar'' : ParamProps P'' W'' := by rw [hW]; exact (hWP P'').2
  set PP : ℂ → W''.toAffine.Point := fun z => mapPt (wc P.g₂ P.g₃) (σ : ℂ →+* ℂ) (wPt P (w z)) with hPP
  choose ψ₀ hψ₀ using fun z => hpar''.2.2 (PP z)
  have hPeq := addHom_eq_iff hpar.1 hpar.2.1
  have hP''eq := addHom_eq_iff hpar''.1 hpar''.2.1
  -- the hypotheses of LIN
  have l_inj : ∀ a b, a ∉ P''.lattice → b ∉ P''.lattice →
      P''.weierstrassP a = P''.weierstrassP b →
      P''.derivWeierstrassP a = P''.derivWeierstrassP b → a - b ∈ P''.lattice := by
    intro a b ha hb e1 e2
    rw [← hP''eq]
    obtain ⟨ha', hA⟩ := wPtW_of_not_mem hpar'' ha
    obtain ⟨hb', hB⟩ := wPtW_of_not_mem hpar'' hb
    rw [hA, hB]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨e1, by rw [e2]⟩
  have l_add : ∀ z z', ψ₀ (z + z') - ψ₀ z - ψ₀ z' ∈ P''.lattice := by
    intro z z'
    rw [sub_sub, ← hP''eq, hpar''.1, hψ₀, hψ₀, hψ₀, hPP]
    simp only
    rw [← map_add]
    congr 1
    show wPtW P _ _ = wPtW P _ _ + wPtW P _ _
    rw [← hpar.1]
    exact (hPeq _ _).2 (hw_add z z')
  have l_ker : ∀ z, ψ₀ z ∈ P''.lattice ↔ z ∈ P'.lattice := by
    intro z
    rw [← hpar''.2.1, hψ₀, hPP]
    simp only
    rw [← hw_ker, ← hpar.2.1, ← map_zero (mapPt (wc P.g₂ P.g₃) (σ : ℂ →+* ℂ))]
    exact (mapPt_injective _ _).eq_iff
  have l_surj : ∀ a, ∃ z, ψ₀ z - a ∈ P''.lattice := by
    intro a
    obtain ⟨Q, hQ⟩ := mapPt_surjective (wc P.g₂ P.g₃) σ (wPtW P'' W'' a)
    obtain ⟨b, hb⟩ := hpar.2.2 Q
    obtain ⟨z, hz⟩ := hw_surj b
    refine ⟨z, ?_⟩
    rw [← hP''eq, hψ₀, ← hQ, ← hb, hPP]
    simp only
    congr 1
    exact (hPeq _ _).2 hz
  have l_F : ∀ z, z ∉ P'.lattice →
      P''.weierstrassP (ψ₀ z) = F z ∧ P''.derivWeierstrassP (ψ₀ z) = G z := by
    intro z hz
    have hwz : w z ∉ P.lattice := fun hm => hz ((hw_ker z).1 hm)
    have hψz : ψ₀ z ∉ P''.lattice := fun hm => hz ((l_ker z).1 hm)
    obtain ⟨h1, e1⟩ := wPtW_of_not_mem hpar hwz
    obtain ⟨h2', e2⟩ := wPtW_of_not_mem hpar'' hψz
    have := hψ₀ z
    rw [e2, hPP] at this
    simp only [wPt] at this
    rw [e1, mapPt_some] at this
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at this
    obtain ⟨a1, a2⟩ := this
    simp only [RingEquiv.coe_toRingHom] at a1 a2
    rw [(hFval z hz).1, (hFval z hz).2, a1]
    refine ⟨rfl, ?_⟩
    rw [map_div₀, map_ofNat] at a2
    linear_combination 2 * a2
  -- LIN
  obtain ⟨α, hα⟩ := lin P' P'' ψ₀ F G l_inj l_add l_ker l_surj l_F hFd hGc
  have hα_iff : ∀ z, α * z ∈ P''.lattice ↔ z ∈ P'.lattice := fun z => by
    rw [← l_ker]
    constructor
    · intro hm; simpa using add_mem (hα z) hm
    · intro hm; simpa using sub_mem hm (hα z)
  have hα0 : α ≠ 0 := by
    intro h0
    have := (hα_iff (P'.ω₁ / 2)).1 (by rw [h0, zero_mul]; exact zero_mem _)
    exact P'.ω₁_div_two_notMem_lattice this
  have hscale : T5Glue.IsScale P'' P' α := by
    refine ⟨hα0, ?_⟩
    ext t
    simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
    constructor
    · intro ht
      refine ⟨t / α, ?_, by field_simp⟩
      rw [← hα_iff]; field_simp; exact ht
    · rintro ⟨u, hu, rfl⟩
      exact (hα_iff u).2 hu
  refine ⟨α⁻¹, ⟨inv_ne_zero hα0, ?_, ?_⟩, ?_⟩
  · show σ P.g₂ = α⁻¹ ^ 4 * P'.g₂
    rw [← h2, hscale.g₂, inv_pow]
  · show σ P.g₃ = α⁻¹ ^ 6 * P'.g₃
    rw [← h3, hscale.g₃, inv_pow]
  · intro z z' hz hrel
    have hD' : dd σ A (Θ' z') = Θ z := dd_unique σ A hrel
    have hzz : w z' - z ∈ P.lattice := by rw [← hΘeq, hw]; exact hD'
    have hz' : z' ∉ P'.lattice := by
      intro hm
      have h1 : Θ' z' = 1 := (hΘ'k z').2 hm
      rw [h1, dd_one] at hD'
      exact hz ((hΘk z).1 hD'.symm)
    have hper : P.weierstrassP (w z') = P.weierstrassP z ∧
        P.derivWeierstrassP (w z') = P.derivWeierstrassP z := by
      have e : w z' = z + ((⟨w z' - z, hzz⟩ : P.lattice) : ℂ) := by simp
      rw [e, PeriodPair.weierstrassP_add_coe, PeriodPair.derivWeierstrassP_add_coe]
      exact ⟨rfl, rfl⟩
    have hper'' : P''.weierstrassP (ψ₀ z') = P''.weierstrassP (α * z') ∧
        P''.derivWeierstrassP (ψ₀ z') = P''.derivWeierstrassP (α * z') := by
      have e : ψ₀ z' = α * z' + ((⟨ψ₀ z' - α * z', hα z'⟩ : P''.lattice) : ℂ) := by simp
      rw [e, PeriodPair.weierstrassP_add_coe, PeriodPair.derivWeierstrassP_add_coe]
      exact ⟨rfl, rfl⟩
    obtain ⟨f1, f2⟩ := l_F z' hz'
    obtain ⟨v1, v2⟩ := hFval z' hz'
    refine ⟨?_, ?_⟩
    · rw [← hper.1, ← v1, ← f1, hper''.1, hscale.weierstrassP, inv_pow]
    · rw [← hper.2, ← v2, ← f2, hper''.2, hscale.derivWeierstrassP, inv_pow]

end CoreSec

/-! ## The printed main theorem of CM with Shimura's normalization -/

section MainCM

open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped TensorProduct

/-- The body of `QMRecPrinted.MainTheoremCM` at a fixed sign `ε` (verbatim; `mainTheoremCM_iff`). -/
def MainTheoremCMSign (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- `MainTheoremCM` is exactly `∃ ε, MainTheoremCMSign ε` (checks the verbatim copy). -/
theorem mainTheoremCM_iff : QMRecPrinted.MainTheoremCM ↔ ∃ ε, MainTheoremCMSign ε := Iff.rfl

/-- **LEAF `MainTheoremCMArith` (the main theorem of complex multiplication, adelic form with torsion, in
Shimura's normalization; printed form).** `QMRecPrinted.MainTheoremCM` with the sign `ε = 1`: for `σ = [s, E*]`
(Tau Ceti's Artin map, which sends a uniformizer at `𝔭` to the arithmetic Frobenius), `A^σ` is uniformized by
`ℂ^g/Φ(N(s)⁻¹𝔞)` with `θ(Φ(x))^σ = θ'(Φ(y))` whenever `N(s)y − x ∈ 𝔞̂`.

*Published statement*: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971),
Thm 5.15 (abelian varieties) and Thm 5.4 (elliptic curves): `ξ(u)^σ = ξ'(N_{Φ*}(s)⁻¹u)` with `σ = [s, K]`, where
`[s, K]` is the Artin symbol of the classical (arithmetic) reciprocity law (§5.2); Shimura, *Abelian varieties with
complex multiplication and modular functions* (1998), Thm 18.6; Lang, *Elliptic functions*, Ch. 10 Thm 3; Silverman,
*Advanced topics*, Thm II.8.2 (`𝒪_K`; numbers UNVERIFIED). In the arithmetic normalization the lattice of `A^σ` is
`N(s)⁻¹𝔞` (for `E` imaginary quadratic: `j(𝔞)^{(𝔭, H/K)} = j(𝔭⁻¹𝔞)`, Silverman, *Advanced topics*, Thm II.4.3:
`F(𝔞)·j(E) = j(𝔞 * E)` with `𝔞 * E_Λ = E_{𝔞⁻¹Λ}`; UNVERIFIED number), i.e. `ε = 1`. qmrec-printed's `MainTheoremCM`
leaves `ε` existential; that form cannot decide the direction of `T5Glue.ShimuraMainCM`. It is implied by this leaf
(`mainTheoremCM_of_arith`). -/
def MainTheoremCMArith : Prop := MainTheoremCMSign 1

theorem mainTheoremCM_of_arith (h : MainTheoremCMArith) : QMRecPrinted.MainTheoremCM := ⟨1, h⟩

end MainCM

/-! ## Specialization to `K = ℚ(√−m)`, `g = 1` -/

section CMSpec

open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM
open scoped TensorProduct FiniteAdeleExtension

variable {m : ℕ} [NeZero m]

/-- `κ : ℚ(√−m) → ℂ` as a ring homomorphism. -/
abbrev kap (m : ℕ) : QNeg m →+* ℂ := (kappaAlg m).toRingHom

theorem kap_apply (x : QNeg m) : kap m x = kappa m x := kappaAlg_apply m x

/-! ### The Artin condition -/

set_option maxRecDepth 4000 in
open scoped IsMulCommutative in
/-- **`ArtinCond` (through `ιC ∘ e` on subfields of `Kˢ`) gives `ArtinCondC` (every abelian `L/K` with a
`K`-embedding into `ℂ`).** -/
theorem artinCondC_of_artinCond (e : SeparableClosure (QNeg m) →ₐ[ℚ] ZInQ.Contrib.TYZDecomp.CurveA.Qbar)
    (he : ZInQ.Contrib.TYZGenus.CM.ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ))
    (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (hs : T5Glue.ArtinCond m e σ s) :
    ArtinCondC (kap m) σ s := by
  intro L _ _ _ _ j hj x
  let ε : SeparableClosure (QNeg m) →+* ℂ := ZInQ.Contrib.TYZGenus.CM.ιC.comp e.toRingHom
  have hε : ε.comp (algebraMap (QNeg m) (SeparableClosure (QNeg m))) = kap m := by
    ext k; exact (T5Glue.kappa_eq_of_normalized e he k).trans (kap_apply k).symm
  obtain ⟨iota, hι⟩ := exists_iota (kap m) ε hε L j hj
  obtain ⟨τ, hτ⟩ : ∃ τ : TauCeti.AbsoluteGaloisGroup (QNeg m),
      Additive.ofMul (τ : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup (QNeg m))) =
        (globalClassFormation (QNeg m)).absoluteArtinMap
          (globalGroundEquiv (QNeg m) (Additive.ofMul (QuotientGroup.mk s))) := by
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (Additive.toMul
      ((globalClassFormation (QNeg m)).absoluteArtinMap
        (globalGroundEquiv (QNeg m) (Additive.ofMul (QuotientGroup.mk s)))))
    exact ⟨τ, by rw [hτ]; rfl⟩
  have artin : ∀ (F : Type) [Field F] [NumberField F] [Algebra (QNeg m) F]
      [IsAbelianGalois (QNeg m) F] (ιF : F →ₐ[QNeg m] SeparableClosure (QNeg m)),
      ideleClassArtinMap (QNeg m) F (QuotientGroup.mk s) = ιF.restrictNormalHom τ := by
    intro F _ _ _ _ ιF
    have h1 := of_ideleClassArtinMap (QNeg m) F ιF (QuotientGroup.mk s)
    have h0 := globalArtinMap_eq_of_mk_eq_absoluteArtinMap (QNeg m) F ιF τ hτ
    have h3 : Abelianization.of (ideleClassArtinMap (QNeg m) F (QuotientGroup.mk s)) =
        Abelianization.of (ιF.restrictNormalHom τ) := by
      rw [h1, h0, toMul_ofMul]
    exact (Abelianization.equivOfComm (H := Gal(F/QNeg m))).injective h3
  let φ := AlgEquiv.ofInjectiveField iota
  haveI : FiniteDimensional (QNeg m) iota.fieldRange := LinearEquiv.finiteDimensional φ.toLinearEquiv
  haveI : NumberField iota.fieldRange :=
    { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans (QNeg m) _ }
  haveI : IsAbelianGalois (QNeg m) iota.fieldRange := IsAbelianGalois.of_algHom φ.symm.toAlgHom
  have hF := hs iota.fieldRange ⟨iota x, x, rfl⟩
  unfold T5Glue.icl at hF
  have h4 := iota.fieldRange.val.restrictNormalHom_commutes τ ⟨iota x, x, rfl⟩
  have key : ((ideleClassArtinMap (QNeg m) iota.fieldRange (QuotientGroup.mk s) ⟨iota x, x, rfl⟩ :
      iota.fieldRange) : SeparableClosure (QNeg m)) = τ (iota x) := by
    have hA := artin iota.fieldRange iota.fieldRange.val
    simp only [hA]
    exact h4
  rw [key] at hF
  rw [← hι x, ← hι, artin L iota, AlgHom.restrictNormalHom_commutes]
  exact hF

/-! ### The CM type `(K, κ)` -/

instance isTotallyComplex_QNeg : IsTotallyComplex (QNeg m) :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 (T5Glue.not_isReal_QNeg m w)⟩

theorem finrank_QNeg : Module.finrank ℚ (QNeg m) = 2 := QuadraticAlgebra.finrank_eq_two _ _

instance isCMField_QNeg : IsCMField (QNeg m) := by
  haveI : Algebra.IsQuadraticExtension ℚ (QNeg m) := ⟨finrank_QNeg⟩
  exact IsCMField.ofCMExtension ℚ (QNeg m)

theorem kap_omega : kap m QuadraticAlgebra.omega = I * (Real.sqrt m : ℂ) := by
  rw [kap_apply, T5Glue.kappa_omega]

theorem type_inj :
    Function.Injective (Sum.elim (fun _ : Fin 1 => kap m) fun i => (starRingEnd ℂ).comp
      ((fun _ : Fin 1 => kap m) i)) := by
  have hne : kap m ≠ (starRingEnd ℂ).comp (kap m) := by
    intro h
    have h1 := congrArg (fun ψ : QNeg m →+* ℂ => ψ QuadraticAlgebra.omega) h
    simp only [RingHom.coe_comp, Function.comp_apply, kap_omega] at h1
    have hm : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))
    have h2 := congrArg Complex.im h1
    simp at h2
    linarith
  rintro (i | i) (j | j) h
  · rw [Subsingleton.elim i j]
  · exact absurd h hne
  · exact absurd h.symm hne
  · rw [Subsingleton.elim i j]

theorem reflex_range : (kap m).fieldRange =
    Subfield.closure (Set.range fun e : QNeg m => ∑ i : Fin 1, (fun _ : Fin 1 => kap m) i e) := by
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  rw [← RingHom.coe_fieldRange, Subfield.closure_eq]

/-- `ρ(a)` = multiplication by `a` on `V = K`. -/
def rhoQ : QNeg m →ₐ[ℚ] Matrix (Fin 1) (Fin 1) (QNeg m) :=
  (Algebra.ofId (QNeg m) (Matrix (Fin 1) (Fin 1) (QNeg m))).restrictScalars ℚ

/-- `j(v) = κ(v₀)`. -/
def jQ : (Fin 1 → QNeg m) →+ (Fin 1 → ℂ) :=
  (cmVec (fun _ : Fin 1 => kap m)).comp (Pi.evalAddMonoidHom (fun _ => QNeg m) 0)

theorem jQ_apply (v : Fin 1 → QNeg m) (i : Fin 1) : jQ v i = kap m (v 0) := rfl

theorem rhoQ_mulVec (a : QNeg m) (v : Fin 1 → QNeg m) :
    (rhoQ a).mulVec v = fun i => a * v i := by
  funext i
  simp [rhoQ, Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem model : IsReflexModel (fun _ : Fin 1 => kap m) (kap m) rhoQ jQ := by
  refine ⟨fun e v => ?_, fun a v => ?_, ?_, rfl⟩
  · funext i; simp [jQ_apply, map_mul]
  · funext i; simp [jQ_apply, rhoQ_mulVec, map_mul]
  · rw [eq_top_iff]
    intro w _
    have hw : w = (w 0) • jQ (fun _ => (1 : QNeg m)) := by
      funext i; rw [Subsingleton.elim i 0]; simp [jQ_apply]
    rw [hw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- `𝔸_f ⊗ K ≅ 𝔸_{K,f}` (Tau Ceti). -/
abbrev eK (m : ℕ) [NeZero m] := finiteAdeleBaseChangeAlgEquiv ℚ (QNeg m)

theorem rhoA_rhoQ (w : AQ ⊗[ℚ] QNeg m) : rhoA rhoQ w 0 0 = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a k =>
    rw [rhoA, AlgHom.liftEquiv_tmul]
    simp [rhoQ, Matrix.algebraMap_eq_diagonal, Algebra.TensorProduct.includeRight_apply,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, Matrix.add_apply, hx, hy]

/-- **The reflex norm of `(K, κ)` is `𝔸_{K,f} ≅ 𝔸_f ⊗ K`.** -/
theorem reflexNorm_rhoQ (u : (FiniteAdeleRing (𝓞 (QNeg m)) (QNeg m))ˣ) :
    (reflexNorm rhoQ u : AQ ⊗[ℚ] QNeg m) = (eK m).symm u := by
  simp only [reflexNorm, Units.coe_map, MonoidHom.coe_comp, Function.comp_apply,
    Matrix.coe_detMonoidHom, Matrix.det_unique]
  exact rhoA_rhoQ _

end CMSpec

/-! ### The adelic dictionary: `𝔞̂ ⊂ 𝔸_{K,f}` and `𝔞 ⊗ ℤ̂ ⊂ 𝔸_f ⊗ K` -/

section Adelic

open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM
open scoped TensorProduct FiniteAdeleExtension

variable {m : ℕ} [NeZero m]

theorem eK_tmul (c : AQ) (k : QNeg m) :
    eK m (c ⊗ₜ k) = algebraMap AQ (T5Glue.AfK m) c * algebraMap (QNeg m) (T5Glue.AfK m) k := by
  have h1 : c ⊗ₜ[ℚ] k = c • ((1 : AQ) ⊗ₜ[ℚ] k) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have h2 : eK m ((1 : AQ) ⊗ₜ[ℚ] k) = algebraMap (QNeg m) (T5Glue.AfK m) k := by
    rw [← finiteAdeleBaseChangeAlgEquiv_symm_algebraMap, AlgEquiv.apply_symm_apply]
  rw [h1, map_smul, h2, Algebra.smul_def]

theorem continuous_algQ : Continuous (algebraMap AQ (T5Glue.AfK m)) := by
  rw [IsDedekindDomain.algebraMap_finiteAdeleExtensionAlgebra]
  exact IsDedekindDomain.continuous_finiteAdeleExtension _ _ _ _

theorem zhat_eq : ZhatQ = (FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ : Set AQ) := rfl

theorem int_of_ringOfIntegers (r : 𝓞 ℚ) : ∃ n : ℤ, r = (n : 𝓞 ℚ) :=
  ⟨Rat.ringOfIntegersEquiv r, by
    conv_lhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply r]
    exact map_intCast _ _⟩

/-- **The adelic dictionary.** For `𝔞 = ℤb₁ + ℤb₂ ⊂ K` (and `S` the same set as an additive subgroup),
`w ∈ 𝔞 ⊗ ℤ̂` (qmrec-printed's `latHat`) iff its image in `𝔸_{K,f}` lies in the closure `𝔞̂` of `𝔞`
(t5-glue's `latHat`). -/
theorem adelic (𝔞 : Set (QNeg m)) (S : AddSubgroup (QNeg m)) (hS : (S : Set (QNeg m)) = 𝔞)
    (b₁ b₂ : QNeg m) (hb : ∀ x, x ∈ 𝔞 ↔ ∃ n₁ n₂ : ℤ, x = n₁ * b₁ + n₂ * b₂) (w : AQ ⊗[ℚ] QNeg m) :
    w ∈ QMRecPrinted.latHat S ↔ eK m w ∈ T5Glue.latHat m 𝔞 := by
  set alg := algebraMap AQ (T5Glue.AfK m) with halg
  set algK := algebraMap (QNeg m) (T5Glue.AfK m) with halgK
  set Φ : AQ → AQ → T5Glue.AfK m := fun c₁ c₂ => alg c₁ * algK b₁ + alg c₂ * algK b₂ with hΦ
  have hΦc : Continuous (Function.uncurry Φ) := by
    refine ((continuous_algQ.comp continuous_fst).mul continuous_const).add
      ((continuous_algQ.comp continuous_snd).mul continuous_const)
  have hb₁ : b₁ ∈ S := by rw [← SetLike.mem_coe, hS, hb]; exact ⟨1, 0, by simp⟩
  have hb₂ : b₂ ∈ S := by rw [← SetLike.mem_coe, hS, hb]; exact ⟨0, 1, by simp⟩
  have hint : ∀ n : ℤ, (n : AQ) ∈ ZhatQ := fun n => intCast_mem ZhatS n
  have hΦint : ∀ n₁ n₂ : ℤ, Φ n₁ n₂ = algK (n₁ * b₁ + n₂ * b₂) := by
    intro n₁ n₂; simp [hΦ, halg, halgK, map_add, map_mul, map_intCast]
  have heK : ∀ c₁ c₂ : AQ, eK m (c₁ ⊗ₜ b₁ + c₂ ⊗ₜ b₂) = Φ c₁ c₂ := by
    intro c₁ c₂; rw [map_add, eK_tmul, eK_tmul]
  -- claim A: `latHat S = {c₁ ⊗ b₁ + c₂ ⊗ b₂}`
  have hA : ∀ w : AQ ⊗[ℚ] QNeg m, w ∈ QMRecPrinted.latHat S ↔
      ∃ c₁ ∈ ZhatQ, ∃ c₂ ∈ ZhatQ, w = c₁ ⊗ₜ b₁ + c₂ ⊗ₜ b₂ := by
    intro w
    constructor
    · intro hw
      induction hw using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨c, hc, y, hy, rfl⟩ := hx
        rw [← SetLike.mem_coe, hS, hb] at hy
        obtain ⟨n₁, n₂, rfl⟩ := hy
        refine ⟨n₁ • c, ZhatS.zsmul_mem hc n₁, n₂ • c, ZhatS.zsmul_mem hc n₂, ?_⟩
        rw [TensorProduct.tmul_add, ← zsmul_eq_mul, ← zsmul_eq_mul, TensorProduct.tmul_smul,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      | zero => exact ⟨0, ZhatS.zero_mem, 0, ZhatS.zero_mem, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨c₁, h₁, c₂, h₂, rfl⟩ := hx
        obtain ⟨d₁, k₁, d₂, k₂, rfl⟩ := hy
        refine ⟨c₁ + d₁, ZhatS.add_mem h₁ k₁, c₂ + d₂, ZhatS.add_mem h₂ k₂, ?_⟩
        rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel
      | neg x _ hx =>
        obtain ⟨c₁, h₁, c₂, h₂, rfl⟩ := hx
        refine ⟨-c₁, ZhatS.neg_mem h₁, -c₂, ZhatS.neg_mem h₂, ?_⟩
        rw [TensorProduct.neg_tmul, TensorProduct.neg_tmul, neg_add]
    · rintro ⟨c₁, h₁, c₂, h₂, rfl⟩
      exact add_mem (AddSubgroup.subset_closure ⟨c₁, h₁, b₁, hb₁, rfl⟩)
        (AddSubgroup.subset_closure ⟨c₂, h₂, b₂, hb₂, rfl⟩)
  -- claim B: `𝔞̂ = Φ(ℤ̂ × ℤ̂)`
  have hB : ∀ y : T5Glue.AfK m, y ∈ T5Glue.latHat m 𝔞 ↔ ∃ c₁ ∈ ZhatQ, ∃ c₂ ∈ ZhatQ, y = Φ c₁ c₂ := by
    intro y
    have hcomp : IsCompact (Function.uncurry Φ '' (ZhatQ ×ˢ ZhatQ)) := by
      rw [zhat_eq]
      exact ((FiniteAdeleRing.isCompact_integralAdeles).prod
        (FiniteAdeleRing.isCompact_integralAdeles)).image hΦc
    constructor
    · intro hy
      have hsub : algebraMap (QNeg m) (T5Glue.AfK m) '' 𝔞 ⊆ Function.uncurry Φ '' (ZhatQ ×ˢ ZhatQ) := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨n₁, n₂, rfl⟩ := (hb x).1 hx
        exact ⟨((n₁ : AQ), (n₂ : AQ)), ⟨hint n₁, hint n₂⟩, by simp only [Function.uncurry_apply_pair]; rw [hΦint]⟩
      obtain ⟨⟨c₁, c₂⟩, ⟨h₁, h₂⟩, rfl⟩ := closure_minimal hsub hcomp.isClosed hy
      exact ⟨c₁, h₁, c₂, h₂, rfl⟩
    · rintro ⟨c₁, h₁, c₂, h₂, rfl⟩
      have hcl : ZhatQ = closure (Set.range (algebraMap (𝓞 ℚ) AQ)) := by
        rw [zhat_eq]; exact (FiniteAdeleRing.closure_range_algebraMap (𝓞 ℚ) ℚ).symm
      rw [hcl] at h₁ h₂
      refine map_mem_closure₂ hΦc h₁ h₂ ?_
      rintro _ ⟨r₁, rfl⟩ _ ⟨r₂, rfl⟩
      obtain ⟨n₁, rfl⟩ := int_of_ringOfIntegers r₁
      obtain ⟨n₂, rfl⟩ := int_of_ringOfIntegers r₂
      refine ⟨n₁ * b₁ + n₂ * b₂, (hb _).2 ⟨n₁, n₂, rfl⟩, ?_⟩
      rw [map_intCast, map_intCast, hΦint]
  rw [hA, hB]
  constructor
  · rintro ⟨c₁, h₁, c₂, h₂, rfl⟩; exact ⟨c₁, h₁, c₂, h₂, heK c₁ c₂⟩
  · rintro ⟨c₁, h₁, c₂, h₂, he⟩
    exact ⟨c₁, h₁, c₂, h₂, (eK m).injective (by rw [he, heK])⟩

end Adelic

/-! ### Lattices, CM endomorphisms, and the final theorem -/

section Final

open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM
open scoped TensorProduct FiniteAdeleExtension

variable {m : ℕ} [NeZero m]

theorem cmLat_eq (S : AddSubgroup (QNeg m)) (Q : PeriodPair)
    (h : (Q.lattice : Set ℂ) = kappa m '' (S : Set (QNeg m))) :
    cmLat (fun _ : Fin 1 => kap m) S = lat1 Q := by
  ext v
  rw [mem_lat1]
  change v ∈ S.map (cmVec (fun _ : Fin 1 => kap m)) ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change kap m x ∈ Q.lattice
    rw [← SetLike.mem_coe, h]
    exact ⟨x, hx, (kap_apply x).symm⟩
  · intro hv
    rw [← SetLike.mem_coe, h] at hv
    obtain ⟨x, hx, hxv⟩ := hv
    refine ⟨x, hx, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0]
    change kap m x = v 0
    rw [kap_apply, hxv]

/-- **The CM endomorphisms** (from the textbook leaf `HomLatticeCorr`, realization half): multiplication by
`κ(e)` on `ℂ/κ(𝔞)` (`e𝔞 ⊆ 𝔞`) is induced by an endomorphism of `A`. -/
theorem isOfType_of_corr (hH : ZInQ.HomUnify.HomLatticeCorr) (A : PkgI3.AbVar ℂ)
    (hdim : A.dim = ((1 : ℕ) : WithBot ℕ∞)) (θ : (Fin 1 → ℂ) → CPts A (RingHom.id ℂ)) (P : PeriodPair)
    (hθ : IsUniformization (RingHom.id ℂ) (lat1 P) θ) (S : AddSubgroup (QNeg m))
    (h : (P.lattice : Set ℂ) = kappa m '' (S : Set (QNeg m))) :
    IsOfType (fun _ : Fin 1 => kap m) S θ := by
  intro e he
  let M : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := (kap m e) • LinearMap.id
  have hM : ∀ z ∈ lat1 P, M z ∈ lat1 P := by
    intro z hz
    rw [mem_lat1] at hz ⊢
    rw [← SetLike.mem_coe, h] at hz ⊢
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨e * x, he x hx, ?_⟩
    change kappa m (e * x) = kap m e * z 0
    rw [← kap_apply, map_mul, kap_apply x, hxz]
  obtain ⟨f, hf, -⟩ := hH.2 A A 1 1 (lat1 P) (lat1 P) θ θ hdim hdim hθ hθ M hM
  exact ⟨f, fun w => hf w⟩

/-- **`T5Glue.ShimuraMainCM` from printed leaves.** The main theorem of CM in Shimura's normalization
(`MainTheoremCMArith`), the Weierstrass parametrization (`WeierstrassParam`), the uniformization theorem
(`WeierstrassUniformization`), the curve `E_Λ` as an abelian variety with its coordinates (`WeierstrassAbVar`),
and the bundle's textbook leaf `HomLatticeCorr` (CM endomorphisms). -/
theorem shimuraMainCM_of_printed (hM : MainTheoremCMArith) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar) (hH : ZInQ.HomUnify.HomLatticeCorr) :
    T5Glue.ShimuraMainCM := by
  intro m _ hsq e he σ s hs 𝔞 P P' hP hP'
  obtain ⟨A, θ, U, x, y, hdim, hθ, hθU⟩ := hWA P
  let S : AddSubgroup (QNeg m) := P.lattice.toAddSubgroup.comap (kap m).toAddMonoidHom
  have hS : (S : Set (QNeg m)) = 𝔞 := by
    ext z
    change kap m z ∈ P.lattice ↔ z ∈ 𝔞
    rw [← SetLike.mem_coe, hP]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rw [kap_apply] at hwz
      rwa [T5Glue.kappa_injective hwz] at hw
    · intro hz; exact ⟨z, hz, (kap_apply z).symm⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ : ∃ b ∈ 𝔞, kappa m b = P.ω₁ := by
    have := P.ω₁_mem_lattice; rw [← SetLike.mem_coe, hP] at this; exact this
  obtain ⟨b₂, hb₂, hb₂'⟩ : ∃ b ∈ 𝔞, kappa m b = P.ω₂ := by
    have := P.ω₂_mem_lattice; rw [← SetLike.mem_coe, hP] at this; exact this
  have hb : ∀ z, z ∈ 𝔞 ↔ ∃ n₁ n₂ : ℤ, z = n₁ * b₁ + n₂ * b₂ := by
    intro z
    constructor
    · intro hz
      have hk : kappa m z ∈ P.lattice := by rw [← SetLike.mem_coe, hP]; exact ⟨z, hz, rfl⟩
      obtain ⟨n₁, n₂, hn⟩ := PeriodPair.mem_lattice.1 hk
      refine ⟨n₁, n₂, T5Glue.kappa_injective ?_⟩
      rw [T5Glue.kappa_add, T5Glue.kappa_intCast_mul, T5Glue.kappa_intCast_mul, hb₁', hb₂', hn]
    · rintro ⟨n₁, n₂, rfl⟩
      rw [← hS]
      have h1 : b₁ ∈ S := by rw [← SetLike.mem_coe, hS]; exact hb₁
      have h2 : b₂ ∈ S := by rw [← SetLike.mem_coe, hS]; exact hb₂
      rw [← zsmul_eq_mul, ← zsmul_eq_mul]
      exact add_mem (zsmul_mem h1 n₁) (zsmul_mem h2 n₂)
  -- `t = N(s)` and the lattice of `A^σ`
  set t : AQ ⊗[ℚ] QNeg m := ((reflexNorm rhoQ (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s) ^
    ((1 : ℤˣ) : ℤ) : (AQ ⊗[ℚ] QNeg m)ˣ) : AQ ⊗[ℚ] QNeg m) with ht_def
  have ht : t = (eK m).symm (T5Glue.finPart s) := by
    rw [ht_def, Units.val_one, zpow_one, reflexNorm_rhoQ]; rfl
  have htmul : ∀ z : QNeg m, t * (1 ⊗ₜ z) =
      (eK m).symm (T5Glue.finPart s * algebraMap (QNeg m) (T5Glue.AfK m) z) := by
    intro z; rw [ht, map_mul, finiteAdeleBaseChangeAlgEquiv_symm_algebraMap]
  have hadel := adelic 𝔞 S hS b₁ b₂ hb
  have hlat : (latAct t S : Set (QNeg m)) = T5Glue.sInvLat m s 𝔞 := by
    ext z
    change t * Algebra.TensorProduct.includeRight z ∈ QMRecPrinted.latHat S ↔ _
    rw [Algebra.TensorProduct.includeRight_apply, htmul, hadel, AlgEquiv.apply_symm_apply]
    rfl
  -- the main theorem of CM
  obtain ⟨θ', hθ', hrel⟩ := hM (QNeg m) 1 (fun _ => kap m) (by rw [finrank_QNeg]) type_inj (QNeg m) (kap m)
    reflex_range 1 rhoQ jQ model σ s (artinCondC_of_artinCond e he σ s hs) A hdim S θ
    (by rw [cmLat_eq S P (by rw [hP, hS])]; exact hθ)
    (isOfType_of_corr hH A hdim θ P hθ S (by rw [hP, hS]))
    (bcC A (σ : ℂ →+* ℂ)) (projC A (σ : ℂ →+* ℂ)) (isPullback_bc σ A) (one_left_bc σ A)
  have hθ'' : IsUniformization (RingHom.id ℂ) (lat1 P') θ' := by
    rw [cmLat_eq _ P' (by rw [hP', hlat])] at hθ'
    exact hθ'
  obtain ⟨ν, hν, hcoord⟩ := core hWP hWU σ P P' A θ U x y hθ hθU θ' hθ''
  refine ⟨ν, hν, fun u v hu huv => ?_⟩
  have hmem : t * (1 ⊗ₜ v) - 1 ⊗ₜ u ∈ QMRecPrinted.latHat S := by
    rw [htmul, ← finiteAdeleBaseChangeAlgEquiv_symm_algebraMap, ← map_sub, hadel,
      AlgEquiv.apply_symm_apply]
    exact huv
  have hr := hrel u v hmem
  have hcv : ∀ z : QNeg m, cmVec (fun _ : Fin 1 => kap m) z = fun _ => kappa m z :=
    fun z => funext fun _ => kap_apply z
  rw [hcv, hcv] at hr
  exact hcoord (kappa m u) (kappa m v) hu hr


/-- **`T5Glue.ShimuraMainCM` from printed leaves and the bundles' current textbook fields** (`HomLatticeCorr` from
`uniformizationLeafAll` and `gagaMorphism` through the chain's `AvSplit.Final.h69`). -/
theorem shimuraMainCM_of_textbook (hM : MainTheoremCMArith) (hWU : WeierstrassUniformization)
    (hWP : WeierstrassParam) (hWA : WeierstrassAbVar)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    T5Glue.ShimuraMainCM :=
  shimuraMainCM_of_printed hM hWU hWP hWA (AvSplit.Final.h69 hUL hG)

end Final

end HcmPrinted

