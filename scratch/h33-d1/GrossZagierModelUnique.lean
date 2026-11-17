import ZInQKernel.Contrib.OneProof.GrossZagierScheme
import ZInQKernel.Contrib.OneProof.CurveModelUnique

/-!
# h33-d1: the Gross–Zagier curve leaf for one model of `X₀(N)` (step S1 removed)

Task h33-d1 (2026-11-17). Report: `docs/research/h33-d1.md`; scratch and log: `scratch/h33-d1/`.

hgz-steps' leaf `GZSch.GrossZagierCurveCd` quantifies over **every** normal proper model
`(X, ι : K(X) ≃ ℚ(X₀(N)))`, which its review rated GLUE on step S1 (nothing in Lean said that all
these models are the canonical model). Here:

* `isCuspInfty_map`, `isPointAt_comp`: a morphism `h : X ⟶ Y` compatible with `ι_X`, `ι_Y` on
  function fields carries cusps to cusps and the point `τ` to the point `τ`.
* `gzModelBody_transfer`: the Gross–Zagier statement for one model `(X, ι)` implies it for every
  other model `(X', ι')`, through the isomorphism `X' ≅ X` of `CurveModel.exists_iso_of_functionField`
  (model uniqueness).
* The new leaf `GrossZagierCurveCdSome` asks for the statement on **some** normal proper model of
  `X₀(N)` (the canonical model is one), so it is weaker than `GrossZagierCurveCd`, and
  `grossZagierCurveCd_of_some : GrossZagierCurveCdSome → GrossZagierCurveCd`.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology HeckeRing.GL2
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZUnique

open ZInQ.GZSch ZInQ.GZAlg ZInQ.GZDict2 ZInQ.CurveModel

/-! ## §1. Cusps and points along a compatible morphism -/

section Transport

variable {N : ℕ} [NeZero N] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (h : X ⟶ Y)
  (c : Y.functionField ⟶ X.functionField)
  (hc : X.fromSpecFunctionField ≫ h = Spec.map c ≫ Y.fromSpecFunctionField)
  (ιX : X.functionField ≃+* X0Field N) (ιY : Y.functionField ≃+* X0Field N)
  (hι : ∀ a, ιX (c.hom a) = ιY a)
include hc hι

theorem isCuspInfty_map (p : X) (hp : IsCuspInfty N ιX p) : IsCuspInfty N ιY (h p) := by
  intro s
  have := hp (h.stalkMap p s)
  rwa [algebraMap_stalkMap h c hc p s, hι] at this

theorem isPointAt_comp (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X) (hx : IsPointAt N ιX τ x) :
    IsPointAt N ιY τ (x ≫ h) := by
  intro s P Q hr
  have := hx (h.stalkMap _ s) P Q (by erw [algebraMap_stalkMap h c hc _ s, hι]; exact hr)
  rw [Scheme.stalkClosedPointTo_comp]
  exact this

end Transport

/-! ## §2. The statement for one model -/

/-- **The Gross–Zagier statement on one model `(X, ι)` of `X₀(N)`**: the part of
`GZSch.GrossZagierCurveAt E` after the model (verbatim). -/
def GZModelBody (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] (f : Newform N 2) (X : Scheme.{0})
    [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)) (ι : X.functionField ≃+* X0Field N) : Prop :=
    ∀ π : X ⟶ ESch E, π ≫ toSpecQ E = sX →
    (∃ p₁ p₂ : X, π p₁ ≠ π p₂) →
    (∀ p : X, IsCuspInfty N ι p → π p ∉ (chartZ E).opensRange) →
    ∀ D β : ℤ, ZInQ.GZDecomp.IsOddImagFundDisc D → D < -4 →
    (∀ p : ℕ, p.Prime → p ∣ N → ZInQ.HGZSteps.epsD D p = 1) →
    (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ (R : Type) [Fintype R] (τ : R → ℍ), ZInQ.GZModuli.IsHeegnerPointReps N D β τ →
    ∀ x : R → (Spec (CommRingCat.of ℂ) ⟶ X), (∀ r, IsPointAt N ι (τ r) (x r)) →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ιK : K →ₐ[ℚ] ℂ, ιK δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ n : ℤ, n ≠ 0 →
    ∀ y : (E⁄K).Point, WeierstrassCurve.Affine.Point.map ιK y = n • ∑ r, ptOf E (x r ≫ π) →
    ∀ F G : ℂ → ℂ, ZInQ.GZDecomp.IsEntireCont (ZInQ.GZDecomp.coeff f) 2 F →
      ZInQ.GZDecomp.IsEntireCont (fun m => ZInQ.GZDecomp.coeff f m * (ZInQ.HGZSteps.epsD D m : ℂ)) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- `GrossZagierCurveAt E` is the model body on every normal proper model (definitional). -/
theorem grossZagierCurveAt_iff (E : WeierstrassCurve ℚ) :
    GrossZagierCurveAt E ↔ ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
      (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
      ∀ (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX →
      ZInQ.Contrib.CurvesG.IsNormalScheme X → topologicalKrullDim X = 1 →
      ∀ ι : X.functionField ≃+* X0Field N, GZModelBody E N f X sX ι := Iff.rfl

theorem valuationRing_of_model {X : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    (hprop : IsProper sX) (hN : ZInQ.Contrib.CurvesG.IsNormalScheme X)
    (hdim : topologicalKrullDim X = 1) (p : X) : ValuationRing (X.presheaf.stalk p) := by
  have := hprop
  have : LocallyOfFiniteType sX := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  exact valuationRing_stalk_of_normal X hN hdim p

/-! ## §3. Transfer between models -/

/-- **Transfer (S1 in Lean)**: the Gross–Zagier statement on one model `(X, ι)` whose local rings
are valuation rings gives it on every other such model `(X', ι')`. -/
theorem gzModelBody_transfer (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] (f : Newform N 2)
    {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    (sX' : X' ⟶ Spec (CommRingCat.of ℚ)) [IsProper sX] [IsProper sX']
    (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p))
    (hv' : ∀ p : X', ValuationRing (X'.presheaf.stalk p))
    (ι : X.functionField ≃+* X0Field N) (ι' : X'.functionField ≃+* X0Field N)
    (hX : GZModelBody E N f X sX ι) : GZModelBody E N f X' sX' ι' := by
  set e : X'.functionField ≃+* X.functionField := ι'.trans ι.symm with he
  obtain ⟨F, hFi, hF⟩ := exists_iso_of_functionField sX' sX hv' hv e
  set G := inv F
  have hFG : F ≫ G = 𝟙 X' := IsIso.hom_inv_id F
  have hGF : G ≫ F = 𝟙 X := IsIso.inv_hom_id F
  have hGF' : ∀ p : X, F (G p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, hGF]; rfl
  have hFG' : ∀ p : X', G (F p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, hFG]; rfl
  have hee : Spec.map (CommRingCat.ofHom (e : X'.functionField →+* X.functionField)) ≫
      Spec.map (CommRingCat.ofHom (e.symm : X.functionField →+* X'.functionField)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : X'.functionField →+* X.functionField).comp
        (e.symm : X.functionField →+* X'.functionField) = RingHom.id _ := by
      ext a; simp
    rw [this]
    exact Spec.map_id _
  have hG : X.fromSpecFunctionField ≫ G =
      Spec.map (CommRingCat.ofHom (e : X'.functionField →+* X.functionField)) ≫
        X'.fromSpecFunctionField := by
    have h1 : X'.fromSpecFunctionField = Spec.map (CommRingCat.ofHom
        (e.symm : X.functionField →+* X'.functionField)) ≫ X.fromSpecFunctionField ≫ G := by
      rw [← Category.assoc, ← hF, Category.assoc, hFG, Category.comp_id]
    rw [h1, ← Category.assoc, ← Category.assoc, hee]
    exact (Category.id_comp _).symm
  -- compatibility of the identifications
  have hιF : ∀ a, ι' ((CommRingCat.ofHom (e.symm : X.functionField →+* X'.functionField)).hom a) =
      ι a := fun a => by simp [he]
  have hιG : ∀ a, ι ((CommRingCat.ofHom (e : X'.functionField →+* X.functionField)).hom a) =
      ι' a := fun a => by simp [he]
  intro π' hπ' hnc hcusp D β hD hD4 hsplit hβ R _ τ hτ x' hx' K _ _ _ hK δ hδ ιK hιK n hn y hy
    Fc Gc hFc hGc
  refine hX (G ≫ π') (specQ_ext _ _) ?_ ?_ D β hD hD4 hsplit hβ R τ hτ (fun r => x' r ≫ F)
    (fun r => isPointAt_comp F _ hF ι' ι hιF (τ r) (x' r) (hx' r)) K hK δ hδ ιK hιK n hn y ?_
    Fc Gc hFc hGc
  · obtain ⟨p₁, p₂, hne⟩ := hnc
    refine ⟨F p₁, F p₂, ?_⟩
    simp only [Scheme.Hom.comp_apply, hFG']
    exact hne
  · intro p hp
    have := isCuspInfty_map G _ hG ι ι' hιG p hp
    simpa only [Scheme.Hom.comp_apply] using hcusp (G p) this
  · rw [hy]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Category.assoc, ← Category.assoc F G π', hFG, Category.id_comp]

/-! ## §4. The leaf for some model -/

/-- **The Gross–Zagier formula on some model of `X₀(N)` (Gross–Zagier 1986, Thm I.6.3 and Ch. V
Thm 2.1; positive constant forgotten).** As `GZSch.GrossZagierCurveAt E`, except that the
statement is asked for **one** integral normal scheme `X`, proper of dimension `1` over `ℚ`, with
function field `ι : K(X) ≃ ℚ(X₀(N)) = ℚ(j, j_N)`: the canonical model `X₀(N)/ℚ` (Shimura 1971,
§6.7, UNVERIFIED locator) is one. Weaker than `GrossZagierCurveAt E` (which asks it for every
such model); `grossZagierCurveAt_of_some` proves the converse in Lean (model uniqueness).

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84
(1986), 225–320, Thm I.6.3 and Ch. V §2 (Thm 2.1), for a modular parametrization
`π : X₀(N) → E` with `π(∞) = 0`. Weakenings as in `GrossZagierCurveAt`. -/
def GrossZagierCurveAtSome (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
    ∃ (X : Scheme.{0}) (_ : IsIntegral X) (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX ∧
      ZInQ.Contrib.CurvesG.IsNormalScheme X ∧ topologicalKrullDim X = 1 ∧
      ∃ ι : X.functionField ≃+* X0Field N, GZModelBody E N f X sX ι

/-- **Leaf (curve form, one model)**: `GrossZagierCurveAtSome E'` for every short model `E'` in
the isogeny class of `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree. -/
def GrossZagierCurveCdSome : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic], ZInQ.GZOptimal.IsShortModel E' →
      (∀ n : ℕ, n ≠ 0 → E'.LFunction n = (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LFunction n) →
      GrossZagierCurveAtSome E'

theorem grossZagierCurveAt_of_some (E : WeierstrassCurve ℚ) (h : GrossZagierCurveAtSome E) :
    GrossZagierCurveAt E := by
  rw [grossZagierCurveAt_iff]
  intro N _ f hχ hf X' _ sX' hprop' hN' hdim' ι'
  obtain ⟨X, hXi, sX, hprop, hN, hdim, ι, hbody⟩ := h N f hχ hf
  haveI := hprop
  haveI := hprop'
  exact gzModelBody_transfer E N f sX sX' (valuationRing_of_model sX hprop hN hdim)
    (valuationRing_of_model sX' hprop' hN' hdim') ι ι' hbody

/-- **hgz-steps' leaf from the one-model leaf** (S1 discharged). -/
theorem grossZagierCurveCd_of_some (h : GrossZagierCurveCdSome) : GrossZagierCurveCd :=
  fun d hd hsq E' _ hE' hL => grossZagierCurveAt_of_some E' (h d hd hsq E' hE' hL)

/-- **What `frozenTarget` reads (`hGZ`), from the one-model leaf.** -/
theorem grossZagierAlgOptCd_of_some (h : GrossZagierCurveCdSome) : GZAlg.GrossZagierAlgOptCd :=
  grossZagierAlgOptCd_of_curve (grossZagierCurveCd_of_some h)

/-! ## §5. Transfer data between two models (for any statement over a model) -/

/-- **Model transfer data**: between two normal proper models `(X, ι)`, `(X', ι')` of `X₀(N)` there
are mutually inverse morphisms `F : X' ⟶ X`, `G : X ⟶ X'` carrying cusps to cusps and the point `τ`
to the point `τ`, in both directions. -/
theorem model_transfer {N : ℕ} [NeZero N] {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (sX : X ⟶ Spec (CommRingCat.of ℚ)) (sX' : X' ⟶ Spec (CommRingCat.of ℚ)) [IsProper sX]
    [IsProper sX'] (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p))
    (hv' : ∀ p : X', ValuationRing (X'.presheaf.stalk p))
    (ι : X.functionField ≃+* X0Field N) (ι' : X'.functionField ≃+* X0Field N) :
    ∃ (F : X' ⟶ X) (G : X ⟶ X'), F ≫ G = 𝟙 X' ∧ G ≫ F = 𝟙 X ∧
      (∀ p : X, IsCuspInfty N ι p → IsCuspInfty N ι' (G p)) ∧
      (∀ p : X', IsCuspInfty N ι' p → IsCuspInfty N ι (F p)) ∧
      (∀ (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X'), IsPointAt N ι' τ x → IsPointAt N ι τ (x ≫ F)) ∧
      (∀ (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X), IsPointAt N ι τ x → IsPointAt N ι' τ (x ≫ G)) := by
  set e : X'.functionField ≃+* X.functionField := ι'.trans ι.symm with he
  obtain ⟨F, hFi, hF⟩ := exists_iso_of_functionField sX' sX hv' hv e
  set G := inv F
  have hFG : F ≫ G = 𝟙 X' := IsIso.hom_inv_id F
  have hGF : G ≫ F = 𝟙 X := IsIso.inv_hom_id F
  have hee : Spec.map (CommRingCat.ofHom (e : X'.functionField →+* X.functionField)) ≫
      Spec.map (CommRingCat.ofHom (e.symm : X.functionField →+* X'.functionField)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : X'.functionField →+* X.functionField).comp
        (e.symm : X.functionField →+* X'.functionField) = RingHom.id _ := by
      ext a; simp
    rw [this]
    exact Spec.map_id _
  have hG : X.fromSpecFunctionField ≫ G =
      Spec.map (CommRingCat.ofHom (e : X'.functionField →+* X.functionField)) ≫
        X'.fromSpecFunctionField := by
    have h1 : X'.fromSpecFunctionField = Spec.map (CommRingCat.ofHom
        (e.symm : X.functionField →+* X'.functionField)) ≫ X.fromSpecFunctionField ≫ G := by
      rw [← Category.assoc, ← hF, Category.assoc, hFG, Category.comp_id]
    rw [h1, ← Category.assoc, ← Category.assoc, hee]
    exact (Category.id_comp _).symm
  have hιF : ∀ a, ι' ((CommRingCat.ofHom (e.symm : X.functionField →+* X'.functionField)).hom a) =
      ι a := fun a => by simp [he]
  have hιG : ∀ a, ι ((CommRingCat.ofHom (e : X'.functionField →+* X.functionField)).hom a) =
      ι' a := fun a => by simp [he]
  exact ⟨F, G, hFG, hGF, fun p hp => isCuspInfty_map G _ hG ι ι' hιG p hp,
    fun p hp => isCuspInfty_map F _ hF ι' ι hιF p hp,
    fun τ x hx => isPointAt_comp F _ hF ι' ι hιF τ x hx,
    fun τ x hx => isPointAt_comp G _ hG ι ι' hιG τ x hx⟩

end ZInQ.GZUnique
