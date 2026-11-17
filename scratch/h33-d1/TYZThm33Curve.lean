import ZInQKernel.Contrib.OneProof.TYZThm33Alg
import ZInQKernel.Contrib.OneProof.TYZThm33Curve.Normal
import ZInQKernel.Contrib.OneProof.GrossZagierModelUnique

/-!
# h33-d1: TYZ Theorem 3.3 for TYZ's isomorphism of curves `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ`

Task h33-d1 (2026-11-17). Report: `docs/research/h33-d1.md`; scratch and log: `scratch/h33-d1/`.

The leaf `TYZThm33CurveSome` states Tian–Yuan–Zhang Theorem 3.3 with `i₀` a genuine isomorphism of
proper curves over `ℚ`, as TYZ print it: on **some** normal proper model `(X, ι)` of `X₀(32)`
(`X` integral, normal, proper of dimension `1` over `ℚ`, `ι : K(X) ≅ ℚ(X₀(32)) = ℚ(j, j₃₂) ⊂ ℚ((q))`;
the canonical model is one), for every isomorphism of `ℚ`-schemes `i₀ : X ⟶ ESch curveA` sending
the cusp `∞` to `O`, with the CM points `P_n` the `ℂ`-points of `X` at `τ_n` (`GZSch.IsPointAt`).
`TYZThm33Curve` is the same for every such model; it implies the one-model leaf
(`tyzThm33CurveSome_of_all`).

`tyzThm33Alg_of_curveSome : TYZThm33CurveSome → H33Fix.TYZThm33Alg` proves the step D1 in Lean,
in both directions:
* `φ^*` bijective gives `e : K(X) ≅ ℚ(X₀(32)) ≅ ℚ(A) ≅ K(ESch curveA)` (`ffEquiv`, `Charts.lean`);
* model uniqueness (`CurveModel.exists_iso_of_functionField`) turns `e` into an isomorphism of
  schemes `i₀ : X ≅ ESch curveA`; this needs the local rings of `ESch curveA` to be valuation
  rings (`valuationRing_stalk_ESch`, `Normal.lean`, including the point `O`);
* `i₀(∞) = O` and `i₀(P_n) = (X(τ_n), Y(τ_n))` from hgz-steps' `cusp_not_mem_chart`,
  `ptOf_eq_modPt`.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology
open scoped WeierstrassCurve.Affine Manifold

namespace ZInQ.H33D1

open ZInQ.GZSch ZInQ.GZAlg ZInQ.GZDict2
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.TYZSplit
  ZInQ.Contrib.TYZGenus.H33Dict ZInQ.Contrib.TYZGenus.CMBridge

instance curveA_isElliptic' : curveA.IsElliptic := by
  unfold curveA
  exact ZInQ.shortCurve_isElliptic (by norm_num)

/-! ## §1. The leaf -/

/-- **The statement of TYZ Theorem 3.3 on one model `(X, ι)` of `X₀(32)`.** For every isomorphism
`i₀ : X ⟶ ESch curveA` over `ℚ` with `i₀(∞) = O`, and every family `w` of algebraic points with
`w n = i₀(P_n)` in `A(ℂ)`, `TYZThm33EpsAfter (zOfLift w)`. -/
def TYZ33Body (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    (ι : X.functionField ≃+* X0Field 32) : Prop :=
  ∀ i₀ : X ⟶ ESch curveA, IsIso i₀ → i₀ ≫ toSpecQ curveA = sX →
  (∀ p : X, IsCuspInfty 32 ι p → i₀ p = ptO curveA) →
  ∀ w : ℕ → PtA,
    (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
      IsPointAt 32 ι (tyzForm n hn).tauH x → toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) →
    (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
      IsPointAt 32 ι (tyzForm7 n hn).tauH x → toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) →
    TYZThm33EpsAfter (zOfLift w)

/-- **Leaf TYZ-3.3 (curve form, one model): Tian–Yuan–Zhang Theorem 3.3 for TYZ's isomorphism of
curves `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ`, for `n ≡ 5, 7 (mod 8)`.**

Source: Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*,
arXiv:1411.4728v1, Theorem 3.3 (Period7.tex L1296–1311), with §3.1: `A` "is isomorphic to
`(X₀(32), ∞)`. Fix an identification `i₀`" (L1173–1174), `f_n = f₀ − f₀∘[i]` for `n ≡ 5` and
`f_n = i₀` for `n ≡ 7` (L1195–1198), the CM points `P_n` (L1203–1295). Journal version: Asian J.
Math. 21 (2017), NOT checked.

The objects:
* `X₀(32)` is the canonical model over `ℚ` (Shimura 1971 §6.7, UNVERIFIED locator): an integral
  normal scheme `X`, proper of dimension `1` over `ℚ`, with function field
  `ι : K(X) ≅ ℚ(X₀(32)) = ℚ(j, j₃₂) ⊂ ℚ((q))` (FLT's `modularFunctionField 32`, embedded by
  `q`-expansion at `∞`). The leaf asks the statement for **some** such `(X, ι)`: weaker than for
  all of them (`TYZThm33Curve`), and the canonical model is one. Any two are isomorphic
  compatibly with `ι` (`CurveModel.exists_iso_of_functionField`, proved).
* `A` is the projective scheme `ESch curveA = Proj ℚ[X, Y, Z]/(Y²Z − X³ − 4XZ²)` (`y² = x³ + 4x`,
  `ℚ`-isomorphic to TYZ's `2y² = x³ + x` by `(x, y) ↦ (2x, 4y)`).
* `i₀ : X ⟶ ESch curveA` is an isomorphism of `ℚ`-schemes with `i₀(∞) = O`: the cusp `∞`
  (`IsCuspInfty`, the center of `ord_q`) maps to the point `O = ptO curveA` (the `ℚ`-point
  `[0 : 1 : 0]` of the chart `D₊(Y)`, `chiO`), the unique point outside the chart `D₊(Z)`
  (G4(b), `not_mem_chartZ_iff`).
* `P_n` is the CM point `τ_n` of `tyzForm n` (`n ≡ 5`) resp. `tyzForm7 n` (`n ≡ 7`): the
  `ℂ`-points `x` of `X` at `τ_n` (`IsPointAt`), and `i₀(P_n) ∈ A(ℂ)` is `ptOf curveA (x ≫ i₀)`.
* `w n ∈ A(ℚ̄)` with `w n = i₀(P_n)` in `A(ℂ)`; then `TYZThm33EpsAfter (zOfLift w)` (h33-dict's
  display: `P_χ` torsion unless `χ = χ_{d₀,d₁}`, and then `P_χ = ε(d₀, d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)`
  in `A(ℚ̄) ⊗ ℚ`, `ε` chosen after `Φ`, `χ`), with `z_n = w n − [i](w n)` for `n ≡ 5` and
  `z_n = w n` for `n ≡ 7`.

Readings (not Lean): `X_U ≅ X₀(32)_{ℚ(i)}` with `P_n ↦ τ_n` (L1191–1193, G5) and the sign of `[i]`
(h33-sign), unchanged from h33-fix; the weakenings of h33-dict. -/
def TYZThm33CurveSome : Prop :=
  ∃ (X : Scheme.{0}) (_ : IsIntegral X) (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX ∧
    ZInQ.Contrib.CurvesG.IsNormalScheme X ∧ topologicalKrullDim X = 1 ∧
    ∃ ι : X.functionField ≃+* X0Field 32, TYZ33Body X sX ι

/-- **TYZ Theorem 3.3, curve form, on every normal proper model of `X₀(32)`.** -/
def TYZThm33Curve : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX →
    ZInQ.Contrib.CurvesG.IsNormalScheme X → topologicalKrullDim X = 1 →
    ∀ ι : X.functionField ≃+* X0Field 32, TYZ33Body X sX ι

/-- The all-models form implies the one-model leaf (a normal proper model exists, hgz-steps'
`exists_model`). -/
theorem tyzThm33CurveSome_of_all (h : TYZThm33Curve) : TYZThm33CurveSome := by
  obtain ⟨X, hXi, sX, hprop, hN, hdim, ⟨ι⟩⟩ := exists_model 32
  exact ⟨X, hXi, sX, hprop, hN, hdim, ι, h X sX hprop hN hdim ι⟩

/-! ## §2. The value of `i₀` at `τ` is `(X(τ), Y(τ))` -/

theorem tendsto_of_mdiff {Xf : ℍ → ℂ} (hXf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Xf) (τ : ℍ) :
    Tendsto (Xf ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 (Xf τ)) := by
  have h := ((ZInQ.H33Fix.analyticOnNhd_of_mdiff hXf) τ τ.im_pos).continuousAt.tendsto
  have e : (Xf ∘ ofComplex) (τ : ℂ) = Xf τ := by simp [Function.comp_apply, ofComplex_apply]
  rw [e] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **The plane-model value `modPt` is h33-dict's `ptOf X Y τ`** for the holomorphic `X, Y` with
`q`-expansions `φ(x), φ(y)`. -/
theorem modPt_eq_h33 (φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32)
    {Xf Yf : ℍ → ℂ} (hXf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Xf) (hYf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Yf)
    (hqX : HasQExp Xf (φ (genX curveA))) (hqY : HasQExp Yf (φ (genY curveA))) (τ : ℍ)
    {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep 32 (φ (genX curveA) : LaurentSeries ℚ) Px Qx)
    (hry : IsRatRep 32 (φ (genY curveA) : LaurentSeries ℚ) Py Qy) :
    ZInQ.GZModuli.modPt curveA (ratFn 32 Px Qx) (ratFn 32 Py Qy) τ =
      ZInQ.Contrib.TYZGenus.H33Dict.ptOf Xf Yf τ := by
  have hmX : ∀ τ : ℍ, MeromorphicAt (Xf ∘ ofComplex) (τ : ℂ) := fun τ =>
    ((ZInQ.H33Fix.analyticOnNhd_of_mdiff hXf) τ τ.im_pos).meromorphicAt
  have hmY : ∀ τ : ℍ, MeromorphicAt (Yf ∘ ofComplex) (τ : ℂ) := fun τ =>
    ((ZInQ.H33Fix.analyticOnNhd_of_mdiff hYf) τ τ.im_pos).meromorphicAt
  have hlx := (tendsto_of_mdiff hXf τ).congr' (eventuallyEq_ratFn hmX hqX hrx τ)
  have hly := (tendsto_of_mdiff hYf τ).congr' (eventuallyEq_ratFn hmY hqY hry τ)
  rcases modPt_plane_cases curveA φ hrx hry τ with ⟨x₀, y₀, hns, hl1, hl2, hmod⟩ | ⟨hpole, -⟩
  · have e1 : Xf τ = x₀ := tendsto_nhds_unique hlx hl1
    have e2 : Yf τ = y₀ := tendsto_nhds_unique hly hl2
    rw [hmod]
    have hns' : ZInQ.Contrib.TYZGenus.X0.curveAC.toAffine.Nonsingular (Xf τ) (Yf τ) := by
      rw [e1, e2]; exact hns
    unfold ZInQ.Contrib.TYZGenus.H33Dict.ptOf
    rw [dif_pos hns']
    exact point_some_congr curveA _ _ e1.symm e2.symm
  · exact absurd hpole (not_tendsto_atTop_of_tendsto_nhds hlx.norm)

/-! ## §3. The isomorphism `i₀` from `φ` (D1 in both directions) -/

/-- `K(X) ≅ ℚ(X₀(32)) ≅ ℚ(A) ≅ K(ESch curveA)` from `ι` and a bijective `φ`. -/
def eOf {X : Scheme.{0}} [IsIntegral X] (ι : X.functionField ≃+* X0Field 32)
    (φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32) (hφ : Function.Bijective φ) :
    X.functionField ≃+* (ESch curveA).functionField :=
  (ι.trans (RingEquiv.ofBijective (φ : curveA.toAffine.FunctionField →+* X0Field 32) hφ).symm).trans
    (ffEquiv curveA).symm

theorem eOf_symm_kappaZ {X : Scheme.{0}} [IsIntegral X] (ι : X.functionField ≃+* X0Field 32)
    (φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32) (hφ : Function.Bijective φ) :
    ((eOf ι φ hφ).symm : (ESch curveA).functionField →+* X.functionField).comp (kappaZ curveA) =
      uOf φ ι := by
  apply ringHom_ext_AZ curveA
  · rw [RingHom.comp_apply, uOf_xz]
    simp only [eOf, RingEquiv.coe_toRingHom, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
      ffEquiv_xz]
    rfl
  · rw [RingHom.comp_apply, uOf_yz]
    simp only [eOf, RingEquiv.coe_toRingHom, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
      ffEquiv_yz]
    rfl

/-- **D1 in both directions: `φ^*` is induced by an isomorphism of curves `i₀ : X ≅ A`** over
`ℚ`, for any normal proper model `(X, ι)` of `X₀(32)`. -/
theorem exists_iso_of_phi {X : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper sX] (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p))
    (ι : X.functionField ≃+* X0Field 32) (φ : curveA.toAffine.FunctionField →ₐ[ℚ] X0Field 32)
    (hφ : Function.Bijective φ) :
    ∃ i₀ : X ⟶ ESch curveA, IsIso i₀ ∧
      X.fromSpecFunctionField ≫ i₀ = Spec.map (CommRingCat.ofHom (uOf φ ι)) ≫ chartZ curveA := by
  obtain ⟨F, hFi, hF⟩ := ZInQ.CurveModel.exists_iso_of_functionField sX (toSpecQ curveA) hv
    (valuationRing_stalk_ESch curveA) (eOf ι φ hφ)
  refine ⟨F, hFi, ?_⟩
  rw [hF, ← kappaZ_spec curveA, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    eOf_symm_kappaZ]

/-! ## §4. The bridge -/

/-- **D1 in Lean: the function-field leaf from the curve leaf.** -/
theorem tyzThm33Alg_of_curveSome (h : TYZThm33CurveSome) : ZInQ.H33Fix.TYZThm33Alg := by
  intro φ hφ Xf Yf hXf hYf hqX hqY w h5 h7
  obtain ⟨X, hXi, sX, hprop, hN, hdim, ι, hbody⟩ := h
  have := hprop
  have hv := ZInQ.GZUnique.valuationRing_of_model sX hprop hN hdim
  obtain ⟨i₀, hiso, hπ⟩ := exists_iso_of_phi sX hv ι φ hφ.1
  have hrx := repOf_spec (φ (genX curveA))
  have hry := repOf_spec (φ (genY curveA))
  have hval : ∀ (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X), IsPointAt 32 ι τ x →
      ZInQ.GZSch.ptOf curveA (x ≫ i₀) = ZInQ.Contrib.TYZGenus.H33Dict.ptOf Xf Yf τ := by
    intro τ x hx
    rw [ptOf_eq_modPt φ hv ι i₀ hπ hrx hry τ x hx]
    exact modPt_eq_h33 φ hXf hYf hqX hqY τ hrx hry
  refine hbody i₀ hiso (specQ_ext _ _)
    (fun p hp => (not_mem_chartZ_iff curveA _).mp (cusp_not_mem_chart φ ι i₀ hπ hφ.2 p hp)) w ?_ ?_
  · intro n hn hsq x hx
    rw [h5 n hn hsq, hval _ x hx]
  · intro n hn hsq x hx
    rw [h7 n hn hsq, hval _ x hx]

/-- **`TYZSplit.TYZThm33` (the binder `h33` of `frozenTarget`) from the curve leaf** and the
printed main theorem of CM `hCM`. -/
theorem tyzThm33_of_curveSome (hCM : T5Glue.ShimuraMainCM)
    (h : TYZThm33CurveSome) : TYZThm33 :=
  ZInQ.H33Fix.tyzThm33_of_alg hCM (tyzThm33Alg_of_curveSome h)

/-! ## §5. The one-model leaf gives every model, and its hypotheses are satisfiable -/

/-- **The one-model leaf implies the all-models form** (model uniqueness: transfer along the
isomorphism of models, `GZUnique.model_transfer`). With `tyzThm33CurveSome_of_all`, the two forms
are equivalent. -/
theorem tyzThm33Curve_of_some (h : TYZThm33CurveSome) : TYZThm33Curve := by
  intro X' _ sX' hprop' hN' hdim' ι' i₀' hiso' _ hcusp' w h5 h7
  obtain ⟨X, hXi, sX, hprop, hN, hdim, ι, hbody⟩ := h
  haveI := hprop
  haveI := hprop'
  obtain ⟨F, G, hFG, hGF, hcG, -, -, hpG⟩ := ZInQ.GZUnique.model_transfer sX sX'
    (ZInQ.GZUnique.valuationRing_of_model sX hprop hN hdim)
    (ZInQ.GZUnique.valuationRing_of_model sX' hprop' hN' hdim') ι ι'
  haveI : IsIso G := ⟨⟨F, hGF, hFG⟩⟩
  refine hbody (G ≫ i₀') inferInstance (specQ_ext _ _) ?_ w ?_ ?_
  · intro p hp
    simpa only [Scheme.Hom.comp_apply] using hcusp' (G p) (hcG p hp)
  · intro n hn hsq x hx
    rw [← Category.assoc]
    exact h5 n hn hsq (x ≫ G) (hpG _ x hx)
  · intro n hn hsq x hx
    rw [← Category.assoc]
    exact h7 n hn hsq (x ≫ G) (hpG _ x hx)

/-- **The hypotheses of the leaf are satisfiable** (given `hCM`) on every normal proper model of
`X₀(32)`: there is an isomorphism `i₀ : X ≅ A` over `ℚ` with `i₀(∞) = O` (from the eta model), and a
family `w` of algebraic points with `w n = i₀(P_n)`; so `TYZ33Body` is not vacuous. -/
theorem tyzThm33Curve_hyps_satisfiable (hCM : T5Glue.ShimuraMainCM) {X : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper sX]
    (hv : ∀ p : X, ValuationRing (X.presheaf.stalk p)) (ι : X.functionField ≃+* X0Field 32) :
    ∃ i₀ : X ⟶ ESch curveA, IsIso i₀ ∧ i₀ ≫ toSpecQ curveA = sX ∧
      (∀ p : X, IsCuspInfty 32 ι p → i₀ p = ptO curveA) ∧
      ∃ w : ℕ → PtA,
        (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
          IsPointAt 32 ι (tyzForm n hn).tauH x → toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) ∧
        (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
          IsPointAt 32 ι (tyzForm7 n hn).tauH x → toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) := by
  obtain ⟨φ, hφ, Xf, Yf, hXf, hYf, hqX, hqY, w, h5, h7⟩ :=
    ZInQ.H33Fix.tyzThm33Alg_hyps_satisfiable hCM
  obtain ⟨i₀, hiso, hπ⟩ := exists_iso_of_phi sX hv ι φ hφ.1
  have hrx := repOf_spec (φ (genX curveA))
  have hry := repOf_spec (φ (genY curveA))
  have hval : ∀ (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X), IsPointAt 32 ι τ x →
      ZInQ.GZSch.ptOf curveA (x ≫ i₀) = ZInQ.Contrib.TYZGenus.H33Dict.ptOf Xf Yf τ := by
    intro τ x hx
    rw [ptOf_eq_modPt φ hv ι i₀ hπ hrx hry τ x hx]
    exact modPt_eq_h33 φ hXf hYf hqX hqY τ hrx hry
  refine ⟨i₀, hiso, specQ_ext _ _,
    fun p hp => (not_mem_chartZ_iff curveA _).mp (cusp_not_mem_chart φ ι i₀ hπ hφ.2 p hp), w, ?_, ?_⟩
  · intro n hn hsq x hx
    rw [h5 n hn hsq, hval _ x hx]
  · intro n hn hsq x hx
    rw [h7 n hn hsq, hval _ x hx]

end ZInQ.H33D1
