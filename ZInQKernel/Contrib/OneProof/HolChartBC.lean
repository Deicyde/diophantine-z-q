import ZInQKernel.Contrib.OneProof.HolChartSerre
import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge

/-! # r3prime-bc: R3′ with the genuine complex space of the base change `𝒢 ×_{𝓞_L,τ} ℂ`

Task r3prime-bc (2026-11-17), report `docs/research/r3prime-bc.md`, scratch `scratch/r3prime-bc/`.
Follow-up to r3prime-etale (`HolChartSerre.lean`), whose Serre sheaf `AnHolAt` was built on `𝒢.Pts τ`
(topology `anTop`) from regular functions of the model `𝒢` over `𝓞_L`. Its reading note (a), that this is
the sheaf of the base change `𝒢 ×_{𝓞_L,τ} Spec ℂ`, is proved here:

* §1 `bc 𝒢 τ` (the base change, a `ℂ`-scheme), `ptsEquivBC`, `xevalAt_toBC` (evaluation of regular
  functions is compatible), `bc_formula` (near each point a regular function of the base change is
  `Σ u_j c_j / (Σ v_j c_j)^N` with `c_j` regular on `𝒢`: `Γ(Spec ℂ ×_{𝓞_L} V) = ℂ ⊗ Γ(V)`, through
  r3prime-etale's `exists_tensor_formula`), `anTop_eq_induced`, and the homeomorphism
  `ptsHomeomorph : (𝒢.Pts τ, anTop) ≃ₜ ((𝒢 ×_τ ℂ)(ℂ), classicalTopology)` (Bridge's classical topology;
  `ptsHomeomorphPort` composes with Bridge's `cptHomeomorph`, `chartedSpacePts` transports the vendored
  atlas);
* §2 `BCHolAt X` (Serre's sheaf of a `ℂ`-scheme `X` from its own regular functions, GAGA §2) and the
  comparison `bcHolAt_iff : BCHolAt (bc 𝒢 τ) k (toBC q) ↔ AnHolAt 𝒢 τ (k ∘ toBC) q`;
* §3 `IsBCSerreChart` (charts of the complex space `((𝒢 ×_τ ℂ)(ℂ), 𝒪^an)`),
  `isHolChart_iff_isBCSerreChart (hT35)`, `isBCSerreChart_iff_isHolChart`, `exists_bcSerreChart_at`,
  and the unit-germ charts `bcHolAt_chartAt`, `unitGermChart_bc`.

ON THE SPOT: not in the manuscript (which uses the stable Faltings height of the literature) nor in its
bibliography; proved here in Lean, no new leaf. No `sorry`, no `axiom`, no code that runs at build time. -/

open CategoryTheory AlgebraicGeometry Topology Set Filter MonObj Limits
open ZInQ.DefFaltings ZInQ.HeightGlue ZInQ.HeightDict ZInQ.R3Residual ZInQ.R3Etale CloudB3W17Hodge

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

attribute [local instance] ZInQ.HeightGlue.anTop CloudB3W17Hodge.classicalTopology

namespace ZInQ.R3BC

/-! ## §1. The base change `𝒢 ×_{𝓞_L,τ} Spec ℂ` and its complex points -/

section BaseChange

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec ℂ → Spec 𝓞_L` via `τ` (the structure map of `GroupModel.ptC τ`). -/
noncomputable abbrev bcBase (τ : L →+* ℂ) : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers L)) :=
  Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (NumberField.RingOfIntegers L) L)))

/-- The base change `𝒢_τ = 𝒢 ×_{𝓞_L, τ} Spec ℂ` of a group model along `τ`, a `ℂ`-scheme. -/
noncomputable def bc (𝒢 : GroupModel A L) (τ : L →+* ℂ) : Over (Spec (CommRingCat.of ℂ)) :=
  Over.mk (pullback.fst (bcBase τ) 𝒢.G.hom)

/-- The projection `𝒢_τ → 𝒢`. -/
noncomputable def pr (𝒢 : GroupModel A L) (τ : L →+* ℂ) : (bc 𝒢 τ).left ⟶ 𝒢.G.left :=
  pullback.snd (bcBase τ) 𝒢.G.hom

theorem ptObj_hom : (PkgI3.AbVar.ptObj (K := ℂ) ℂ).hom = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  simp [PkgI3.AbVar.ptObj]

variable (𝒢 : GroupModel A L) (τ : L →+* ℂ)

/-- The underlying morphism `Spec ℂ → 𝒢` of a complex point. -/
noncomputable abbrev ptL (p : 𝒢.Pts τ) : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := p.left

/-- The underlying morphism `Spec ℂ → 𝒢 ×_τ Spec ℂ` of a `ℂ`-point of the base change. -/
noncomputable abbrev cptL (P : CPt (bc 𝒢 τ)) : Spec (CommRingCat.of ℂ) ⟶ pullback (bcBase τ) 𝒢.G.hom := P.left

theorem pts_w (p : 𝒢.Pts τ) : 𝟙 _ ≫ bcBase τ = ptL 𝒢 τ p ≫ 𝒢.G.hom := by
  rw [Category.id_comp]; exact (Over.w p).symm

/-- `(id, p) : Spec ℂ → 𝒢 ×_τ Spec ℂ`. -/
noncomputable def toBCl (p : 𝒢.Pts τ) : Spec (CommRingCat.of ℂ) ⟶ pullback (bcBase τ) 𝒢.G.hom :=
  pullback.lift (𝟙 _) (ptL 𝒢 τ p) (pts_w 𝒢 τ p)

theorem toBCl_fst (p : 𝒢.Pts τ) : toBCl 𝒢 τ p ≫ pullback.fst (bcBase τ) 𝒢.G.hom = 𝟙 _ :=
  pullback.lift_fst _ _ _

theorem toBCl_snd (p : 𝒢.Pts τ) : toBCl 𝒢 τ p ≫ pullback.snd (bcBase τ) 𝒢.G.hom = ptL 𝒢 τ p :=
  pullback.lift_snd _ _ _

/-- A complex point `p : Spec ℂ → 𝒢` over `τ`, as a `ℂ`-point `(id, p)` of the base change. -/
noncomputable def toBC (p : 𝒢.Pts τ) : CPt (bc 𝒢 τ) :=
  Over.homMk (toBCl 𝒢 τ p) ((toBCl_fst 𝒢 τ p).trans ptObj_hom.symm)

theorem toBC_left (p : 𝒢.Pts τ) : cptL 𝒢 τ (toBC 𝒢 τ p) = toBCl 𝒢 τ p := rfl

theorem cpt_fst (P : CPt (bc 𝒢 τ)) : cptL 𝒢 τ P ≫ pullback.fst (bcBase τ) 𝒢.G.hom = 𝟙 _ := by
  have := Over.w P
  rw [ptObj_hom] at this
  exact this

theorem ofBC_w (P : CPt (bc 𝒢 τ)) : (cptL 𝒢 τ P ≫ pullback.snd (bcBase τ) 𝒢.G.hom) ≫ 𝒢.G.hom = bcBase τ := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, cpt_fst, Category.id_comp]

/-- A `ℂ`-point of the base change, as a complex point of `𝒢` over `τ`. -/
noncomputable def ofBC (P : CPt (bc 𝒢 τ)) : 𝒢.Pts τ :=
  Over.homMk (cptL 𝒢 τ P ≫ pullback.snd (bcBase τ) 𝒢.G.hom) (ofBC_w 𝒢 τ P)

theorem toBC_pr (p : 𝒢.Pts τ) : cptL 𝒢 τ (toBC 𝒢 τ p) ≫ pr 𝒢 τ = ptL 𝒢 τ p :=
  toBCl_snd 𝒢 τ p

/-- **Complex points of `𝒢` at `τ` are the `ℂ`-points of the base change** (as a bare equivalence). -/
noncomputable def ptsEquivBC : 𝒢.Pts τ ≃ CPt (bc 𝒢 τ) where
  toFun := toBC 𝒢 τ
  invFun := ofBC 𝒢 τ
  left_inv p := by
    apply Over.OverMorphism.ext
    exact toBC_pr 𝒢 τ p
  right_inv P := by
    apply Over.OverMorphism.ext
    show toBCl 𝒢 τ (ofBC 𝒢 τ P) = cptL 𝒢 τ P
    apply pullback.hom_ext
    · rw [toBCl_fst, cpt_fst]
    · rw [toBCl_snd]; rfl

@[simp] theorem toBC_ofBC (P : CPt (bc 𝒢 τ)) : toBC 𝒢 τ (ofBC 𝒢 τ P) = P :=
  (ptsEquivBC 𝒢 τ).right_inv P

@[simp] theorem ofBC_toBC (p : 𝒢.Pts τ) : ofBC 𝒢 τ (toBC 𝒢 τ p) = p :=
  (ptsEquivBC 𝒢 τ).left_inv p

/-! ### Evaluation -/

/-- Functoriality of evaluation, with no domain hypothesis. -/
theorem evS_comp' {Y Z : Scheme} (y : Spec (CommRingCat.of ℂ) ⟶ Y) (f : Y ⟶ Z) (U : Z.Opens)
    (s : Γ(Z, U)) : evS (y ≫ f) U s = evS y (f ⁻¹ᵁ U) (f.app U s) := by
  by_cases h : ⊤ ≤ (y ≫ f) ⁻¹ᵁ U
  · exact evS_comp y f U s h
  · have h' : ¬ ⊤ ≤ y ⁻¹ᵁ (f ⁻¹ᵁ U) := h
    unfold evS
    rw [dite_eq_right h, dite_eq_right h']

/-- Bridge's `XevalAt` is `evS` of the underlying scheme morphism. -/
theorem xevalAt_eq_evS (X : Over (Spec (CommRingCat.of ℂ))) (U : X.left.Opens) (f : Γ(X.left, U))
    (P : CPt X) : XevalAt X U f P = evS P.left U f := by
  unfold XevalAt XPtIn evS
  split_ifs <;> first | rfl | contradiction

theorem xptIn_toBC (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) :
    XPtIn (bc 𝒢 τ) (toBC 𝒢 τ p) (pr 𝒢 τ ⁻¹ᵁ U) ↔ ⊤ ≤ p.left ⁻¹ᵁ U := by
  show ⊤ ≤ (cptL 𝒢 τ (toBC 𝒢 τ p) ≫ pr 𝒢 τ) ⁻¹ᵁ U ↔ _
  rw [toBC_pr]
  exact Iff.rfl

/-- **Evaluation of regular functions is compatible with the comparison**: `(pr^* s)(p_ℂ) = s(p)`. -/
theorem xevalAt_toBC (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) :
    XevalAt (bc 𝒢 τ) (pr 𝒢 τ ⁻¹ᵁ U) ((pr 𝒢 τ).app U s) (toBC 𝒢 τ p) = 𝒢.evalAt p U s := by
  rw [xevalAt_eq_evS, evalAt_eq_evS]
  show evS (toBCl 𝒢 τ p) (pullback.snd (bcBase τ) 𝒢.G.hom ⁻¹ᵁ U)
    ((pullback.snd (bcBase τ) 𝒢.G.hom).app U s) = evS (ptL 𝒢 τ p) U s
  rw [← evS_comp', toBCl_snd]

/-! ### Regular functions of the base change near a point, through regular functions of `𝒢` -/

/-- **Every regular function of the base change is, near each point, a rational function with complex
coefficients of regular functions of `𝒢`**: `σ(x) · (Σ v_j c_j(x))^N = Σ u_j c_j(x)`. (Γ of the affine
open `Spec ℂ ×_{𝓞_L} V = Spec(ℂ ⊗ Γ(V))`, Mathlib's `pullbackSpecIso`; r3prime-etale's
`exists_tensor_formula` with `X = Spec ℂ`, `a = id`.) -/
theorem bc_formula (W : (bc 𝒢 τ).left.Opens) (σ : Γ((bc 𝒢 τ).left, W)) (q : 𝒢.Pts τ)
    (hq : XPtIn _ (toBC 𝒢 τ q) W) :
    ∃ (V : 𝒢.G.left.Opens) (m : ℕ) (c : Fin m → Γ(𝒢.G.left, V)) (u v : Fin m → ℂ) (N : ℕ),
      ⊤ ≤ q.left ⁻¹ᵁ V ∧ ∑ j, v j * 𝒢.evalAt q V (c j) ≠ 0 ∧
      ∀ x : 𝒢.Pts τ, ⊤ ≤ x.left ⁻¹ᵁ V → ∑ j, v j * 𝒢.evalAt x V (c j) ≠ 0 →
        XPtIn _ (toBC 𝒢 τ x) W ∧
        XevalAt _ W σ (toBC 𝒢 τ x) * (∑ j, v j * 𝒢.evalAt x V (c j)) ^ N =
          ∑ j, u j * 𝒢.evalAt x V (c j) := by
  obtain ⟨V, m, c, u, v, N, hV, hd, hall⟩ := exists_tensor_formula
    (bcBase τ) 𝒢.G.hom W σ (𝟙 _) (ptL 𝒢 τ q) (pts_w 𝒢 τ q) hq
  refine ⟨V, m, c, u, v, N, hV, hd, fun x hx hdx => ?_⟩
  obtain ⟨h1, h2⟩ := hall (ptL 𝒢 τ x) (pts_w 𝒢 τ x) hx hdx
  refine ⟨h1, ?_⟩
  rw [xevalAt_eq_evS]
  exact h2

/-- Serre-holomorphic functions are continuous (analytic topology). -/
theorem continuousAt_of_anHolAt {h : 𝒢.Pts τ → ℂ} {q : 𝒢.Pts τ} (hh : AnHolAt 𝒢 τ h q) :
    @ContinuousAt _ _ (anTop 𝒢 τ) _ h q := by
  letI := anTop 𝒢 τ
  obtain ⟨m, U, s, H, hU, hH, hev⟩ := hh
  have hv : ContinuousAt (evalVec 𝒢 τ U s) q :=
    continuousAt_pi.mpr fun j => continuousAt_evalAt 𝒢 τ (U j) (s j) (hU j)
  have hc : ContinuousAt (H ∘ evalVec 𝒢 τ U s) q := hH.self_of_nhds.continuousAt.comp hv
  exact hc.congr (hev.mono fun x hx => hx.symm)

/-- A regular function of the base change, read on `𝒢.Pts τ`, is Serre-holomorphic (for `𝒢`). -/
theorem anHolAt_bc (W : (bc 𝒢 τ).left.Opens) (σ : Γ((bc 𝒢 τ).left, W)) (q : 𝒢.Pts τ)
    (hq : XPtIn _ (toBC 𝒢 τ q) W) :
    AnHolAt 𝒢 τ (fun x => XevalAt _ W σ (toBC 𝒢 τ x)) q ∧
      ∀ᶠ x in @nhds _ (anTop 𝒢 τ) q, XPtIn _ (toBC 𝒢 τ x) W := by
  letI := anTop 𝒢 τ
  obtain ⟨V, m, c, u, v, N, hb₀, hden₀, hall⟩ := bc_formula 𝒢 τ W σ q hq
  let num : (Fin m → ℂ) → ℂ := fun z => ∑ j, u j * z j
  let den : (Fin m → ℂ) → ℂ := fun z => ∑ j, v j * z j
  have hden : Continuous den :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hnumd : Differentiable ℂ num := fun z =>
    DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul (differentiableAt_apply j z)
  have hdend : Differentiable ℂ den := fun z =>
    DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul (differentiableAt_apply j z)
  have h0 : den (evalVec 𝒢 τ (fun _ => V) c q) ≠ 0 := hden₀
  have hcont : ContinuousAt (fun x => evalVec 𝒢 τ (fun _ => V) c x) q :=
    continuousAt_pi.mpr fun j => continuousAt_evalAt 𝒢 τ V (c j) hb₀
  have hnear : ∀ᶠ x in 𝓝 q, ⊤ ≤ x.left ⁻¹ᵁ V ∧ den (evalVec 𝒢 τ (fun _ => V) c x) ≠ 0 := by
    filter_upwards [(R3Etale.isOpen_ptsIn 𝒢 τ V).mem_nhds hb₀,
      (hden.continuousAt.comp hcont).eventually (isOpen_ne.mem_nhds h0)] with x hxV hxd
    exact ⟨hxV, hxd⟩
  refine ⟨⟨m, fun _ => V, c, fun z => num z / den z ^ N, fun _ => hb₀, ?_, ?_⟩, ?_⟩
  · filter_upwards [hden.continuousAt.eventually (isOpen_ne.mem_nhds h0)] with z hz
    have hp : DifferentiableAt ℂ (fun w => den w ^ N) z := (hdend z).pow N
    have hq := (hnumd z).mul (hp.inv (pow_ne_zero N hz))
    have hfun : (fun z => num z / den z ^ N) = num * (fun w => den w ^ N)⁻¹ := by
      funext w; simp [div_eq_mul_inv]
    rw [hfun]; exact hq
  · filter_upwards [hnear] with x hx
    obtain ⟨-, h2⟩ := hall x hx.1 hx.2
    exact eq_div_of_mul_eq (pow_ne_zero N hx.2) h2
  · filter_upwards [hnear] with x hx
    exact (hall x hx.1 hx.2).1

/-! ### The analytic topology is the classical topology of the base change -/

/-- `{P ∈ U(ℂ) | f(P) ∈ V}` is open for the classical topology (through Bridge's
`classicalTopology_eq`). -/
theorem isOpen_evalSet (X : Over (Spec (CommRingCat.of ℂ))) (U : X.left.Opens) (f : Γ(X.left, U))
    {V : Set ℂ} (hV : IsOpen V) :
    IsOpen[classicalTopology X] {P | XPtIn X P U ∧ XevalAt X U f P ∈ V} := by
  rw [classicalTopology_eq, isOpen_induced_iff]
  refine ⟨AlgebraicGeometry.Point.overOpen U ∩ AlgebraicGeometry.Point.evaluate U f ⁻¹' V, ?_, ?_⟩
  · rw [AlgebraicGeometry.Point.analyticTopology_eq_generateFrom]
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f, V, hV, rfl⟩
  · ext P
    simp only [mem_preimage, mem_inter_iff, AlgebraicGeometry.Point.overOpen, mem_ofPred_eq]
    rw [xevalAt_eq_evaluate, ptIn_iff]

/-- **`anTop` is the classical topology of `(𝒢 ×_τ ℂ)(ℂ)`**, transported along the comparison. -/
theorem anTop_eq_induced :
    anTop 𝒢 τ = TopologicalSpace.induced (toBC 𝒢 τ) (classicalTopology (bc 𝒢 τ)) := by
  apply le_antisymm
  · show anTop 𝒢 τ ≤ TopologicalSpace.induced _ (TopologicalSpace.generateFrom (basicSets _))
    rw [induced_generateFrom_eq]
    apply le_generateFrom
    rintro _ ⟨S, ⟨W, σ, z, ε, rfl⟩, rfl⟩
    letI := anTop 𝒢 τ
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨hqW, hqz⟩
    obtain ⟨hhol, hW⟩ := anHolAt_bc 𝒢 τ W σ q hqW
    have hc := continuousAt_of_anHolAt 𝒢 τ hhol
    have h2 : ∀ᶠ x in 𝓝 q, ‖XevalAt _ W σ (toBC 𝒢 τ x) - z‖ < ε :=
      Filter.Tendsto.eventually_lt_const hqz (hc.sub continuousAt_const).norm
    filter_upwards [hW, h2] with x h1 h2'
    exact ⟨h1, h2'⟩
  · show TopologicalSpace.induced _ _ ≤ TopologicalSpace.generateFrom _
    apply le_generateFrom
    rintro _ ⟨U, s, V, hV, rfl⟩
    rw [isOpen_induced_iff]
    refine ⟨_, isOpen_evalSet (bc 𝒢 τ) (pr 𝒢 τ ⁻¹ᵁ U) ((pr 𝒢 τ).app U s) hV, ?_⟩
    ext p
    simp only [mem_preimage, mem_ofPred_eq]
    rw [xptIn_toBC, xevalAt_toBC]

/-- **(1) The comparison homeomorphism** `(𝒢.Pts τ, anTop) ≃ₜ ((𝒢 ×_τ ℂ)(ℂ), classical topology)`,
compatible with evaluation of regular functions (`xevalAt_toBC`). -/
noncomputable def ptsHomeomorph :
    @Homeomorph (𝒢.Pts τ) (CPt (bc 𝒢 τ)) (anTop 𝒢 τ) (classicalTopology _) :=
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  (ptsEquivBC 𝒢 τ).toHomeomorphOfIsInducing ⟨anTop_eq_induced 𝒢 τ⟩

theorem ptsHomeomorph_apply (p : 𝒢.Pts τ) : ptsHomeomorph 𝒢 τ p = toBC 𝒢 τ p := rfl

theorem ptsHomeomorph_symm_apply (P : CPt (bc 𝒢 τ)) : (ptsHomeomorph 𝒢 τ).symm P = ofBC 𝒢 τ P := rfl

/-- Composite with Bridge's `cptHomeomorph`: the points with `anTop` are the vendored port's
`ℂ`-points of the base change with their analytic topology. -/
noncomputable def ptsHomeomorphPort :
    @Homeomorph (𝒢.Pts τ) (AlgebraicGeometry.Point ℂ (bc 𝒢 τ)) (anTop 𝒢 τ)
      AlgebraicGeometry.Point.analyticTopology :=
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  (ptsHomeomorph 𝒢 τ).trans (cptHomeomorph (bc 𝒢 τ))

/-- The vendored complex-manifold atlas of a smooth `ℂ`-scheme, transported to `(𝒢.Pts τ, anTop)`. -/
noncomputable def chartedSpacePts (d : ℕ) [SmoothOfRelativeDimension d (bc 𝒢 τ).hom] :
    @ChartedSpace (Fin d → ℂ) _ (𝒢.Pts τ) (anTop 𝒢 τ) :=
  letI := chartedSpace (bc 𝒢 τ) d
  (ptsHomeomorph 𝒢 τ).symm.chartedSpace

theorem eventually_nhds_toBC (q : 𝒢.Pts τ) (P : CPt (bc 𝒢 τ) → Prop) :
    (∀ᶠ Q in @nhds _ (classicalTopology _) (toBC 𝒢 τ q), P Q) ↔
      ∀ᶠ x in @nhds _ (anTop 𝒢 τ) q, P (toBC 𝒢 τ x) := by
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  rw [← ptsHomeomorph_apply, ← (ptsHomeomorph 𝒢 τ).map_nhds_eq q]
  rfl

end BaseChange

/-! ## §2. Serre's sheaf of the base change, and the comparison -/

/-- **Serre's sheaf of holomorphic functions of the complex space `X(ℂ)^an`** of a `ℂ`-scheme `X`
(Serre, GAGA §2; SGA 1 XII 1.1; UNVERIFIED numbering): `h` is holomorphic at `P` when, near `P` in the
classical topology, `h = H(s₁, …, s_m)` for regular functions `s_j ∈ Γ(U_j, 𝒪_X)` with `P ∈ U_j(ℂ)` and
`H` holomorphic near `(s_j(P))_j`. Regular functions of `X` itself, the `ℂ`-scheme. -/
def BCHolAt (X : Over (Spec (CommRingCat.of ℂ))) (h : CPt X → ℂ) (P : CPt X) : Prop :=
  ∃ (m : ℕ) (U : Fin m → X.left.Opens) (s : ∀ j, Γ(X.left, U j)) (H : (Fin m → ℂ) → ℂ),
    (∀ j, XPtIn X P (U j)) ∧
    (∀ᶠ y in 𝓝 (fun j => XevalAt X (U j) (s j) P), DifferentiableAt ℂ H y) ∧
    ∀ᶠ Q in @nhds _ (classicalTopology X) P, h Q = H (fun j => XevalAt X (U j) (s j) Q)

section Comparison

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L) (τ : L →+* ℂ)

/-- **(2) The base-change sheaf comparison.** Under the comparison homeomorphism, Serre's sheaf of
`𝒢 ×_τ ℂ` (from its own regular functions) is r3prime-etale's `AnHolAt` (from regular functions of the
model `𝒢` over `𝓞_L`). -/
theorem bcHolAt_iff (k : CPt (bc 𝒢 τ) → ℂ) (q : 𝒢.Pts τ) :
    BCHolAt (bc 𝒢 τ) k (toBC 𝒢 τ q) ↔ AnHolAt 𝒢 τ (k ∘ toBC 𝒢 τ) q := by
  constructor
  · rintro ⟨n, W, σ, H, hW, hH, hev⟩
    letI := anTop 𝒢 τ
    have hi : ∀ j, AnHolAt 𝒢 τ (fun x => (fun i => XevalAt _ (W i) (σ i) (toBC 𝒢 τ x)) j) q :=
      fun j => (anHolAt_bc 𝒢 τ (W j) (σ j) q (hW j)).1
    obtain ⟨m, U, s, H', hU, hH', hev'⟩ := anHolAt_pi 𝒢 τ hi
    have hy0 : H' (evalVec 𝒢 τ U s q) = fun j => XevalAt _ (W j) (σ j) (toBC 𝒢 τ q) :=
      hev'.self_of_nhds.symm
    refine ⟨m, U, s, H ∘ H', hU, ?_, ?_⟩
    · have hc : ContinuousAt H' (evalVec 𝒢 τ U s q) := hH'.self_of_nhds.continuousAt
      have hH2 : ∀ᶠ y in 𝓝 (evalVec 𝒢 τ U s q), DifferentiableAt ℂ H (H' y) := by
        rw [← hy0] at hH
        exact hc.eventually hH
      filter_upwards [hH', hH2] with y h1 h2
      exact h2.comp y h1
    · have hev2 := (eventually_nhds_toBC 𝒢 τ q _).mp hev
      filter_upwards [hev2, hev'] with x h1 h2
      simp only [Function.comp_apply]
      rw [h1, ← h2]
  · rintro ⟨m, U, s, H, hU, hH, hev⟩
    refine ⟨m, fun j => pr 𝒢 τ ⁻¹ᵁ U j, fun j => (pr 𝒢 τ).app (U j) (s j), H,
      fun j => (xptIn_toBC 𝒢 τ q (U j)).mpr (hU j), ?_, ?_⟩
    · have : (fun j => XevalAt _ (pr 𝒢 τ ⁻¹ᵁ U j) ((pr 𝒢 τ).app (U j) (s j)) (toBC 𝒢 τ q)) =
          evalVec 𝒢 τ U s q := funext fun j => xevalAt_toBC 𝒢 τ q (U j) (s j)
      rw [this]; exact hH
    · rw [eventually_nhds_toBC]
      filter_upwards [hev] with x hx
      have : (fun j => XevalAt _ (pr 𝒢 τ ⁻¹ᵁ U j) ((pr 𝒢 τ).app (U j) (s j)) (toBC 𝒢 τ x)) =
          evalVec 𝒢 τ U s x := funext fun j => xevalAt_toBC 𝒢 τ x (U j) (s j)
      rw [this]; exact hx

/-- (2), read on `𝒢.Pts τ`: `AnHolAt h q ↔` the transported function is holomorphic on the complex
space of the base change. -/
theorem anHolAt_iff_bcHolAt (h : 𝒢.Pts τ → ℂ) (q : 𝒢.Pts τ) :
    AnHolAt 𝒢 τ h q ↔ BCHolAt (bc 𝒢 τ) (h ∘ ofBC 𝒢 τ) (toBC 𝒢 τ q) := by
  rw [bcHolAt_iff]
  have : (h ∘ ofBC 𝒢 τ) ∘ toBC 𝒢 τ = h := funext fun x => by simp
  rw [this]

end Comparison

/-! ## §3. Charts: Serre charts of the base change; unit-germ charts -/

/-- **`φ` is a chart of the complex space `(X(ℂ), 𝒪_X^an)`** of a `ℂ`-scheme `X`: a homeomorphism from
an open subset of `X(ℂ)` (classical topology) onto an open subset of `ℂ^g` that is an isomorphism of
ringed spaces onto its image (Serre's sheaf `BCHolAt`). -/
def IsBCSerreChart (X : Over (Spec (CommRingCat.of ℂ))) {g : ℕ}
    (φ : @OpenPartialHomeomorph (CPt X) (Fin g → ℂ) (classicalTopology X) _) : Prop :=
  letI := classicalTopology X
  ∀ P ∈ φ.source, ∀ h : CPt X → ℂ,
    BCHolAt X h P ↔ ∀ᶠ y in 𝓝 (φ P), DifferentiableAt ℂ (h ∘ φ.symm) y

section Charts

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L) (τ : L →+* ℂ)

/-- A chart of the base change, pulled back to `𝒢.Pts τ`. -/
noncomputable def pullChart {g : ℕ}
    (φ : @OpenPartialHomeomorph (CPt (bc 𝒢 τ)) (Fin g → ℂ) (classicalTopology _) _) :
    @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _ :=
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  (ptsHomeomorph 𝒢 τ).toOpenPartialHomeomorph.trans φ

/-- A chart of `𝒢.Pts τ`, pushed to the base change. -/
noncomputable def pushChart {g : ℕ}
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    @OpenPartialHomeomorph (CPt (bc 𝒢 τ)) (Fin g → ℂ) (classicalTopology _) _ :=
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  (ptsHomeomorph 𝒢 τ).symm.toOpenPartialHomeomorph.trans φ

theorem pullChart_pushChart {g : ℕ}
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    pullChart 𝒢 τ (pushChart 𝒢 τ φ) = φ := by
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  apply OpenPartialHomeomorph.ext
  · intro x; simp [pullChart, pushChart]
  · intro y; simp [pullChart, pushChart]
  · ext x; simp [pullChart, pushChart]

theorem isSerreChart_pullChart_iff {g : ℕ}
    (φ : @OpenPartialHomeomorph (CPt (bc 𝒢 τ)) (Fin g → ℂ) (classicalTopology _) _) :
    IsSerreChart 𝒢 τ (pullChart 𝒢 τ φ) ↔ IsBCSerreChart (bc 𝒢 τ) φ := by
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  have hsrc : ∀ q, q ∈ (pullChart 𝒢 τ φ).source ↔ toBC 𝒢 τ q ∈ φ.source := fun q => by
    simp [pullChart, ptsHomeomorph_apply]
  have happ : ∀ q, pullChart 𝒢 τ φ q = φ (toBC 𝒢 τ q) := fun q => rfl
  have hsymm : ∀ (h : 𝒢.Pts τ → ℂ), h ∘ (pullChart 𝒢 τ φ).symm = (h ∘ ofBC 𝒢 τ) ∘ φ.symm :=
    fun h => rfl
  constructor
  · intro H P hP k
    have hq : ofBC 𝒢 τ P ∈ (pullChart 𝒢 τ φ).source := by rw [hsrc]; simpa using hP
    have := H _ hq (k ∘ toBC 𝒢 τ)
    rw [happ, toBC_ofBC, hsymm] at this
    rw [← toBC_ofBC 𝒢 τ P, bcHolAt_iff, toBC_ofBC]
    have hk : (k ∘ toBC 𝒢 τ) ∘ ofBC 𝒢 τ = k := funext fun P => by simp
    rw [hk] at this
    exact this
  · intro H q hq h
    rw [hsrc] at hq
    rw [anHolAt_iff_bcHolAt, H _ hq, happ, hsymm]

/-- **(4) R3′ with the genuine complex space of the base change on the Serre side.** For `g = dim A`, a
chart `φ` of `(𝒢.Pts τ, anTop)` is an `IsHolChart` chart iff, transported along the comparison
homeomorphism, it is a chart of Serre's complex space `((𝒢 ×_τ ℂ)(ℂ), 𝒪^an)`, built from the regular
functions of the base change. From T35 alone. -/
theorem isHolChart_iff_isBCSerreChart (hT35 : ZInQ.LeafPush2.UniformizationExists) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞))
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    IsHolChart 𝒢 τ φ ↔ IsBCSerreChart (bc 𝒢 τ) (pushChart 𝒢 τ φ) := by
  rw [isHolChart_iff_isSerreChart' hT35 𝒢 g hg τ φ, ← isSerreChart_pullChart_iff,
    pullChart_pushChart]

/-- (4), for charts given on the base change. -/
theorem isBCSerreChart_iff_isHolChart (hT35 : ZInQ.LeafPush2.UniformizationExists) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞))
    (φ : @OpenPartialHomeomorph (CPt (bc 𝒢 τ)) (Fin g → ℂ) (classicalTopology _) _) :
    IsBCSerreChart (bc 𝒢 τ) φ ↔ IsHolChart 𝒢 τ (pullChart 𝒢 τ φ) := by
  rw [isHolChart_iff_isSerreChart' hT35 𝒢 g hg τ, isSerreChart_pullChart_iff]

/-- Serre charts of the complex space of the base change exist at every point (T35). -/
theorem exists_bcSerreChart_at (hT35 : ZInQ.LeafPush2.UniformizationExists) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) (P : CPt (bc 𝒢 τ)) :
    letI := classicalTopology (bc 𝒢 τ)
    ∃ φ : OpenPartialHomeomorph (CPt (bc 𝒢 τ)) (Fin g → ℂ), P ∈ φ.source ∧ IsBCSerreChart (bc 𝒢 τ) φ := by
  letI := anTop 𝒢 τ
  letI := classicalTopology (bc 𝒢 τ)
  obtain ⟨φ, hp, hφ⟩ := exists_holChart_at hT35 𝒢 g hg τ (ofBC 𝒢 τ P)
  refine ⟨pushChart 𝒢 τ φ, ?_, (isHolChart_iff_isBCSerreChart 𝒢 τ hT35 g hg φ).mp hφ⟩
  simpa [pushChart, ptsHomeomorph_symm_apply] using hp

/-- **(3) The unit-germ charts through the comparison.** Each coordinate of the translated algebraic
chart `ZInQ.HeightFix.chartAt 𝒢 τ U s q` (`PrintedStableHeight.lean`), read on the base change, is holomorphic for
Serre's sheaf of `𝒢 ×_τ ℂ` at every point of its domain. -/
theorem bcHolAt_chartAt {g : ℕ} (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i))
    (q : 𝒢.Pts τ) (P : CPt (bc 𝒢 τ)) (i : Fin g)
    (hP : ⊤ ≤ (q⁻¹ * ofBC 𝒢 τ P).left ⁻¹ᵁ U i) :
    BCHolAt (bc 𝒢 τ) (fun P => ZInQ.HeightFix.chartAt 𝒢 τ U s q (ofBC 𝒢 τ P) i) P := by
  rw [← toBC_ofBC 𝒢 τ P, bcHolAt_iff]
  have : (fun P => ZInQ.HeightFix.chartAt 𝒢 τ U s q (ofBC 𝒢 τ P) i) ∘ toBC 𝒢 τ =
      fun x => 𝒢.evalAt (q⁻¹ * x) (U i) (s i) := funext fun x => by
    simp [ZInQ.HeightFix.chartAt, coordMap]
  rw [this]
  exact translationAnHol K A L 𝒢 τ (U i) (s i) q⁻¹ (ofBC 𝒢 τ P) hP

/-- (3), the charts: the `IsHolChart` atlas (`exists_holChart_at`), in which the translated unit-germ
coordinates are holomorphic with invertible derivative, pushed to the base change, consists of Serre
charts of `((𝒢 ×_τ ℂ)(ℂ), 𝒪^an)`; and the unit-germ chart coordinates centred at `q` are Serre
holomorphic there at `toBC q`. -/
theorem unitGermChart_bc (hT35 : ZInQ.LeafPush2.UniformizationExists) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞))
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) (hφ : IsHolChart 𝒢 τ φ)
    (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hone : ∀ i, ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U i) (q : 𝒢.Pts τ) :
    IsBCSerreChart (bc 𝒢 τ) (pushChart 𝒢 τ φ) ∧
      ∀ i, BCHolAt (bc 𝒢 τ) (fun P => ZInQ.HeightFix.chartAt 𝒢 τ U s q (ofBC 𝒢 τ P) i) (toBC 𝒢 τ q) := by
  refine ⟨(isHolChart_iff_isBCSerreChart 𝒢 τ hT35 g hg φ).mp hφ, fun i => ?_⟩
  refine bcHolAt_chartAt 𝒢 τ U s q _ i ?_
  rw [ofBC_toBC, inv_mul_cancel]
  exact hone i

end Charts

end ZInQ.R3BC
