import ZInQKernel.OneProof.H.TailU

/-!
# shimura-split, Part 4: `ShimuraFamily` (row shimuraFamily) from Shimura's holomorphic family

The row `HDec.QMSplit.Moduli.ShimuraFamily` asks, on one fine witness `(Y, Φ)`, for every algebraic
`π : Y → P¹` a family `τ ↦ y_τ ∈ Y(ℂ)` with the moduli clause (the object at `y_τ` is `ℂ²/ι(𝒪)(τ,1)ᵀ`) and
`τ ↦ π(y_τ)` continuous and holomorphic into `P¹(ℂ)`. qm-split flagged it as Shimura's Main Theorem I
**plus** a GAGA-level step (an algebraic map composed with a holomorphic family is holomorphic).

Here Shimura's statement is a leaf in its own form: **one** family `τ ↦ y_τ` (independent of `π`) with the
moduli clause which is *holomorphic*, where "holomorphic map `ℍ → Y(ℂ)`" is the standard notion written
with the regular functions of `Y`: preimages of Zariski opens are open, and every regular function on a
Zariski open pulls back to a holomorphic function (`IsHolFamily`). The step to every `π : Y → P¹` is proved
in Lean (`ShimuraSplit.holP1_of_isHolFamily`): it only uses the two charts of `π`.
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits Filter Topology
open LeafQM.AV

variable {X : Scheme.{0}}

/-- The point of `X` under a `ℂ`-point. -/
abbrev ptC (y : Spec (CommRingCat.of ℂ) ⟶ X) : X := (Scheme.SpecToEquivOfField ℂ X y).1

open Classical in
/-- The value `f(y) ∈ ℂ` of a regular function `f ∈ Γ(X, U)` at a `ℂ`-point `y` whose point lies in `U`
(the image of `f(x) ∈ κ(x)` under the embedding `κ(x) → ℂ` of `y`), and `0` otherwise. -/
def regVal (U : X.Opens) (f : Γ(X, U)) (y : Spec (CommRingCat.of ℂ) ⟶ X) : ℂ :=
  if h : ptC y ∈ U then (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation U _ h f) else 0

/-- **A holomorphic map `ℍ → X(ℂ)`**, written with the regular functions of `X`: the preimage of every
Zariski open is open, and every regular function on a Zariski open `U` pulls back to a function holomorphic
(analytic) on the preimage of `U`. For a variety this is the usual notion (an affine open embeds in `ℂ^n`
by finitely many regular functions, and the analytic topology is the one induced from `ℂ^n`). -/
def IsHolFamily (φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)) : Prop :=
  (∀ U : X.Opens, IsOpen {τ | ptC (φ τ) ∈ U}) ∧
  ∀ (U : X.Opens) (f : Γ(X, U)) (τ : UpperHalfPlane), ptC (φ τ) ∈ U →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, regVal U f (φ ⟨z, hz⟩) = g z

/-! ## The two charts of `π` -/

theorem val_of_mem (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X) (h : ptC y ∈ π.U) :
    π.val y = ((regVal π.U π.f y : ℂ) : OnePoint ℂ) := by
  unfold ToP1.val regVal
  rw [dif_pos h, dif_pos h]

theorem eval_res {U U' : X.Opens} (i : U' ⟶ U) (x : X) (hx : x ∈ U') (f : Γ(X, U)) :
    X.evaluation U' x hx (X.presheaf.map i.op f) = X.evaluation U x (i.le hx) f := by
  simp only [Scheme.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

theorem val_of_memV (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X) (hV : ptC y ∈ π.V) :
    π.val y = if regVal π.V π.g y = 0 then OnePoint.infty
      else (((regVal π.V π.g y)⁻¹ : ℂ) : OnePoint ℂ) := by
  have hreg : regVal π.V π.g y =
      (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation π.V (ptC y) hV π.g) := by
    unfold regVal; rw [dif_pos hV]
  rw [hreg]
  by_cases hg : X.evaluation π.V (ptC y) hV π.g = 0
  · have hxU : ptC y ∉ π.U := by
      intro hU
      have := (Scheme.evaluation_eq_zero_iff_notMem_basicOpen X (ptC y) hV π.g).1 hg
      rw [π.basicOpen_g] at this
      exact this ⟨hU, hV⟩
    rw [hg, map_zero, if_pos rfl]
    unfold ToP1.val
    rw [dif_neg hxU]
  · have hmem : ptC y ∈ X.basicOpen π.g :=
      (Scheme.evaluation_ne_zero_iff_mem_basicOpen X (ptC y) hV π.g).1 hg
    rw [π.basicOpen_g] at hmem
    have hU : ptC y ∈ π.U := hmem.1
    have hι0 : (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation π.V (ptC y) hV π.g) ≠ 0 := by
      intro h0
      exact hg ((Scheme.SpecToEquivOfField ℂ X y).2.hom.injective (h0.trans (map_zero _).symm))
    rw [if_neg hι0]
    unfold ToP1.val
    rw [dif_pos hU]
    congr 1
    have hinv := congrArg (X.evaluation (π.U ⊓ π.V) (ptC y) hmem) π.inv
    rw [map_mul, map_one, eval_res, eval_res] at hinv
    have h2 := congrArg (Scheme.SpecToEquivOfField ℂ X y).2 hinv
    rw [map_mul, map_one] at h2
    exact eq_inv_of_mul_eq_one_left h2

/-! ## Topology on `ℍ` versus `ℂ` -/

theorem eventually_of_complex {P : UpperHalfPlane → Prop} {τ : UpperHalfPlane}
    (h : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩) : ∀ᶠ σ in 𝓝 τ, P σ :=
  ((UpperHalfPlane.continuous_coe.tendsto τ).eventually h).mono fun σ hσ => hσ σ.im_pos

theorem complex_of_eventually {P : UpperHalfPlane → Prop} {τ : UpperHalfPlane}
    (h : ∀ᶠ σ in 𝓝 τ, P σ) : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩ := by
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq τ, Filter.eventually_map]
  exact h.mono fun σ hσ hz => hσ

/-- `w ↦ 1/w` as a map `ℂ → P¹(ℂ)` (`0 ↦ ∞`) is continuous at `0`. -/
theorem tendsto_invP1 :
    Tendsto (fun w : ℂ => if w = 0 then (OnePoint.infty : OnePoint ℂ) else ((w⁻¹ : ℂ) : OnePoint ℂ))
      (𝓝 0) (𝓝 OnePoint.infty) := by
  rw [← nhdsNE_sup_pure (0 : ℂ)]
  refine Tendsto.sup ?_ ?_
  · have h1 : Tendsto (fun w : ℂ => ((w⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 OnePoint.infty) := by
      have hc := OnePoint.tendsto_coe_infty (X := ℂ)
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at hc
      exact hc.comp tendsto_inv₀_nhdsNE_zero
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (if_neg hw).symm
  · rw [tendsto_pure_left]
    intro s hs
    rw [if_pos rfl]
    exact mem_of_mem_nhds hs

/-! ## The GAGA-level step: every `π : X → P¹` composed with a holomorphic family -/

/-- **For a holomorphic family `φ` and every `π : X → P¹` (by charts), `τ ↦ π(φ τ)` is continuous and
holomorphic into `P¹(ℂ)` at every point.** -/
theorem holP1_of_isHolFamily (π : ToP1 X) {φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)}
    (hφ : IsHolFamily φ) :
    Continuous (fun τ => π.val (φ τ)) ∧
      ∀ τ, HDec.HSyn.G0Split.FibreQM.IsHolP1At (fun τ => π.val (φ τ)) τ := by
  obtain ⟨hopen, hhol⟩ := hφ
  -- the local description at each `τ`
  have key : ∀ τ : UpperHalfPlane,
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, π.val (φ ⟨z, hz⟩) = ((g z : ℂ) : OnePoint ℂ)) ∨
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
        ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im,
          π.val (φ ⟨z, hz⟩) = if g z = 0 then OnePoint.infty else (((g z)⁻¹ : ℂ) : OnePoint ℂ)) := by
    intro τ
    by_cases hU : ptC (φ τ) ∈ π.U
    · left
      obtain ⟨g, hg, hev⟩ := hhol π.U π.f τ hU
      have hU' := complex_of_eventually (P := fun σ => ptC (φ σ) ∈ π.U)
        ((hopen π.U).mem_nhds hU)
      refine ⟨g, hg, ?_⟩
      filter_upwards [hev, hU'] with z h1 h2 hz
      rw [val_of_mem π _ (h2 hz), h1 hz]
    · right
      have hV : ptC (φ τ) ∈ π.V := by
        have : ptC (φ τ) ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
        rcases (TopologicalSpace.Opens.mem_sup).1 this with h | h
        · exact absurd h hU
        · exact h
      obtain ⟨g, hg, hev⟩ := hhol π.V π.g τ hV
      have hV' := complex_of_eventually (P := fun σ => ptC (φ σ) ∈ π.V)
        ((hopen π.V).mem_nhds hV)
      refine ⟨g, hg, ?_, ?_⟩
      · have h0 := hev.self_of_nhds τ.im_pos
        rw [← h0]
        have hτ : (⟨(τ : ℂ), τ.im_pos⟩ : UpperHalfPlane) = τ := rfl
        rw [hτ]
        unfold regVal
        rw [dif_pos hV]
        have hnot : ptC (φ τ) ∉ X.basicOpen π.g := by
          rw [π.basicOpen_g]; exact fun h => hU h.1
        rw [(Scheme.evaluation_eq_zero_iff_notMem_basicOpen X _ hV π.g).2 hnot, map_zero]
      · filter_upwards [hev, hV'] with z h1 h2 hz
        rw [val_of_memV π _ (h2 hz), h1 hz]
  refine ⟨continuous_iff_continuousAt.2 fun τ => ?_, fun τ => key τ⟩
  rcases key τ with ⟨g, hg, hev⟩ | ⟨g, hg, hg0, hev⟩
  · have hc : ContinuousAt (fun σ : UpperHalfPlane => ((g σ : ℂ) : OnePoint ℂ)) τ :=
      OnePoint.continuous_coe.continuousAt.comp
        (hg.continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt)
    exact hc.congr (eventually_of_complex (P := fun σ => ((g σ : ℂ) : OnePoint ℂ) = π.val (φ σ))
      (hev.mono fun z hz hz' => (hz hz').symm))
  · have hc : ContinuousAt (fun σ : UpperHalfPlane =>
        if g σ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g σ)⁻¹ : ℂ) : OnePoint ℂ)) τ := by
      have ht := hg.continuousAt.comp (UpperHalfPlane.continuous_coe.continuousAt (x := τ))
      unfold ContinuousAt at ht ⊢
      have hgτ : (g ∘ (fun σ : UpperHalfPlane => (σ : ℂ))) τ = 0 := hg0
      rw [hgτ] at ht
      have hval : (if g τ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g τ)⁻¹ : ℂ) : OnePoint ℂ)) =
          OnePoint.infty := by rw [if_pos hg0]
      dsimp only
      rw [hval]
      exact tendsto_invP1.comp ht
    exact hc.congr (eventually_of_complex
      (P := fun σ => (if g σ = 0 then (OnePoint.infty : OnePoint ℂ) else (((g σ)⁻¹ : ℂ) : OnePoint ℂ)) =
        π.val (φ σ))
      (hev.mono fun z hz hz' => (hz hz').symm))

end ShimuraSplit

namespace HDec

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex

/-- **Shimura's holomorphic family on a witness** (the moduli clause of `IsR1bFamily`, copied verbatim, and
holomorphy of `τ ↦ y_τ` in the sense of `ShimuraSplit.IsHolFamily`; no map to `P¹` involved). -/
def IsShimuraHolFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu) ∧
  ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (yτ τ).left)

/-- **The GAGA-level step, proved**: a holomorphic family with the moduli clause is an `R1bFamily` family for
every `π : Y → P¹`. -/
theorem isR1bFamily_of_hol {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)} (h : IsShimuraHolFamily Y Φ yτ) (π : ToP1 Y.left) :
    IsR1bFamily Y Φ π yτ :=
  ⟨h.1, ShimuraSplit.holP1_of_isHolFamily π h.2⟩

end FibreQM

end G0Split

end HSyn

end HDec

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF (Shimura's complex uniformization of the canonical model, Main Theorem I).**

*Published statement* (Shimura, Ann. of Math. 85 (1967), Main Theorem I; Deligne, Sém. Bourbaki 389 (1971),
§4.15; locators UNVERIFIED, no network): the canonical model `V` of `Γ\ℍ` carries a holomorphic map
`φ : ℍ → V(ℂ)` whose value at `τ` is the moduli point of `ℂ²/ι(𝒪)(τ, 1)ᵀ` (with its `ι` and level
structure).

*Lean form*: some fine witness `(Y, Φ)` (the canonical model `Y₃`) has `τ ↦ y_τ ∈ Y(ℂ)` with the object at
`y_τ` equal (by an `ι`-compatible analytic uniformization with kernel `Λ_τ = ι(𝒪)(τ,1)ᵀ`) to `ℂ²/Λ_τ`, and
`τ ↦ y_τ` holomorphic (`ShimuraSplit.IsHolFamily`: preimages of Zariski opens are open and regular
functions pull back to holomorphic functions, the standard notion for maps into the complex points of a
variety).

*Form*: published form (Main Thm I is a statement about one holomorphic `φ`, as here). The row's "for
every `π : Y → P¹`" is derived (`isR1bFamily_of_hol`), so the flagged GAGA-level composition step is no
longer part of the leaf. Lemma QP (polarizations) as for `R1fp`. -/
def ShimuraHolFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ

/-- **Row `shimuraFamily` from Shimura's holomorphic family.** -/
theorem shimuraFamily_of_hol (h : ShimuraHolFamily) : ShimuraFamily := by
  obtain ⟨Y, Φ, h1, yτ, hy⟩ := h
  exact ⟨Y, Φ, h1, fun π => ⟨yτ, HSyn.G0Split.FibreQM.isR1bFamily_of_hol hy π⟩⟩

end HDec.QMSplit.Moduli

#print axioms ShimuraSplit.holP1_of_isHolFamily
#print axioms HDec.QMSplit.Moduli.shimuraFamily_of_hol
