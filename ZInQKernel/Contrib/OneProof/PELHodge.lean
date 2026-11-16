import ZInQKernel.Contrib.OneProof.HolFamilyPrinted
import ZInQKernel.Contrib.OneProof.UniformizationPrinted

/-!
# pel-hodge: the PEL family with its fibres in Hodge / `H₁` form

Task pel-hodge (2026-11-16). Report: `docs/research/pel-hodge.md`; log: `scratch/pel-hodge/log.md`.

holfam's leaf `HolFamilyPrinted.PELHolFamily` describes the fibre of Deligne's universal QM abelian scheme over
`[τ, 1] ∈ M_{K₃}(ℂ)` in lattice coordinates: an `ι`-compatible analytic uniformization `ℂ² → A(ℂ)` with kernel
`Λ_τ = ι(𝒪)(τ, 1)ᵀ`. The prints (Deligne, Sém. Bourbaki 389, §4; Milne, *Introduction to Shimura varieties*, §§8,
14) describe it in Hodge / `H₁` form instead: the fibre at `[h, g]` is the abelian variety whose `H₁(A, ℤ)`, with its
`𝒪`-action and its Hodge structure (the complex structure of `H₁(A, ℝ) = Lie A`), is `(gL, h)`; here `L = 𝒪`, `g = 1`
and `h = h_τ` is the complex structure that makes `x ↦ ι(x)(τ, 1)ᵀ` a `ℂ`-linear map `B ⊗ ℝ → ℂ²`. Passing to lattice
coordinates is Riemann's `A(ℂ) = Lie A / H₁(A, ℤ)`, i.e. the complex uniformization.

This file states the leaf in the print's form, `PELHolFamilyHodge`, and proves holfam's lattice form from it with the
textbook field `UniformizationLeafAll` (which unif-printed / unif-topology prove from Mumford's printed complex-torus
theorem over the analytic topology). `gagaMorphism` is not needed.

**The `H₁` form, over genuine definitions.**
* `A(ℂ)` carries unif-printed's classical topology `UnifPrinted.classicalTopology` (the coarsest topology in which
  every `U(ℂ)` is open and every regular function is continuous; unif-topology's
  `classicalTopology_eq_analyticTopology` identifies it with the textbook analytic topology).
* `H1 A := π₁(A(ℂ), 0)ᵃᵇ` (Mathlib's `FundamentalGroup` and `Abelianization`): `H₁(A(ℂ), ℤ)` by Hurewicz.
* `H1Form A Λ e` says: `e : ℂⁿ → A(ℂ)` is a holomorphic homomorphism (`IsAnalyticHom`), so `e = exp_A ∘ L` for a
  `ℂ`-linear `L : ℂⁿ → Lie A`; `e` kills `Λ`; and `v ↦ [t ↦ e(t v)]` is a bijection `Λ ≃ H₁(A(ℂ), ℤ)`. Since
  `λ ↦ [t ↦ exp(t λ)]` is the canonical isomorphism `ker exp_A ≅ π₁(A(ℂ), 0)`, this says that `L` carries `Λ` onto
  `H₁(A, ℤ) ⊂ Lie A`: the complex structure of `H₁(A, ℝ) = Lie A`, transported to `Λ ⊗ ℝ`, is that of `ℂⁿ`.
* `IsHodgeFibre τ P := ∃ e, H1Form P.A Λ_τ e ∧ IotaCompatible P e`: with `Λ_τ = ι(𝒪)(τ, 1)ᵀ ≅ 𝒪` this is
  "`(H₁(A, ℤ), 𝒪, Hodge structure) ≅ (𝒪, left multiplication, h_τ)`".

**Results** (all proved, standard axioms):
* `h1Form_iff`: given `UniformizationLeafAll`, `H1Form A Λ e ↔ IsUniformization id Λ e` for every full lattice
  `Λ ⊂ ℂⁿ` (the identification of `H₁(A(ℂ), ℤ)` with the period lattice: `π₁` of the covering `ℂ^g → ℂ^g/Λ'`,
  Mathlib's `IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite`);
* `pelHolFamily_of_hodge : UniformizationLeafAll → PELHolFamilyHodge → HolFamilyPrinted.PELHolFamily`;
* `pelHolFamilyHodge_of_pel` (converse, so the new leaf is not stronger given the textbook field), and
  `pelHolFamilyHodge_iff`;
* `shimuraHolModAll_of_hodge`, `compositeUses_of_hodge`: holfam's consumers from the new leaf.
-/

set_option linter.all false
set_option warn.classDefReducibility false

noncomputable section

namespace PELHodge

open CategoryTheory AlgebraicGeometry Limits Topology Filter Set MonObj
open PkgI3 (AbVar)
open BPAnalytic
open LeafQM LeafQM.AV
open ZInQ.LeafPush2 (CPts IsUniformization cEvalAt cDom)
open ZInQ.HomLattice (IsAnalyticHom IsStrongUnif)
open UnifPrinted (CPt classicalTopology XPtIn XevalAt)

attribute [local instance] UnifPrinted.classicalTopology

/-- **`H₁(A(ℂ), ℤ)`** of a complex abelian variety, as the abelianized fundamental group `π₁(A(ℂ), 0)ᵃᵇ` of `A(ℂ)`
with its classical (analytic) topology `UnifPrinted.classicalTopology` (Hurewicz: `H₁ = π₁ᵃᵇ` for a path-connected
space). Mathlib's `FundamentalGroup` and `Abelianization`. -/
def H1 (A : AbVar ℂ) : Type := Abelianization (FundamentalGroup (A.Pt ℂ) 1)

instance (A : AbVar ℂ) : CommGroup (H1 A) := by unfold H1; infer_instance

/-- The class in `H₁(A(ℂ), ℤ)` of a loop at `0` in `A(ℂ)`. -/
def loopClass {A : AbVar ℂ} (lp : Path (1 : A.Pt ℂ) 1) : H1 A :=
  Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk lp))

/-- **`Λ ⊂ ℂⁿ` is `H₁(A, ℤ)` inside `Lie A`, through `e`** (the `H₁` / Hodge form of a complex uniformization).
`e : ℂⁿ → A(ℂ)` is a holomorphic homomorphism (`IsAnalyticHom`: a homomorphism, preimages of the `U(ℂ)` open, regular
functions holomorphic), i.e. `e = exp_A ∘ L` with `L : ℂⁿ → Lie A` `ℂ`-linear; `e` kills `Λ`; and
`v ↦ [t ↦ e(t v)]` (`t ∈ [0, 1]`) is a bijection from `Λ` onto `H₁(A(ℂ), ℤ) = π₁(A(ℂ), 0)ᵃᵇ`. As
`λ ↦ [t ↦ exp_A(t λ)]` is the canonical isomorphism `ker exp_A ≅ π₁(A(ℂ), 0)`, this says that `L` maps `Λ` onto the
lattice `H₁(A, ℤ)` of `H₁(A, ℝ) = Lie A`, so that `Λ ⊗ ℝ = ℂⁿ` with its complex structure is `H₁(A, ℝ)` with its
Hodge structure. It does not say that `e` is onto or that its kernel is `Λ` (that is the uniformization theorem;
`h1Form_iff`). -/
def H1Form (A : AbVar ℂ) {n : ℕ} (Λ : Submodule ℤ (Fin n → ℂ))
    (e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)) : Prop :=
  IsAnalyticHom (RingHom.id ℂ) e ∧ (∀ v ∈ Λ, e v = 1) ∧
    ∃ lp : Λ → Path (1 : A.Pt ℂ) 1,
      (∀ v (t : unitInterval), lp v t = e (((t : ℝ) : ℂ) • (v : Fin n → ℂ))) ∧
      Function.Bijective (fun v => loopClass (lp v))

/-- **The fibre over `[τ, 1]` in Hodge / `H₁` form.** The QM abelian surface `P` has `H₁(P.A, ℤ)`, with its
`𝒪`-action and its Hodge structure, equal to `Λ_τ = ι(𝒪)(τ, 1)ᵀ ⊂ ℂ²` with `ι` and the complex structure of `ℂ²`;
equivalently (through the `ℝ`-isomorphism `B ⊗ ℝ → ℂ²`, `x ↦ ι(x)(τ, 1)ᵀ`) to `(𝒪, left multiplication, h_τ)`.
`IotaCompatible P e` (`e(ι(a) z) = ι_P(a)(e z)`) is the `𝒪`-linearity of `L : ℂ² → Lie P.A`, hence of
`Λ_τ ≅ H₁(P.A, ℤ)`. -/
def IsHodgeFibre (τ : UpperHalfPlane) (P : QML3 ℂ) : Prop :=
  ∃ e : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
    H1Form P.A (QM.qmLattice τ.im_pos.ne') e ∧ HDec.HSyn.G0Split.FibreQM.IotaCompatible P e

section Unif

variable {A : AbVar ℂ} {g : ℕ} {Λ' : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ']
  {φ : Torus Λ' ≃+ Additive (A.Pt ℂ)}

/-- The map `ℂ^g → A(ℂ)`, `w ↦ φ(w mod Λ')`. -/
def pmap (φ : Torus Λ' ≃+ Additive (A.Pt ℂ)) (w : Fin g → ℂ) : A.Pt ℂ :=
  Additive.toMul (φ (proj Λ' w))

theorem continuous_phi (hφ : Uniformization.IsUniformization A Λ' φ) :
    Continuous (fun q : Torus Λ' => Additive.toMul (φ q)) := by
  refine (continuous_generateFrom_iff (b := UnifPrinted.basicSets A.X)).mpr ?_
  rintro S ⟨U, f, z, ε, rfl⟩
  rw [← (QuotientAddGroup.isQuotientMap_mk Λ'.toAddSubgroup).isOpen_preimage]
  obtain ⟨hO, han⟩ := hφ.holo U f
  have := han.continuousOn.isOpen_inter_preimage hO (Metric.isOpen_ball (x := z) (ε := ε))
  convert this using 1
  ext v
  simp [Metric.mem_ball, dist_eq_norm, UnifPrinted.xPtIn_eq, UnifPrinted.xevalAt_eq]

theorem isOpenMap_phi (hφ : Uniformization.IsUniformization A Λ' φ) :
    IsOpenMap (fun q : Torus Λ' => Additive.toMul (φ q)) := by
  intro V hV
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨q, hqV, rfl⟩
  obtain ⟨v₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hφ.open_map v₀ V (hV.mem_nhds hqV)
  set P₀ := Additive.toMul (φ (proj Λ' v₀))
  have hW : IsOpen {P : A.Pt ℂ | Uniformization.PtIn A P U ∧
      ∀ i, ‖Uniformization.evalAt A U (f i) P - Uniformization.evalAt A U (f i) P₀‖ < ε} := by
    have : {P : A.Pt ℂ | Uniformization.PtIn A P U ∧
        ∀ i, ‖Uniformization.evalAt A U (f i) P - Uniformization.evalAt A U (f i) P₀‖ < ε} =
        {P | XPtIn A.X P U} ∩ ⋂ i, {P | XPtIn A.X P U ∧
          ‖XevalAt A.X U (f i) P - Uniformization.evalAt A U (f i) P₀‖ < ε} := by
      ext P
      simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, UnifPrinted.xPtIn_eq,
        UnifPrinted.xevalAt_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => ⟨h1, h2 i⟩⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => (h2 i).2⟩
    rw [this]
    exact (UnifPrinted.isOpen_ptIn U).inter
      (isOpen_iInter_of_finite fun i => UnifPrinted.isOpen_basic (f i) _ ε)
  refine Filter.mem_of_superset (hW.mem_nhds ⟨hU, fun i => lt_of_eq_of_lt (by rw [norm_eq_zero, sub_eq_zero]) hε⟩) ?_
  rintro P ⟨hP, hPi⟩
  obtain ⟨q, hqN, hq⟩ := hsep P hP hPi
  exact ⟨q, hqN, hq⟩

/-- `φ` is a homeomorphism onto `A(ℂ)` with its classical topology. -/
def phiHomeo (hφ : Uniformization.IsUniformization A Λ' φ) : Torus Λ' ≃ₜ A.Pt ℂ :=
  (φ.toEquiv.trans Additive.toMul).toHomeomorphOfContinuousOpen (continuous_phi hφ)
    (isOpenMap_phi hφ)

theorem pmap_eq_one_iff (w : Fin g → ℂ) : pmap φ w = 1 ↔ w ∈ Λ' := by
  unfold pmap
  constructor
  · intro h
    have h1 : φ (proj Λ' w) = 0 := by
      have : φ (proj Λ' w) = Additive.ofMul 1 := by rw [← h]; rfl
      rw [this]; rfl
    rw [map_eq_zero_iff φ φ.injective] at h1
    simpa using (QuotientAddGroup.eq_zero_iff w).mp h1
  · intro h
    rw [show proj Λ' w = 0 from (QuotientAddGroup.eq_zero_iff w).mpr h, map_zero]; rfl

theorem pmap_zero : pmap φ 0 = 1 := by
  unfold pmap; rw [show proj Λ' (0 : Fin g → ℂ) = 0 from rfl, map_zero]; rfl

theorem isCov (hφ : Uniformization.IsUniformization A Λ' φ) :
    IsAddQuotientCoveringMap (pmap φ) Λ'.toAddSubgroup := by
  have hq : IsQuotientMap (pmap φ) :=
    (phiHomeo hφ).isQuotientMap.comp (QuotientAddGroup.isQuotientMap_mk Λ'.toAddSubgroup)
  refine hq.isAddQuotientCoveringMap_of_addSubgroup Λ'.toAddSubgroup
    (isDiscrete_iff_discreteTopology.mpr (by assumption)) ?_
  intro e₁ e₂
  have : pmap φ e₁ = pmap φ e₂ ↔ proj Λ' e₁ = proj Λ' e₂ := by
    unfold pmap
    constructor
    · intro h; exact φ.injective (Additive.toMul.injective h)
    · intro h; rw [h]
  rw [this, proj_eq_iff]
  constructor
  · intro h
    have : e₂ + -e₁ = -(e₁ - e₂) := by abel
    rw [this]; exact Λ'.toAddSubgroup.neg_mem h
  · intro h
    have : e₁ - e₂ = -(e₂ + -e₁) := by abel
    rw [this]; exact Λ'.toAddSubgroup.neg_mem h


theorem continuous_pmap (hφ : Uniformization.IsUniformization A Λ' φ) : Continuous (pmap φ) :=
  (continuous_phi hφ).comp continuous_quot_mk

/-- The loop `t ↦ φ(t w mod Λ')` for `w ∈ Λ'`. -/
def lineLoop (hφ : Uniformization.IsUniformization A Λ' φ) (w : Fin g → ℂ) (hw : w ∈ Λ') :
    Path (1 : A.Pt ℂ) 1 where
  toFun t := pmap φ ((t : ℝ) • w)
  continuous_toFun := (continuous_pmap hφ).comp (continuous_subtype_val.smul continuous_const)
  source' := by simp [pmap_zero]
  target' := by simpa using (pmap_eq_one_iff w).mpr hw

/-- The basepoint `0` in the fibre of `pmap φ` over `1`. -/
def e0 : (pmap φ) ⁻¹' {1} := ⟨0, pmap_zero⟩

/-- **Monodromy of a straight loop.** -/
theorem monodromy_line (hφ : Uniformization.IsUniformization A Λ' φ) (w : Fin g → ℂ) (hw : w ∈ Λ')
    (c : Path (1 : A.Pt ℂ) 1) (hc : ∀ t : unitInterval, c t = pmap φ ((t : ℝ) • w)) :
    (isCov hφ).fundamentalGroupToMulOpposite e0
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)) =
      MulOpposite.op (Multiplicative.ofAdd (⟨w, hw⟩ : Λ'.toAddSubgroup)) := by
  refine (isCov hφ).fundamentalGroupToMulOpposite_apply_mk_eq
    (Γ := ⟨fun t => (t : ℝ) • w, continuous_subtype_val.smul continuous_const⟩) ?_ ?_ ?_
  · funext t; exact (hc t).symm
  · show ((0 : unitInterval) : ℝ) • w = 0
    simp
  · show ((1 : unitInterval) : ℝ) • w = w + 0
    simp

end Unif

section Main

variable {A : AbVar ℂ} {n : ℕ} {Λ : Submodule ℤ (Fin n → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- **Lattice form from the `H₁` form (GLUE, proved).** -/
theorem isUniformization_of_H1 (hU : Uniformization.UniformizationLeafAll)
    (e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)) (he : IsAnalyticHom (RingHom.id ℂ) e)
    (hker : ∀ v ∈ Λ, e v = 1) (lp : Λ → Path (1 : A.Pt ℂ) 1)
    (hlp : ∀ v (t : unitInterval), lp v t = e (((t : ℝ) : ℂ) • (v : Fin n → ℂ)))
    (hbij : Function.Bijective (fun v => loopClass (lp v))) :
    IsUniformization (RingHom.id ℂ) Λ e := by
  obtain ⟨g, Λ', hd, hz, φ, hφ⟩ := hU A
  have hs := ZInQ.HomLattice.isStrongUnif_of_bp hφ
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong hs he
  have hD' : ∀ v, pmap φ (D v) = e v := hD
  have hcov := isCov hφ
  set Θ := hcov.fundamentalGroupToMulOpposite e0 with hΘ
  have hΘinj : Function.Injective Θ := hcov.fundamentalGroupToMulOpposite_injective e0
  let Θ' : H1 A →* (Multiplicative Λ'.toAddSubgroup)ᵐᵒᵖ := Abelianization.lift Θ
  have hΘ' : ∀ x, Θ' (Abelianization.of x) = Θ x := fun x => Abelianization.lift_apply_of Θ x
  have key1 : ∀ v : Λ, D v ∈ Λ' := fun v => (pmap_eq_one_iff _).mp ((hD' v).trans (hker v v.2))
  have key2 : ∀ v : Λ, Θ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (lp v))) =
      MulOpposite.op (Multiplicative.ofAdd (⟨D v, key1 v⟩ : Λ'.toAddSubgroup)) := by
    intro v
    refine monodromy_line hφ (D v) (key1 v) (lp v) fun t => ?_
    rw [hlp v t, ← hD', map_smul, Complex.coe_smul]
  have key3 : ∀ w ∈ Λ', ∃ v : Λ, D v = w := by
    intro w hw
    obtain ⟨v, hv⟩ := hbij.2 (loopClass (lineLoop hφ w hw))
    refine ⟨v, ?_⟩
    have h1 := congrArg Θ' hv
    simp only [loopClass, hΘ'] at h1
    rw [key2 v, monodromy_line hφ w hw (lineLoop hφ w hw) (fun t => rfl)] at h1
    rw [MulOpposite.op_inj] at h1
    exact congrArg Subtype.val (Multiplicative.ofAdd.injective h1)
  have key4 : ∀ v₁ v₂ : Λ, D v₁ = D v₂ → v₁ = v₂ := by
    intro v₁ v₂ h
    apply hbij.1
    show loopClass (lp v₁) = loopClass (lp v₂)
    unfold loopClass
    congr 1
    apply hΘinj
    rw [key2, key2]
    congr 3
  -- `D` is onto: its range contains the full lattice `Λ'`
  have hDsurj : Function.Surjective D := by
    have hle : Submodule.span ℝ (Λ' : Set (Fin g → ℂ)) ≤
        (LinearMap.range (D : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ))).restrictScalars ℝ := by
      rw [Submodule.span_le]
      intro w hw
      obtain ⟨v, hv⟩ := key3 w hw
      exact ⟨v, hv⟩
    rw [IsZLattice.span_top, top_le_iff] at hle
    intro w
    have hw : w ∈ (LinearMap.range (D : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ))).restrictScalars ℝ := by
      rw [hle]; trivial
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, hv⟩
  -- `D` restricts to a bijection `Λ ≃ Λ'`, so the ranks agree and `n = g`
  let Dz : Λ →ₗ[ℤ] Λ' :=
    { toFun := fun v => ⟨D v, key1 v⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by
        show D ((c : ℤ) • (a : Fin n → ℂ)) = c • D a
        exact map_zsmul D c (a : Fin n → ℂ)) }
  have hDz : Function.Bijective Dz := by
    refine ⟨fun a b h => key4 a b (congrArg Subtype.val h), fun w => ?_⟩
    obtain ⟨v, hv⟩ := key3 w w.2
    exact ⟨v, Subtype.ext hv⟩
  have hrank : Module.finrank ℝ (Fin n → ℂ) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← ZLattice.rank ℝ Λ, ← ZLattice.rank ℝ Λ']
    exact (LinearEquiv.ofBijective Dz hDz).finrank_eq
  have hrankC : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ (Fin g → ℂ) := by
    have h1 := finrank_real_of_complex (Fin n → ℂ)
    have h2 := finrank_real_of_complex (Fin g → ℂ)
    omega
  have hDinj : Function.Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrankC
      (f := (D : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)))).mpr hDsurj
  refine (ZInQ.HomLattice.isUniformization_iff _ _ _).mpr ⟨he, fun z => ⟨fun hz => ?_, hker z⟩, ?_⟩
  · have hz' : D z ∈ Λ' := (pmap_eq_one_iff _).mp ((hD' z).trans hz)
    obtain ⟨v, hv⟩ := key3 _ hz'
    rw [← hDinj hv]; exact v.2
  · intro P
    obtain ⟨q, rfl⟩ : ∃ q, Additive.toMul (φ q) = P :=
      ⟨φ.symm (Additive.ofMul P), by rw [AddEquiv.apply_symm_apply]; rfl⟩
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨z, rfl⟩ := hDsurj w
    exact ⟨z, (hD' z).symm⟩


/-- A complex subspace inside a discrete subgroup is zero: `t ↦ t z` is a continuous map from `ℝ` to `Λ`. -/
theorem eq_zero_of_smul_mem {z : Fin n → ℂ} (h : ∀ t : ℝ, t • z ∈ Λ) : z = 0 := by
  let f : ℝ → Λ := fun t => ⟨t • z, h t⟩
  have hf : Continuous f := (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ) hf (x := 1) (y := 0)
  simpa [f] using congrArg Subtype.val this

/-- **The `H₁` form from the lattice form (GLUE, proved; converse of `isUniformization_of_H1`).** -/
theorem exists_H1_of_isUniformization (hU : Uniformization.UniformizationLeafAll)
    (e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)) (hu : IsUniformization (RingHom.id ℂ) Λ e) :
    IsAnalyticHom (RingHom.id ℂ) e ∧ (∀ v ∈ Λ, e v = 1) ∧
    ∃ lp : Λ → Path (1 : A.Pt ℂ) 1,
      (∀ v (t : unitInterval), lp v t = e (((t : ℝ) : ℂ) • (v : Fin n → ℂ))) ∧
      Function.Bijective (fun v => loopClass (lp v)) := by
  obtain ⟨he, hker, hsurj⟩ := (ZInQ.HomLattice.isUniformization_iff _ _ _).mp hu
  obtain ⟨g, Λ', hd, hz, φ, hφ⟩ := hU A
  have hs := ZInQ.HomLattice.isStrongUnif_of_bp hφ
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong hs he
  have hD' : ∀ v, pmap φ (D v) = e v := hD
  have hcov := isCov hφ
  set Θ := hcov.fundamentalGroupToMulOpposite e0 with hΘ
  have hΘinj : Function.Injective Θ := hcov.fundamentalGroupToMulOpposite_injective e0
  let Θ' : H1 A →* (Multiplicative Λ'.toAddSubgroup)ᵐᵒᵖ := Abelianization.lift Θ
  have hΘ' : ∀ x, Θ' (Abelianization.of x) = Θ x := fun x => Abelianization.lift_apply_of Θ x
  have key1 : ∀ v : Λ, D v ∈ Λ' := fun v => (pmap_eq_one_iff _).mp ((hD' v).trans ((hker v).mpr v.2))
  have hDinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro z hz0
    refine eq_zero_of_smul_mem (Λ := Λ) fun t => (hker _).mp ?_
    rw [← hD', ContinuousLinearMap.map_smul_of_tower, hz0, smul_zero]
    exact (pmap_eq_one_iff _).mpr (zero_mem _)
  have hDs : Function.Surjective D := by
    refine ZInQ.HomLattice.surjective_of_proj_comp_surjective (Λ' := Λ')
      (D : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) fun t => ?_
    obtain ⟨z, hz⟩ := hsurj (Additive.toMul (φ t))
    refine ⟨z, φ.injective (Additive.toMul.injective ?_)⟩
    exact (hD z).trans hz
  have hDsurj : ∀ w ∈ Λ', ∃ v : Λ, D v = w := by
    intro w hw
    obtain ⟨z, rfl⟩ := hDs w
    have hz : z ∈ Λ := (hker z).mp ((hD' z).symm.trans ((pmap_eq_one_iff _).mpr hw))
    exact ⟨⟨z, hz⟩, rfl⟩
  have hcont : Continuous (show (Fin n → ℂ) → A.Pt ℂ from e) := by
    have : (show (Fin n → ℂ) → A.Pt ℂ from e) = pmap φ ∘ D := funext fun v => (hD' v).symm
    rw [this]; exact (continuous_pmap hφ).comp D.continuous
  let lp : Λ → Path (1 : A.Pt ℂ) 1 := fun v =>
    { toFun := fun t => e (((t : ℝ) : ℂ) • (v : Fin n → ℂ))
      continuous_toFun := hcont.comp
        ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
      source' := by
        have h0 : (((0 : unitInterval) : ℝ) : ℂ) • (v : Fin n → ℂ) = 0 := by simp
        show e _ = _
        rw [h0]; exact ZInQ.HomLattice.map_zero_of_hom he.1
      target' := by
        have h1 : (((1 : unitInterval) : ℝ) : ℂ) • (v : Fin n → ℂ) = v := by simp
        show e _ = _
        rw [h1]; exact (hker v).mpr v.2 }
  have key2 : ∀ v : Λ, Θ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (lp v))) =
      MulOpposite.op (Multiplicative.ofAdd (⟨D v, key1 v⟩ : Λ'.toAddSubgroup)) := by
    intro v
    refine monodromy_line hφ (D v) (key1 v) (lp v) fun t => ?_
    show e _ = _
    rw [← hD', map_smul, Complex.coe_smul]
  refine ⟨he, fun v hv => (hker v).mpr hv, lp, fun v t => rfl, fun v₁ v₂ h => ?_, fun x => ?_⟩
  · have h1 := congrArg Θ' h
    simp only [loopClass, hΘ'] at h1
    rw [key2, key2, MulOpposite.op_inj] at h1
    exact Subtype.ext (hDinj (congrArg Subtype.val (Multiplicative.ofAdd.injective h1)))
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨w, hw⟩ : ∃ w : Λ'.toAddSubgroup, Θ y = MulOpposite.op (Multiplicative.ofAdd w) :=
      ⟨Multiplicative.toAdd (Θ y).unop, rfl⟩
    obtain ⟨v, hv⟩ := hDsurj w w.2
    refine ⟨v, ?_⟩
    show Abelianization.of _ = Abelianization.of y
    congr 1
    apply hΘinj
    rw [key2, hw]
    congr 3

end Main

/-! ## The identification `H₁(A(ℂ), ℤ) =` period lattice -/

/-- **`H1Form` ⇔ lattice form, given the complex uniformization (GLUE, proved).** For a full lattice `Λ ⊂ ℂⁿ` and
`e : ℂⁿ → A(ℂ)`: `e` presents `H₁(A, ℤ)` as `Λ` inside `Lie A` iff `e` is an analytic uniformization with kernel `Λ`. -/
theorem h1Form_iff (hU : Uniformization.UniformizationLeafAll) {A : AbVar ℂ} {n : ℕ}
    {Λ : Submodule ℤ (Fin n → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)) :
    H1Form A Λ e ↔ IsUniformization (RingHom.id ℂ) Λ e := by
  constructor
  · rintro ⟨he, hker, lp, hlp, hbij⟩
    exact isUniformization_of_H1 hU e he hker lp hlp hbij
  · intro hu
    exact exists_H1_of_isUniformization hU e hu

/-- **The fibre clause: Hodge form ⇔ holfam's lattice form**, given `UniformizationLeafAll`. -/
theorem isHodgeFibre_iff (hU : Uniformization.UniformizationLeafAll) (τ : UpperHalfPlane) (P : QML3 ℂ) :
    IsHodgeFibre τ P ↔ ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (QM.qmLattice τ.im_pos.ne') Φu ∧
        HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu := by
  haveI : DiscreteTopology (QM.qmLattice τ.im_pos.ne') := by unfold QM.qmLattice; infer_instance
  haveI : IsZLattice ℝ (QM.qmLattice τ.im_pos.ne') := by unfold QM.qmLattice; infer_instance
  constructor
  · rintro ⟨e, h1, hι⟩
    exact ⟨e, (h1Form_iff hU e).mp h1, hι⟩
  · rintro ⟨e, hu, hι⟩
    exact ⟨e, (h1Form_iff hU e).mpr hu, hι⟩

/-! ## The leaf -/

/-- **LEAF `PELHolFamilyHodge` (Deligne's PEL moduli curve `M_{K₃}/ℚ` with its universal QM abelian scheme and the
complex uniformization `τ ↦ [τ, 1]`, the fibres in the print's Hodge / `H₁` form).** There are a curve `S`, proper
and smooth of relative dimension 1 over `ℚ`, a QM abelian scheme `𝒜 → S` with level-3 structure (`QMAbScheme`) all
of whose field fibres are objects (`QML3`), and a holomorphic map `τ ↦ s_τ ∈ S(ℂ)` on `ℍ`
(`ShimuraSplit.IsHolFamily`) such that the fibre `P` of `𝒜` at `s_τ` has `H₁(P.A(ℂ), ℤ)` with its `𝒪`-action and
Hodge structure equal to `(ι(𝒪)(τ, 1)ᵀ, ι, i)`, i.e. to `(𝒪, left multiplication, h_τ)` (`IsHodgeFibre`).

It is holfam's `HolFamilyPrinted.PELHolFamily` with the fibre clause in the form of the print instead of lattice
coordinates (`pelHolFamily_of_hodge`, `pelHolFamilyHodge_of_pel`: equivalent given the textbook field
`UniformizationLeafAll`).

*Published statements* (locators recalled, UNVERIFIED; no network):
* Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§4.9–4.17 and Example 5.8: for a PEL datum
  `(B, *, V, ψ)` and a neat compact open `K`, the moduli scheme `M_K` over the reflex field (here `ℚ`) with its
  universal abelian scheme; `M_K(ℂ) = G(ℚ)\X × G(𝔸_f)/K`, the point `[h, g]` carrying the abelian variety `A` with
  `H₁(A, ℚ) = V` (`B`-linearly), Hodge structure `h` and lattice `H₁(A, ℤ) = g·L`;
* Milne, *Introduction to Shimura varieties* (2005), §8 (PEL Shimura varieties as moduli varieties, with the same
  description of the points over `ℂ` in terms of `H₁` and Hodge structures; Riemann's theorem in families, Deligne
  Hodge II 4.4.3) and §14 (the model over the reflex field).

*Form*: a consequence of the first, not stronger: `B` of discriminant 6, `V = B`, `L = 𝒪`, `G = B^×`,
`K₃ = ker((𝒪⊗ℤ̂)^× → (𝒪/3𝒪)^×)`, `S = M_{K₃}`, `𝒜` its universal family, `s_τ = [h_τ, 1]`; one family; the fibre is
described by `H₁` with `𝒪`-action and Hodge structure only (no polarization, no level clause). Dictionary used to
state it over Mathlib: `H₁ = π₁ᵃᵇ` (Hurewicz), `Lie A` through holomorphic homomorphisms `ℂⁿ → A(ℂ)`, and
`ker exp_A ≅ π₁(A(ℂ), 0)` by `λ ↦ [t ↦ exp(tλ)]` (`H1Form`). -/
def PELHolFamilyHodge : Prop :=
  ∃ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom ∧ SmoothOfRelativeDimension 1 S.hom ∧
    ∃ 𝒜 : R1UnivRigid.QMAbScheme S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜.toQMFamily s.left P) ∧
      ∃ sτ : UpperHalfPlane → (fieldPt ℂ ⟶ S),
        ShimuraSplit.IsHolFamily (X := S.left) (fun τ => (sτ τ).left) ∧
        ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, IsFibreOf 𝒜.toQMFamily (sτ τ).left P ∧ IsHodgeFibre τ P

/-- **holfam's lattice form from the Hodge form (GLUE, proved)**, with the textbook field `UniformizationLeafAll`
(`H₁(A(ℂ), ℤ)` identified with the period lattice, `isHodgeFibre_iff`). -/
theorem pelHolFamily_of_hodge (hU : Uniformization.UniformizationLeafAll) (h : PELHolFamilyHodge) :
    HolFamilyPrinted.PELHolFamily := by
  obtain ⟨S, hp, hs, 𝒜, hfib, sτ, hhol, hmod⟩ := h
  refine ⟨S, hp, hs, 𝒜, hfib, sτ, hhol, fun τ => ?_⟩
  obtain ⟨P, hP, hH⟩ := hmod τ
  exact ⟨P, hP, (isHodgeFibre_iff hU τ P).mp hH⟩

/-- **The converse (proved): the new leaf is not stronger than holfam's, given `UniformizationLeafAll`.** -/
theorem pelHolFamilyHodge_of_pel (hU : Uniformization.UniformizationLeafAll)
    (h : HolFamilyPrinted.PELHolFamily) : PELHolFamilyHodge := by
  obtain ⟨S, hp, hs, 𝒜, hfib, sτ, hhol, hmod⟩ := h
  refine ⟨S, hp, hs, 𝒜, hfib, sτ, hhol, fun τ => ?_⟩
  obtain ⟨P, hP, hL⟩ := hmod τ
  exact ⟨P, hP, (isHodgeFibre_iff hU τ P).mpr hL⟩

theorem pelHolFamilyHodge_iff (hU : Uniformization.UniformizationLeafAll) :
    PELHolFamilyHodge ↔ HolFamilyPrinted.PELHolFamily :=
  ⟨pelHolFamily_of_hodge hU, pelHolFamilyHodge_of_pel hU⟩

/-! ## holfam's consumers from the new leaf -/

/-- `ShimuraSplit2.ShimuraHolModAll` (the holomorphic moduli map on every fine witness). -/
theorem shimuraHolModAll_of_hodge (hU : Uniformization.UniformizationLeafAll) (h : PELHolFamilyHodge) :
    ShimuraSplit2.ShimuraHolModAll :=
  HolFamilyPrinted.shimuraHolModAll_of_pel (pelHolFamily_of_hodge hU h)

/-- The field `shimuraFamilyAb`. -/
theorem shimuraFamilyAb_of_hodge (hR : ShimuraGlue.DeligneComponentsX6PrintedAb)
    (hU : Uniformization.UniformizationLeafAll) (h : PELHolFamilyHodge) :
    HDec.QMSplit.Moduli.ShimuraFamilyAb :=
  HolFamilyPrinted.shimuraFamilyAb_of_pel hR (pelHolFamily_of_hodge hU h)

/-- The chain's `TSHecke.Y3Connected`. -/
theorem y3Connected_of_hodge (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)
    (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (h : PELHolFamilyHodge)
    (hM : QMRecPrinted.MainTheoremCM) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) : HDec.TSHecke.Y3Connected :=
  HolFamilyPrinted.y3Connected_of_pel hGL hR (pelHolFamily_of_hodge hUL h) hM hUL hG hMum

/-- **Everything the composite `shimuraMainThmIDeligneY3AbU` is used for**, from `PELHolFamilyHodge`,
`MainTheoremCM`, the fine witness of `deligneComponentsX6PrintedAb`, the textbook fields and `mumfordGroupLaw`. -/
theorem compositeUses_of_hodge (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (h : PELHolFamilyHodge)
    (hM : QMRecPrinted.MainTheoremCM) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed)
    (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) :
    ShimuraGlue.Ray.RayClassCMAb ∧ HDec.QMSplit.Moduli.ShimuraFamilyAb ∧ HDec.TSHecke.Y3Connected :=
  HolFamilyPrinted.compositeUses_of_pel hR (pelHolFamily_of_hodge hUL h) hM hUL hG hMum hGL

end PELHodge

end
