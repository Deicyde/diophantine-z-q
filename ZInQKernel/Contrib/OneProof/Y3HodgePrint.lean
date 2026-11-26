import ZInQKernel.Contrib.OneProof.ShimuraY3PrintedLeaves
import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge

/-! # y3-hodge: `deligneCanonicalModelY3EveryH` as a direct instance of its print

Task y3-hodge (2026-11-17). Report `docs/research/y3-hodge.md`; log `scratch/y3-hodge/log.md`. No `sorry`; every
theorem uses only `propext`, `Classical.choice`, `Quot.sound`.

The research leaf `Y3Fix.DeligneCanonicalModelY3EveryH` (y3-fix) was rated consequence, GLUE by the review (queue11)
for three gaps; each is closed here in Lean, and the leaf is restated as its print:

* §0–§4, **the print's `H₁(A, ℤ)` reaches `IsHodgeH1`.** `H1 A = π₁(A(ℂ), 0)ᵃᵇ` (Mathlib's fundamental group and
  abelianization, Hurewicz) for the classical topology `CloudB3W17Hodge.classicalTopology` (identified with the ported
  manifold topology by `CloudB3W17Hodge.classicalTopology_eq`). pel-hodge's `h1Form_iff` (on `wip/pel-hodge`, not on
  this base) is ported: straight loops `t ↦ e(tv)` give `Λ ≅ H₁` exactly for uniformizations (monodromy of the
  covering `ℂ^g → A(ℂ)`). `IsHodgeH1Print P τ`: a holomorphic homomorphism `e = exp_A ∘ L : ℂⁿ → A(ℂ)`, an
  `ℝ`-isomorphism `β : B_ℝ ≅ ℂⁿ` with `β(M J_τ) = i β(M)`, and loops `c(b) = [t ↦ e(t β(b))]` giving a bijection
  `𝒪 ≅ H₁(A(ℂ), ℤ)` which is `𝒪`-linear for the action of `ι_A(a)` on `H₁` by functoriality. `print_iff_hodge`:
  `IsHodgeH1Print P τ ↔ Y3Fix.IsHodgeH1 P τ`.
* §5, **`ℍ^±` with `B^×` versus `ℍ` with `B^×_+`.** `DCRelPM` (the print's double cosets on `ℍ^± × G(𝔸_f)`),
  `dcRelPM_iff` (restricted to `ℍ` it is `DCRel`), `exists_upper` (`μ = 1 + i`, `nrd μ = −1`, moves `ℍ⁻` to `ℍ`).
* §6, **the sign of `h` and `B` versus `B^op`.** `F0_iff`: `F⁰ = {M : M J_τ = −i M} = {M : M (τ, 1)ᵀ = 0}`
  (holomorphic in `τ`, Deligne's convention `h(z)|V^{p,q} = z^{-p} z̄^{-q}`), `iota_mul_Jmat` (`B^×_+`-equivariance),
  `adjugate_Jmat` (`J̄_τ = −J_τ`), `Jmat_sq`. The leaf's sign is the right one; no statement change.
* §7, **the leaf as the print.** `DeligneCanonicalModelY3EveryPrint` (`Ψ` on `ℍ^± × G(𝔸_f)`, fibres `DCRelPM`, the
  moduli clause `IsHodgeH1Print`); `deligneH_of_print` (old leaf from the new one).
* §8, **Lemma P on the genuine `H₁`.** `lemmaP_H1`: for the print's data, exactly one principal Riemann form of type
  `μ` on `H₁(A(ℂ), ℤ)` (biadditive, alternating, `ι_A(a)_*` adjoint to `ι_A(a†)_*`, unimodular, positive real
  extension), and it is `E₀` under `c` (y3abu-strict's `lemmaP_lattice_unique` argument, run on `𝒪` and transported).
* §9, **the converse.** `print_iff_deligneH`, `printPM_iff_field`: the new leaf is equivalent to the old one.
-/

set_option linter.all false
set_option warn.classDefReducibility false

noncomputable section

namespace Y3Hodge

open CategoryTheory AlgebraicGeometry Limits Topology Filter Set MonObj
open PkgI3 (AbVar)
open BPAnalytic
open LeafQM LeafQM.AV
open ZInQ.LeafPush2 (CPts IsUniformization cEvalAt cDom)
open ZInQ.HomLattice (IsAnalyticHom IsStrongUnif)
open CloudB3W17Hodge (CPt classicalTopology XPtIn XevalAt)

attribute [local instance] CloudB3W17Hodge.classicalTopology

/-! ## 0. The classical topology: basic facts (unif-printed's lemmas, re-proved for the base's copy) -/

namespace UP

theorem xPtIn_eq (A : AbVar ℂ) : XPtIn A.X = Uniformization.PtIn A := rfl
theorem xevalAt_eq (A : AbVar ℂ) : XevalAt A.X = Uniformization.evalAt A := rfl

variable {X : Over (Spec (CommRingCat.of ℂ))}

theorem isOpen_basic {U : X.left.Opens} (f : Γ(X.left, U)) (z : ℂ) (ε : ℝ) :
    IsOpen[classicalTopology X] {P | XPtIn X P U ∧ ‖XevalAt X U f P - z‖ < ε} :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f, z, ε, rfl⟩

theorem isOpen_ptIn (U : X.left.Opens) : IsOpen[classicalTopology X] {P | XPtIn X P U} := by
  have := isOpen_basic (X := X) (0 : Γ(X.left, U)) 0 1
  convert this using 1
  ext P
  constructor
  · intro h
    refine ⟨h, ?_⟩
    unfold XevalAt
    simp [h]
  · exact fun h => h.1

end UP

/-- **`H₁(A(ℂ), ℤ)`** of a complex abelian variety, as the abelianized fundamental group `π₁(A(ℂ), 0)ᵃᵇ` of `A(ℂ)`
with its classical (analytic) topology `CloudB3W17Hodge.classicalTopology` (Hurewicz: `H₁ = π₁ᵃᵇ` for a path-connected
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
  refine (continuous_generateFrom_iff (b := CloudB3W17Hodge.basicSets A.X)).mpr ?_
  rintro S ⟨U, f, z, ε, rfl⟩
  rw [← (QuotientAddGroup.isQuotientMap_mk Λ'.toAddSubgroup).isOpen_preimage]
  obtain ⟨hO, han⟩ := hφ.holo U f
  have := han.continuousOn.isOpen_inter_preimage hO (Metric.isOpen_ball (x := z) (ε := ε))
  convert this using 1
  ext v
  simp [Metric.mem_ball, dist_eq_norm, UP.xPtIn_eq, UP.xevalAt_eq]

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
      simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, UP.xPtIn_eq,
        UP.xevalAt_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => ⟨h1, h2 i⟩⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => (h2 i).2⟩
    rw [this]
    exact (UP.isOpen_ptIn U).inter
      (isOpen_iInter_of_finite fun i => UP.isOpen_basic (f i) _ ε)
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


/-! ## 2. Functoriality of `H₁`, continuity of analytic homomorphisms -/

/-- A morphism of `ℂ`-schemes is continuous on `ℂ`-points for the classical topology. -/
theorem continuous_postcomp {X Y : Over (Spec (CommRingCat.of ℂ))} (f : X ⟶ Y) :
    Continuous (fun P : CPt X => P ≫ f) := by
  refine (continuous_generateFrom_iff (b := CloudB3W17Hodge.basicSets Y)).mpr ?_
  rintro S ⟨U, s, z, ε, rfl⟩
  have hiff : ∀ P : CPt X, XPtIn Y (P ≫ f) U ↔ XPtIn X P (f.left ⁻¹ᵁ U) := fun P => Iff.rfl
  have hev : ∀ P : CPt X,
      XevalAt Y U s (P ≫ f) = XevalAt X (f.left ⁻¹ᵁ U) (f.left.app U s) P := by
    intro P
    unfold XevalAt
    by_cases h : XPtIn X P (f.left ⁻¹ᵁ U)
    · rw [dif_pos h, dif_pos ((hiff P).mpr h)]
      simp only [Over.comp_left, Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]
      rfl
    · rw [dif_neg h, dif_neg (fun h' => h ((hiff P).mp h'))]
  have : (fun P : CPt X => P ≫ f) ⁻¹' {Q | XPtIn Y Q U ∧ ‖XevalAt Y U s Q - z‖ < ε} =
      {P | XPtIn X P (f.left ⁻¹ᵁ U) ∧ ‖XevalAt X (f.left ⁻¹ᵁ U) (f.left.app U s) P - z‖ < ε} := by
    ext P
    simp only [mem_preimage, mem_setOf_eq, hev P]
    exact and_congr_left' (hiff P)
  rw [this]
  exact UP.isOpen_basic _ _ _

/-- **`f_*` on loops** for an endomorphism `f` of `A` (a homomorphism, so `f(0) = 0`): `t ↦ f(ℓ(t))`.
The class `loopClass (pushLoop f ℓ)` is `f_* [ℓ]`, the functoriality of `H₁(A(ℂ), ℤ) = π₁(A(ℂ), 0)ᵃᵇ`. -/
def pushLoop {A : AbVar ℂ} (f : AbVar.End A) (lp : Path (1 : A.Pt ℂ) 1) : Path (1 : A.Pt ℂ) 1 where
  toFun t := lp t ≫ f.hom
  continuous_toFun := (continuous_postcomp (X := A.X) (Y := A.X) f.hom).comp lp.continuous
  source' := by
    rw [Path.source]; exact map_one (AbVar.ptMap (L := ℂ) f)
  target' := by
    rw [Path.target]; exact map_one (AbVar.ptMap (L := ℂ) f)

theorem pushLoop_apply {A : AbVar ℂ} (f : AbVar.End A) (lp : Path (1 : A.Pt ℂ) 1) (t : unitInterval) :
    pushLoop f lp t = lp t ≫ f.hom := rfl

/-- An analytic homomorphism `ℂⁿ → A(ℂ)` is continuous for the classical topology (it factors through a
uniformization by a `ℂ`-linear map). -/
theorem continuous_of_isAnalyticHom (hU : Uniformization.UniformizationLeafAll) {A : AbVar ℂ} {n : ℕ}
    {e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)} (he : IsAnalyticHom (RingHom.id ℂ) e) :
    Continuous (show (Fin n → ℂ) → A.Pt ℂ from e) := by
  obtain ⟨g, Λ', hd, hz, φ, hφ⟩ := hU A
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong
    (ZInQ.HomLattice.isStrongUnif_of_bp hφ) he
  have : (show (Fin n → ℂ) → A.Pt ℂ from e) = pmap φ ∘ D := funext fun v => (hD v).symm
  rw [this]; exact (continuous_pmap hφ).comp D.continuous

/-! ## 3. The print's moduli clause: `(H₁(A, ℤ), 𝒪, h_A) ≅ (𝒪, left multiplication, h_τ)` -/

section Print

open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)

/-- **The moduli clause in the print's form** (Deligne, Sém. Bourbaki 389, §4; Milne, ISV, §§6–8: the point
`[h_τ, u]`, `u ∈ 𝒪̂^×` so that `L_u = 𝒪`, is the abelian variety `A` with `(H₁(A, ℤ), ι_*, h_A) ≅ (𝒪, left mult.,
h_τ)`), over genuine definitions:
* `H₁(A, ℤ) = H1 P.A = π₁(A(ℂ), 0)ᵃᵇ` (Mathlib's fundamental group and abelianization; `A(ℂ)` with its classical
  topology; Hurewicz);
* `e : ℂⁿ → A(ℂ)` is a holomorphic homomorphism (`IsAnalyticHom`), i.e. `e = exp_A ∘ L` with `L : ℂⁿ → Lie A`
  `ℂ`-linear: `ℂⁿ` with `e` stands for `Lie A` with `exp_A`, whose kernel is `H₁(A, ℤ)`;
* `c b = [t ↦ e(t β(b))]`, `b ∈ 𝒪`: the iso `𝒪 ≅ H₁(A, ℤ)` (bijective) is `b ↦ L β(b) ∈ ker exp_A`, extended
  `ℝ`-linearly by `L ∘ β : B_ℝ → H₁(A, ℝ) = Lie A`;
* `𝒪`-linearity on `H₁`: `ι_A(a)_* c(b) = c(ab)` (the action of `ι_A(a)` on `H₁` by functoriality, `pushLoop`);
* the Hodge structure: the complex structure of `H₁(A, ℝ) = Lie A` corresponds to right multiplication by
  `J_τ = Jmat τ` (`β(M J_τ) = i β(M)`), the complex structure of `(B_ℝ, h_τ)`. -/
def IsHodgeH1Print (P : QML3 ℂ) (τ : UpperHalfPlane) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → ℂ) → CPts P.A (RingHom.id ℂ))
    (β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ)) (c : O → Path (1 : P.A.Pt ℂ) 1),
    IsAnalyticHom (RingHom.id ℂ) e ∧
    (∀ (b : O) (t : unitInterval), c b t = e (((t : ℝ) : ℂ) • β (BPAnalytic.QM.iota (b : B)))) ∧
    Function.Bijective (fun b => loopClass (c b)) ∧
    (∀ a b : O, loopClass (pushLoop (P.q.iota a) (c b)) = loopClass (c (a * b))) ∧
    (∀ M, β (M * Y3Fix.Jmat τ) = Complex.I • β M)

/-- `b ↦ ℓ_τ(ι b) = ι(b)(τ, 1)ᵀ`, `𝒪 → Λ_τ`. -/
def bOf (τ : UpperHalfPlane) (b : O) : BPAnalytic.QM.qmLattice τ.im_pos.ne' :=
  ⟨Y3Fix.ellE τ (BPAnalytic.QM.iota (b : B)),
    (HDec.HSyn.G0Split.FibreQM.PeriodGlue.mem_qmLattice_iff _ _).2 ⟨b, b.2, (Y3Fix.latVec_eq τ b).symm⟩⟩

theorem bOf_val (τ : UpperHalfPlane) (b : O) :
    (bOf τ b : Fin 2 → ℂ) = Y3Fix.ellE τ (BPAnalytic.QM.iota (b : B)) := rfl

theorem bOf_bijective (τ : UpperHalfPlane) : Function.Bijective (bOf τ) := by
  refine ⟨fun b b' h => ?_, fun v => ?_⟩
  · have h1 := congrArg (fun v : BPAnalytic.QM.qmLattice τ.im_pos.ne' => (v : Fin 2 → ℂ)) h
    simp only [bOf_val] at h1
    rw [← Y3Fix.latVec_eq, ← Y3Fix.latVec_eq] at h1
    exact Subtype.ext (RayClassCFT.iota_eig_inj τ.im_pos.ne' h1)
  · obtain ⟨b, hb, hv⟩ := (HDec.HSyn.G0Split.FibreQM.PeriodGlue.mem_qmLattice_iff _ _).mp v.2
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    rw [bOf_val, ← Y3Fix.latVec_eq]; exact hv.symm

theorem ellE_iota_mul (τ : UpperHalfPlane) (a b : O) :
    Y3Fix.ellE τ (BPAnalytic.QM.iota ((a * b : O) : B)) =
      (qmMat a).mulVec (Y3Fix.ellE τ (BPAnalytic.QM.iota (b : B))) := by
  rw [Subring.coe_mul, RayClassCFT.iota_mul, Y3Fix.ellE_iota]

end Print

/-! ## 4. The dictionary: print form ⇔ lattice form ⇔ `Y3Fix.IsHodgeH1` -/

section Dict

open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)

/-- **Print form ⇒ lattice form (GLUE, proved).** `Φu = e ∘ T`, `T = β ∘ ℓ_τ⁻¹` (`ℂ`-linear); `H₁ ≅ 𝒪 ≅ Λ_τ`
gives the uniformization through `isUniformization_of_H1`; the `𝒪`-linearity on `H₁` gives `ι`-compatibility:
`z ↦ Φu(ι(a) z)` and `z ↦ ι_A(a)(Φu z)` are analytic homomorphisms, so `pmap φ ∘ D₁`, `pmap φ ∘ D₂` with `D₁, D₂`
`ℂ`-linear; on `v = ℓ_τ(ι b)` the monodromies of their straight loops are `D₁ v` and `D₂ v`, and these loops are
`c(ab)` and `ι_A(a)_* c(b)`, equal in `H₁`; so `D₁ = D₂` on the full lattice `Λ_τ`, hence everywhere. -/
theorem lattice_of_print (hU : Uniformization.UniformizationLeafAll) {P : QML3 ℂ} {τ : UpperHalfPlane}
    (h : IsHodgeH1Print P τ) :
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧ IotaCompatible P Φu := by
  obtain ⟨n, e, β, c, he, hc, hbij, hact, hJ⟩ := h
  haveI : DiscreteTopology (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    unfold BPAnalytic.QM.qmLattice; infer_instance
  haveI : IsZLattice ℝ (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    unfold BPAnalytic.QM.qmLattice; infer_instance
  set Lτ := BPAnalytic.QM.qmLattice τ.im_pos.ne' with hLτ
  let T := Y3Fix.Tlin τ β hJ
  have hT : ∀ M, T (Y3Fix.ellE τ M) = β M := Y3Fix.Tlin_ellE τ β hJ
  let Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ) := fun z => e (T z)
  have hΦa : IsAnalyticHom (RingHom.id ℂ) Φu := ZInQ.HomLattice.isAnalyticHom_lin he T
  have hΦc : Continuous (show (Fin 2 → ℂ) → P.A.Pt ℂ from Φu) := continuous_of_isAnalyticHom hU hΦa
  have hcb : ∀ (b : O) (t : unitInterval), c b t = Φu (((t : ℝ) : ℂ) • (bOf τ b : Fin 2 → ℂ)) := by
    intro b t
    rw [hc b t, bOf_val]
    show _ = e (T _)
    rw [map_smul, hT]
  have hker : ∀ v ∈ Lτ, Φu v = 1 := by
    intro v hv
    obtain ⟨b, hb⟩ := (bOf_bijective τ).2 ⟨v, hv⟩
    have hv' : v = (bOf τ b : Fin 2 → ℂ) := by rw [hb]
    have h1 := hcb b 1
    simp only [Set.Icc.coe_one, Complex.ofReal_one, one_smul] at h1
    rw [hv', ← h1]; exact (c b).target
  let lp : Lτ → Path (1 : P.A.Pt ℂ) 1 := fun v =>
    { toFun := fun t => Φu (((t : ℝ) : ℂ) • (v : Fin 2 → ℂ))
      continuous_toFun := hΦc.comp
        ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
      source' := by
        have h0 : (((0 : unitInterval) : ℝ) : ℂ) • (v : Fin 2 → ℂ) = 0 := by simp
        show Φu _ = _
        rw [h0]; exact ZInQ.HomLattice.map_zero_of_hom hΦa.1
      target' := by
        have h1 : (((1 : unitInterval) : ℝ) : ℂ) • (v : Fin 2 → ℂ) = v := by simp
        show Φu _ = _
        rw [h1]; exact hker v v.2 }
  have hlpc : ∀ b, lp (bOf τ b) = c b := fun b => Path.ext (funext fun t => (hcb b t).symm)
  have hbij' : Function.Bijective (fun v => loopClass (lp v)) := by
    have hcomp : (fun v => loopClass (lp v)) ∘ bOf τ = fun b => loopClass (c b) := funext fun b => by
      simp only [Function.comp_apply, hlpc]
    rw [← Function.Bijective.of_comp_iff _ (bOf_bijective τ), hcomp]; exact hbij
  have hUnif : IsUniformization (RingHom.id ℂ) Lτ Φu :=
    isUniformization_of_H1 hU Φu hΦa hker lp (fun v t => rfl) hbij'
  refine ⟨Φu, hUnif, fun a z => ?_⟩
  obtain ⟨g, Λ', hd, hz, φ, hφ⟩ := hU P.A
  have hs := ZInQ.HomLattice.isStrongUnif_of_bp hφ
  have hcov := isCov hφ
  set Θ := hcov.fundamentalGroupToMulOpposite e0 with hΘ
  let Θ' : H1 P.A →* (Multiplicative Λ'.toAddSubgroup)ᵐᵒᵖ := Abelianization.lift Θ
  have hΘ' : ∀ x, Θ' (Abelianization.of x) = Θ x := fun x => Abelianization.lift_apply_of Θ x
  obtain ⟨D1, hD1⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong hs
    (ZInQ.HomLattice.isAnalyticHom_lin hΦa (Matrix.mulVecLin (qmMat a)))
  obtain ⟨D2, hD2⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong hs
    (ZInQ.HomLattice.isAnalyticHom_comp hΦa (P.q.iota a).hom)
  have hD1' : ∀ v, pmap φ (D1 v) = Φu ((qmMat a).mulVec v) := hD1
  have hD2' : ∀ v, pmap φ (D2 v) = Φu v ≫ (P.q.iota a).hom := hD2
  have hline1 : ∀ (v : Fin 2 → ℂ) (t : ℝ), Φu ((t : ℂ) • (qmMat a).mulVec v) = pmap φ (t • D1 v) := by
    intro v t; rw [← Matrix.mulVec_smul, ← hD1', map_smul, Complex.coe_smul]
  have hline2 : ∀ (v : Fin 2 → ℂ) (t : ℝ), Φu ((t : ℂ) • v) ≫ (P.q.iota a).hom = pmap φ (t • D2 v) := by
    intro v t; rw [← hD2', map_smul, Complex.coe_smul]
  have hagree : ∀ b : O, D1 (bOf τ b) = D2 (bOf τ b) := by
    intro b
    have m1 : D1 (bOf τ b) ∈ Λ' := (pmap_eq_one_iff _).mp (by
      rw [hD1', bOf_val, ← ellE_iota_mul]; exact hker _ (bOf τ (a * b)).2)
    have m2 : D2 (bOf τ b) ∈ Λ' := (pmap_eq_one_iff _).mp (by
      rw [hD2', hker _ (bOf τ b).2]; exact map_one (AbVar.ptMap (L := ℂ) (P.q.iota a)))
    have e1 := monodromy_line hφ _ m1 (c (a * b)) (fun t => by
      rw [hcb, bOf_val, ellE_iota_mul, hline1]; rfl)
    have e2 := monodromy_line hφ _ m2 (pushLoop (P.q.iota a) (c b)) (fun t => by
      rw [pushLoop_apply, hcb]; exact hline2 _ _)
    have h1 := congrArg Θ' (hact a b)
    simp only [loopClass, hΘ'] at h1
    rw [e1, e2, MulOpposite.op_inj] at h1
    exact (congrArg Subtype.val (Multiplicative.ofAdd.injective h1)).symm
  have hD : D1.restrictScalars ℝ = D2.restrictScalars ℝ := by
    apply ContinuousLinearMap.coe_injective
    refine LinearMap.ext_on (s := (Lτ : Set (Fin 2 → ℂ))) (IsZLattice.span_top (K := ℝ) (L := Lτ)) ?_
    intro v hv
    obtain ⟨b, hb⟩ := (bOf_bijective τ).2 ⟨v, hv⟩
    have hv' : v = (bOf τ b : Fin 2 → ℂ) := by rw [hb]
    rw [hv']; exact hagree b
  have hz' : D1 z = D2 z := congrArg (fun L : (Fin 2 → ℂ) →L[ℝ] (Fin g → ℂ) => L z) hD
  show Φu ((qmMat a).mulVec z) = Φu z ≫ (P.q.iota a).hom
  rw [← hD1', ← hD2', hz']

/-- **Lattice form ⇒ print form (GLUE, proved).** `e = Φu`, `β = ℓ_τ`, `c(b)` the straight loop to
`ℓ_τ(ι b) ∈ Λ_τ`; `exists_H1_of_isUniformization` gives `Λ_τ ≅ H₁`; `ι`-compatibility gives `ι_A(a)_* c(b) = c(ab)`
already as loops. -/
theorem print_of_lattice (hU : Uniformization.UniformizationLeafAll) {P : QML3 ℂ} {τ : UpperHalfPlane}
    {Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)}
    (hUn : IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu)
    (hio : IotaCompatible P Φu) : IsHodgeH1Print P τ := by
  haveI : DiscreteTopology (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    unfold BPAnalytic.QM.qmLattice; infer_instance
  haveI : IsZLattice ℝ (BPAnalytic.QM.qmLattice τ.im_pos.ne') := by
    unfold BPAnalytic.QM.qmLattice; infer_instance
  set Lτ := BPAnalytic.QM.qmLattice τ.im_pos.ne' with hLτ
  obtain ⟨he, hker, lp, hlp, hbij⟩ := exists_H1_of_isUniformization hU Φu hUn
  refine ⟨2, Φu, Y3Fix.ellE τ, fun b => lp (bOf τ b), he, fun b t => ?_, ?_, fun a b => ?_,
    Y3Fix.ellE_J τ⟩
  · rw [hlp]; rfl
  · exact (Function.Bijective.of_comp_iff _ (bOf_bijective τ)).mpr hbij
  · show loopClass _ = loopClass _
    congr 1
    refine Path.ext (funext fun t => ?_)
    show lp (bOf τ b) t ≫ (P.q.iota a).hom = lp (bOf τ (a * b)) t
    have h1 := hlp (bOf τ b) t
    have h2 := hlp (bOf τ (a * b)) t
    have h3 : Φu (((t : ℝ) : ℂ) • (bOf τ b : Fin 2 → ℂ)) ≫ (P.q.iota a).hom =
        Φu (((t : ℝ) : ℂ) • (bOf τ (a * b) : Fin 2 → ℂ)) := by
      rw [← hio, Matrix.mulVec_smul, bOf_val, bOf_val, ellE_iota_mul]
    exact (congrArg (· ≫ (P.q.iota a).hom) h1).trans (h3.trans h2.symm)

/-- **The print's `H₁` form is equivalent to y3-fix's `IsHodgeH1`** (both directions proved, given the textbook
uniformization `UniformizationLeafAll`, itself proved in the tree: `uniformizationLeafAll_proof`). -/
theorem print_iff_hodge (P : QML3 ℂ) (τ : UpperHalfPlane) : IsHodgeH1Print P τ ↔ Y3Fix.IsHodgeH1 P τ := by
  constructor
  · intro h
    obtain ⟨Φu, hu, hio⟩ := lattice_of_print uniformizationLeafAll_proof h
    exact Y3Fix.hodge_of_lattice hu hio
  · intro h
    obtain ⟨Φu, hu, hio⟩ := Y3Fix.lattice_of_hodge h
    exact print_of_lattice uniformizationLeafAll_proof hu hio

end Dict

/-! ## 5. `ℍ^±` with `B^×` versus `ℍ` with `B^×_+` (the print's `X = ℍ^±` and the leaf's `ℍ`) -/

section HPM

open ShimuraCFT UpperHalfPlane

/-- `ℍ^± = ℂ ∖ ℝ`, the print's `X` for `G = B^×` (the `B^×_ℝ = GL₂(ℝ)`-conjugacy class of `h`). -/
abbrev HPM : Type := {z : ℂ // z.im ≠ 0}

theorem im_num_div_denom (g : GL (Fin 2) ℝ) (z : ℂ) :
    (num g z / denom g z).im = (g.det : ℝ) * z.im / Complex.normSq (denom g z) := by
  rw [Complex.div_im, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [num, denom, Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem normSq_denom_pos (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : 0 < Complex.normSq (denom g z) :=
  Complex.normSq_pos.mpr (denom_ne_zero_of_im g hz)

/-- The Möbius action of `GL₂(ℝ)` on `ℍ^±`, `z ↦ (az + b)/(cz + d)`. -/
def mobPM (g : GL (Fin 2) ℝ) (z : HPM) : HPM :=
  ⟨num g z / denom g z, by
    rw [im_num_div_denom]
    exact div_ne_zero (mul_ne_zero g.det.ne_zero z.2) (normSq_denom_pos g z.2).ne'⟩

/-- **The print's relation on `ℍ^± × G(𝔸_f)`**: `(z, g) ~ (γz, γ g k)` with `γ ∈ B^×` (any sign of `nrd γ`),
`k ∈ K₃`: the double coset space `B^× \ (ℍ^± × (B ⊗ 𝔸_f)^× / K₃)` of the print. -/
def DCRelPM (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ) : Prop :=
  ∃ (gm : LeafQM.B) (hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0), mobPM (RayClassCFT.iotaGL gm hγ) z = z' ∧
    ∃ k ∈ K3Q, (g' : BAQ) = bEmb gm * (g : BAQ) * (k : BAQ)

/-- `ℍ ⊆ ℍ^±`. -/
def toPM (τ : UpperHalfPlane) : HPM := ⟨τ, τ.im_pos.ne'⟩

theorem det_iotaGL (gm : LeafQM.B) (hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0) :
    ((RayClassCFT.iotaGL gm hγ).det : ℝ) = (ShimuraGlue.nrdQ ℚ gm : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, RayClassCFT.iotaGL_coe, RayClassCFT.det_iota]

/-- **On `ℍ ⊆ ℍ^±` the print's relation is the leaf's `DCRel`** (only `γ ∈ B^×_+` can map `ℍ` into `ℍ`). -/
theorem dcRelPM_iff (τ τ' : UpperHalfPlane) (g g' : BAQˣ) :
    DCRelPM (toPM τ) g (toPM τ') g' ↔ DCRel τ g τ' g' := by
  constructor
  · rintro ⟨gm, hγ, hmob, k, hk, hg⟩
    have him := congrArg (fun z : HPM => z.1.im) hmob
    simp only [mobPM, toPM] at him
    rw [im_num_div_denom, det_iotaGL] at him
    have hpos : 0 < (ShimuraGlue.nrdQ ℚ gm : ℝ) := by
      have h1 : 0 < (τ' : ℂ).im := τ'.im_pos
      have h2 : 0 < (τ : ℂ).im := τ.im_pos
      have h3 := normSq_denom_pos (RayClassCFT.iotaGL gm hγ) τ.im_pos.ne'
      rw [← him] at h1
      by_contra hn
      push Not at hn
      have : (ShimuraGlue.nrdQ ℚ gm : ℝ) * (τ : ℂ).im / Complex.normSq (denom (RayClassCFT.iotaGL gm hγ) τ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn h2.le) h3.le
      linarith
    refine ⟨gm, by exact_mod_cast hpos, ⟨RayClassCFT.iotaGL gm hγ, rfl, ?_⟩, k, hk, hg⟩
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos (by rw [det_iotaGL]; exact hpos)]
    exact congrArg Subtype.val hmob
  · rintro ⟨gm, hpos, ⟨M, hM, hMτ⟩, k, hk, hg⟩
    have hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0 := hpos.ne'
    have hMeq : M = RayClassCFT.iotaGL gm hγ := Matrix.GeneralLinearGroup.ext fun i j => by
      rw [RayClassCFT.iotaGL_coe, ← hM]
    refine ⟨gm, hγ, Subtype.ext ?_, k, hk, hg⟩
    show num (RayClassCFT.iotaGL gm hγ) τ / denom (RayClassCFT.iotaGL gm hγ) τ = τ'
    rw [← hMeq, ← coe_smul_of_det_pos (by rw [hMeq, det_iotaGL]; exact_mod_cast hpos), hMτ]

/-- **Every point of `ℍ^± × G(𝔸_f)` is related to one in `ℍ × G(𝔸_f)`**: for `z ∈ ℍ⁻` use `μ = 1 + i ∈ 𝒪^×`,
`nrd μ = −1` (`RayClassCFT.nrd_mu`), which swaps the two half planes. With `dcRelPM_iff`, the inclusion
`ℍ × G(𝔸_f) → ℍ^± × G(𝔸_f)` identifies the leaf's `B^×_+ \ (ℍ × G(𝔸_f) / K₃)` with the print's
`B^× \ (ℍ^± × G(𝔸_f) / K₃)`. -/
theorem exists_upper (z : HPM) (g : BAQˣ) : ∃ (τ : UpperHalfPlane) (g' : BAQˣ), DCRelPM z g (toPM τ) g' := by
  rcases lt_or_gt_of_ne z.2 with hneg | hpos
  · have hμ : ShimuraGlue.nrdQ ℚ RayClassCFT.mu ≠ 0 := by rw [RayClassCFT.nrd_mu]; norm_num
    set w := mobPM (RayClassCFT.iotaGL RayClassCFT.mu hμ) z with hw
    have hwpos : 0 < w.1.im := by
      rw [hw]
      simp only [mobPM]
      rw [im_num_div_denom, det_iotaGL, RayClassCFT.nrd_mu]
      have h3 := normSq_denom_pos (RayClassCFT.iotaGL RayClassCFT.mu hμ) z.2
      push_cast
      exact div_pos (by nlinarith) h3
    let u : BAQˣ := ⟨bEmb RayClassCFT.mu, bEmb RayClassCFT.muInv,
      by rw [← map_mul, RayClassCFT.mu_mul, map_one], by rw [← map_mul, RayClassCFT.mul_mu, map_one]⟩
    refine ⟨⟨w.1, hwpos⟩, u * g, RayClassCFT.mu, hμ, Subtype.ext rfl, 1, RayClassCFT.K3Q_one, ?_⟩
    simp [u]
  · refine ⟨⟨z.1, hpos⟩, g, 1, by simp [ShimuraGlue.nrdQ_apply], Subtype.ext ?_, 1, RayClassCFT.K3Q_one, by simp⟩
    show num _ z.1 / denom _ z.1 = z.1
    simp [num, denom, RayClassCFT.iotaGL_coe, BPAnalytic.QM.iota]

end HPM

/-! ## 6. The sign of `h` and `B` versus `B^op` (checks against Deligne's conventions) -/

section Sign

open Complex

/-- `(τ, 1)ᵀ`. -/
def vτ (τ : UpperHalfPlane) : Fin 2 → ℂ := ![(τ : ℂ), 1]

/-- `J_τ` as a complex matrix. -/
def JC (τ : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℂ := (Y3Fix.Jmat τ).map (fun r : ℝ => (r : ℂ))

theorem JC_mulVec (τ : UpperHalfPlane) : (JC τ).mulVec (vτ τ) = Complex.I • vτ τ := by
  have h := Y3Fix.ellE_J τ 1
  rw [_root_.one_mul] at h
  funext i
  have hi := congrFun h i
  simp only [Y3Fix.ellE_apply, Y3Fix.ellF, Pi.smul_apply, smul_eq_mul] at hi
  fin_cases i <;> simp [JC, vτ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hi ⊢ <;>
    simp [Matrix.one_apply] at hi <;> linear_combination hi

/-- `J_τ² = −1`. -/
theorem Jmat_sq (τ : UpperHalfPlane) : Y3Fix.Jmat τ * Y3Fix.Jmat τ = -1 := by
  have hy : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Y3Fix.Jmat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- `J_τ` has trace `0`, so its canonical conjugate (the adjugate) is `−J_τ`: under the canonical involution
`x ↦ x̄` of `B_ℝ = M₂(ℝ)` (which turns left multiplications into right ones), right multiplication by `J_τ` becomes
left multiplication by `J̄_τ = −J_τ`. -/
theorem adjugate_Jmat (τ : UpperHalfPlane) : (Y3Fix.Jmat τ).adjugate = -Y3Fix.Jmat τ := by
  rw [Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Y3Fix.Jmat] <;> ring

/-- Two real matrices agreeing on `(τ, 1)ᵀ`, `τ ∉ ℝ`, are equal. -/
theorem real_mat_eq_of_vτ (τ : UpperHalfPlane) {X Y : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (X.map (fun r : ℝ => (r : ℂ))).mulVec (vτ τ) = (Y.map (fun r : ℝ => (r : ℂ))).mulVec (vτ τ)) :
    X = Y := by
  have hy : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  ext i j
  have hi := congrFun h i
  simp only [vτ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one] at hi
  have him := congrArg Complex.im hi
  have hre := congrArg Complex.re hi
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero,
    mul_one] at him hre
  have h0 : X i 0 = Y i 0 := by
    have : (X i 0 - Y i 0) * (τ : ℂ).im = 0 := by linear_combination him
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hy)
  have h1 : X i 1 = Y i 1 := by rw [h0] at hre; linarith
  fin_cases j
  · exact h0
  · exact h1

/-- `ι(γ)(τ, 1)ᵀ = j(γ, τ)(γτ, 1)ᵀ`. -/
theorem iota_mulVec_vτ (gm : LeafQM.B) (hγ : 0 < ShimuraGlue.nrdQ ℚ gm) (τ : UpperHalfPlane) :
    ((BPAnalytic.QM.iota gm).map (fun r : ℝ => (r : ℂ))).mulVec (vτ τ) =
      UpperHalfPlane.denom (RayClassCFT.iotaGL gm hγ.ne') τ •
        vτ (RayClassCFT.iotaGL gm hγ.ne' • τ) := by
  have hd := UpperHalfPlane.denom_ne_zero (RayClassCFT.iotaGL gm hγ.ne') τ
  have hdet : 0 < (RayClassCFT.iotaGL gm hγ.ne').det.val := by
    rw [det_iotaGL]; exact_mod_cast hγ
  funext i
  fin_cases i
  · simp only [vτ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
    have hd' : (τ : ℂ) * ((BPAnalytic.QM.iota gm 1 0 : ℝ) : ℂ) + ((BPAnalytic.QM.iota gm 1 1 : ℝ) : ℂ) ≠ 0 := by
      simpa [UpperHalfPlane.denom, RayClassCFT.iotaGL_coe, mul_comm] using hd
    have hd'' : ((BPAnalytic.QM.iota gm 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((BPAnalytic.QM.iota gm 1 1 : ℝ) : ℂ) ≠ 0 := by
      simpa [UpperHalfPlane.denom, RayClassCFT.iotaGL_coe] using hd
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, RayClassCFT.iotaGL_coe]
    field_simp
  · simp [vτ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom, RayClassCFT.iotaGL_coe]

/-- **`B^×_+`-equivariance of `τ ↦ h_τ`**: `ι(γ) J_τ = J_{γτ} ι(γ)` for `nrd γ > 0`. So right multiplication by
`ι(γ)⁻¹` carries `(B_ℝ, ·J_τ, 𝒪)` to `(B_ℝ, ·J_{γτ}, 𝒪γ⁻¹)`: the Hodge datum at `(τ, g)` to the one at `(γτ, γg)`
(`L_{γg} = L_g γ⁻¹`), compatibly with `DCRel`. -/
theorem iota_mul_Jmat (gm : LeafQM.B) (hγ : 0 < ShimuraGlue.nrdQ ℚ gm) (τ : UpperHalfPlane) :
    BPAnalytic.QM.iota gm * Y3Fix.Jmat τ =
      Y3Fix.Jmat (RayClassCFT.iotaGL gm hγ.ne' • τ) * BPAnalytic.QM.iota gm := by
  apply real_mat_eq_of_vτ τ
  have hm : ∀ X Y : Matrix (Fin 2) (Fin 2) ℝ, (X * Y).map (fun r : ℝ => (r : ℂ)) =
      X.map (fun r : ℝ => (r : ℂ)) * Y.map (fun r : ℝ => (r : ℂ)) := fun X Y =>
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [hm, hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change _ = (JC _).mulVec _
  change ((BPAnalytic.QM.iota gm).map (fun r : ℝ => (r : ℂ))).mulVec ((JC τ).mulVec (vτ τ)) = _
  rw [JC_mulVec, Matrix.mulVec_smul, iota_mulVec_vτ gm hγ, Matrix.mulVec_smul, JC_mulVec, smul_comm]

/-- **The Hodge filtration varies holomorphically** (Deligne's convention `h(z)` acts on `V^{p,q}` by
`z^{-p} z̄^{-q}`, so `F⁰ = V^{0,-1}` is the `−i`-eigenspace of `h(i)` on `V_ℂ`): with `h_τ(i)` acting on
`V = B` by right multiplication by `J_τ`, `F⁰ = {M ∈ M₂(ℂ) : M J_τ = −i M} = {M : M (τ, 1)ᵀ = 0}`, which depends
holomorphically on `τ`; and `V_ℂ/F⁰ ≅ ℂ²` by `M ↦ M (τ, 1)ᵀ` restricts on `V_ℝ` to `ℓ_τ`, which is `ℂ`-linear for
`J_τ` (`Y3Fix.ellE_J`): `Lie A = V_ℂ/F⁰` with `H₁(A, ℤ) = ℓ_τ(𝒪) = Λ_τ`. So the leaf's sign `β(M J_τ) = i β(M)`
is the one for which `τ ↦ [h_τ]` is holomorphic (the complex structure of `X⁺` in the print). -/
theorem F0_iff (τ : UpperHalfPlane) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * JC τ = -Complex.I • M ↔ M.mulVec (vτ τ) = 0 := by
  have hy : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hyc : ((τ : ℂ).im : ℂ) ≠ 0 := by exact_mod_cast hy
  constructor
  · intro h
    have h1 : (M * JC τ).mulVec (vτ τ) = Complex.I • M.mulVec (vτ τ) := by
      rw [← Matrix.mulVec_mulVec, JC_mulVec, Matrix.mulVec_smul]
    rw [h, Matrix.smul_mulVec] at h1
    have h2 : (2 * Complex.I) • M.mulVec (vτ τ) = 0 := by
      rw [two_mul, add_smul]; nth_rewrite 1 [← h1]; rw [neg_smul, neg_add_cancel]
    exact (smul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · intro h
    -- `J_τ + i = (τ, 1)ᵀ (1/y, −τ̄/y)`
    set w : Fin 2 → ℂ := ![1 / ((τ : ℂ).im : ℂ), -(starRingEnd ℂ (τ : ℂ)) / ((τ : ℂ).im : ℂ)] with hw
    have hJ : JC τ + Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.vecMulVec (vτ τ) w := by
      have hτ : (τ : ℂ) = (((τ : ℂ).re : ℝ) : ℂ) + (((τ : ℂ).im : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im _).symm
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [JC, Y3Fix.Jmat, Matrix.vecMulVec, vτ, hw, Matrix.one_apply] <;>
        (apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq, pow_two, Complex.mul_re, Complex.mul_im] <;> field_simp <;> ring)
    have h3 : M * (JC τ + Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
      rw [hJ, Matrix.mul_vecMulVec, h]
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h3
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h3

end Sign

/-! ## 7. The canonical-model leaf in the print's form -/

section Leaf

open LeafQM.AV.R1UnivRigid ShimuraCFT RayClassCFT
open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

/-- The holomorphic family `τ ↦ y(τ)` with fibres in the print's `H₁` form (`IsHodgeH1Print`). -/
def IsShimuraHolFamilyHP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧ IsHodgeH1Print P τ) ∧
  ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (yτ τ).left)

/-- **The print's uniformization `Ψ : ℍ^± × G(𝔸_f) → Y(ℂ)`**: onto; fibres the print's double cosets
`B^× \ (ℍ^± × G(𝔸_f) / K₃)` (`DCRelPM`); holomorphic in `τ ∈ ℍ` for every `g`; at `g = 1` the fibres in the
print's `H₁` form; Shimura's reciprocity law at CM points `z ∈ ℍ` (conventions `ε`, `δ` existential). -/
def DeligneBodyAtPM (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
    (∀ y : fieldPt ℂ ⟶ Y, ∃ z g, Ψ z g = y) ∧
    (∀ z g z' g', Ψ z g = Ψ z' g' ↔ DCRelPM z g z' g') ∧
    (∀ g, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ (toPM τ) g).left)) ∧
    IsShimuraHolFamilyHP Y Φ (fun τ => Ψ (toPM τ) 1) ∧
    ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (toPM z) g) = Ψ (toPM z) (qHatU q s ^ (ε : ℤ) * g)

/-- The moduli clause at `[τ, u]`, `u ∈ 𝒪̂^×` (`L_u = 𝒪`), in the print's `H₁` form. -/
def ModuliAtUnitsHP (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
  ∀ u ∈ OhatU, ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (Ψ (toPM τ) u) = M3.mk P ∧ IsHodgeH1Print P τ

/-- **LEAF (consequence form) `DeligneCanonicalModelY3EveryPrint`: Shimura's Main Theorem I in Deligne's form for
`Y₃`, stated as the print states it**, for every witness `(Y, Φ)` of the printed fine-moduli clause list
`Y3Fix.R1fpPropsAbP` (one object: `Y₃ = Sh_{K₃}(B^×, ℍ^±)`; no existence claim).

*Published statement* (locators recalled, UNVERIFIED; no network): G. Shimura, *Construction of class fields and
zeta functions of algebraic curves*, Ann. of Math. 85 (1967), Main Theorem I; P. Deligne, *Travaux de Shimura*,
Sém. Bourbaki 389 (1971), §4 (`Sh_K(ℂ) = G(ℚ) \ X × G(𝔸_f) / K` for `(G, X) = (B^×, ℍ^±)`; the point `[h, g]` is the
abelian variety `A` with `(H₁(A, ℤ), ι_*, h_A) ≅ (L_g, left multiplication, h)`, `L_g = B ∩ 𝒪̂ g⁻¹`) and §5 (Cor. 5.7 /
Ex. 5.8: the PEL moduli scheme is the canonical model over `E(G, X) = ℚ`, reciprocity at CM points).
Background only, not a source (lecture notes; it carries no rating): J. S. Milne, *Introduction to
Shimura varieties* (2005), §§5–8, 12–14.

*Lean form*: `Ψ : ℍ^± × (B ⊗ 𝔸_f)^× → Y(ℂ)` onto, with fibres exactly the print's `DCRelPM`; holomorphic on `ℍ`
for every `g` (on `ℍ⁻` it is then holomorphic too, `Ψ(μτ, g) = Ψ(τ, μ⁻¹g)`); the moduli clause at `[τ, u]`,
`τ ∈ ℍ`, `u ∈ 𝒪̂^×`, in the print's `H₁` form `IsHodgeH1Print` (genuine `H₁(A(ℂ), ℤ) = π₁(A(ℂ), 0)ᵃᵇ`, its
`𝒪`-action by functoriality, the complex structure of `Lie A` via a holomorphic homomorphism `e = exp_A ∘ L`);
reciprocity at CM points of `ℍ`.

*Form*: a consequence of the print (biholomorphism weakened to bijective and holomorphic in `τ`; moduli clause kept
at `𝒪̂^×` without the polarization and level structure; reciprocity only at CM points of `ℍ`; conventions `ε`, `δ`
existential). Reading risks: the polarized PEL problem (the polarization is unique and automatic: Lemma P on `H₁`,
`Y3Hodge.lemmaP_H1`, plus Riemann's theorem, STANDARD); the sign of `h` is fixed by holomorphy (`F0_iff`). -/
def DeligneCanonicalModelY3EveryPrint : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), Y3Fix.R1fpPropsAbP Y Φ →
    ∃ Ψ, DeligneBodyAtPM Y Φ Ψ ∧ ModuliAtUnitsHP Y Φ Ψ

theorem bodyH_of_PM {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : DeligneBodyAtPM Y Φ Ψ) :
    Y3Fix.DeligneBodyAtH Y Φ (fun τ g => Ψ (toPM τ) g) := by
  obtain ⟨h1, h2, h3, ⟨hm, hh⟩, h5⟩ := h
  refine ⟨fun y => ?_, fun τ g τ' g' => (h2 _ _ _ _).trans (dcRelPM_iff τ τ' g g'), h3,
    ⟨fun τ => ?_, hh⟩, h5⟩
  · obtain ⟨z, g, rfl⟩ := h1 y
    obtain ⟨τ, g', hrel⟩ := exists_upper z g
    exact ⟨τ, g', ((h2 z g (toPM τ) g').2 hrel).symm⟩
  · obtain ⟨P, hP, hH⟩ := hm τ
    exact ⟨P, hP, (print_iff_hodge P τ).1 hH⟩

theorem unitsH_of_PM {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : ModuliAtUnitsHP Y Φ Ψ) :
    Y3Fix.ModuliAtUnitsH Y Φ (fun τ g => Ψ (toPM τ) g) := by
  intro u hu τ
  obtain ⟨P, hP, hH⟩ := h u hu τ
  exact ⟨P, hP, (print_iff_hodge P τ).1 hH⟩

/-- **The old leaf from the print-form leaf** (GLUE, proved): restrict `Ψ` to `ℍ ⊂ ℍ^±`. Onto by `exists_upper`,
fibres by `dcRelPM_iff`, moduli clause by `print_iff_hodge`; the other clauses verbatim. -/
theorem deligneH_of_print (h : DeligneCanonicalModelY3EveryPrint) : Y3Fix.DeligneCanonicalModelY3EveryH := by
  intro Y Φ hY
  obtain ⟨Ψ, hb, hU⟩ := h Y Φ hY
  exact ⟨fun τ g => Ψ (toPM τ) g, bodyH_of_PM hb, unitsH_of_PM hU⟩

/-- The discharge of the research field from the print-form leaf (with y3-fix's `Y3FineModuliAbP` and the
textbook field `mumfordTorsionAlgClosed`). -/
theorem shimuraMainThmIDeligneY3AbU_of_printPM (hM : AvSplit.MumfordTorsionAlgClosed)
    (h1 : Y3Fix.Y3FineModuliAbP) (h2 : DeligneCanonicalModelY3EveryPrint) : ShimuraMainThmIDeligneY3AbU :=
  Y3Fix.shimuraMainThmIDeligneY3AbU_of_print hM h1 (deligneH_of_print h2)

end Leaf

/-! ## 8. Lemma P on the genuine `H₁(A(ℂ), ℤ)`

y3abu-strict's helpers (`ZInQKernel/Contrib/OneProof/ShimuraY3StrictLemmaP.lean` on `wip/y3abu-strict`, not on this
base; copied verbatim): the real embedding `ι_ℝ : B_ℝ → M₂(ℝ)` and the complex structure `j_τ ∈ B_ℝ`. -/

namespace LP

open RvQMPolar Matrix
open LeafQM (B)


/-- The real embedding `ι_ℝ : B_ℝ → M₂(ℝ)` (the extension of `BPAnalytic.QM.iota`). -/
def iotaR (y : BR) : Matrix (Fin 2) (Fin 2) ℝ :=
  y.re • 1 + y.imI • BPAnalytic.QM.Mi + y.imJ • BPAnalytic.QM.Mj + y.imK • (BPAnalytic.QM.Mi * BPAnalytic.QM.Mj)

theorem iotaR_mul (x y : BR) : iotaR (x * y) = iotaR x * iotaR y := by
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [iotaR, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp only [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)] <;> ring

/-- `ι_ℝ` extends N5's `ι` (`BPAnalytic.QM.iota`) on `B ⊆ B_ℝ`. -/
theorem iotaR_ofB (x : LeafQM.B) :
    iotaR ⟨(x.re : ℝ), (x.imI : ℝ), (x.imJ : ℝ), (x.imK : ℝ)⟩ = BPAnalytic.QM.iota x := by
  simp [iotaR, BPAnalytic.QM.iota]

/-- **The complex structure of `ℂ²/Λ_τ` on `H₁ ⊗ ℝ = B_ℝ`**: for `τ = s + it`,
`j_τ = (s√2/(2t)) i + ((3 + |τ|²)/(6t)) j + ((|τ|² − 3)√2/(12t)) k`, so that `ι(j_τ)(τ, 1)ᵀ = i (τ, 1)ᵀ`. -/
def jτ (τ : UpperHalfPlane) : BR :=
  ⟨0, τ.re * √2 / (2 * τ.im), (3 + τ.re ^ 2 + τ.im ^ 2) / (6 * τ.im),
    (τ.re ^ 2 + τ.im ^ 2 - 3) * √2 / (12 * τ.im)⟩

theorem jτ_sq (τ : UpperHalfPlane) : jτ τ * jτ τ = -1 := by
  have ht : τ.im ≠ 0 := τ.im_pos.ne'
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext <;> simp [jτ] <;> field_simp <;> ring_nf <;> simp only [h2] <;> ring

theorem jτ_imJ_pos (τ : UpperHalfPlane) : 0 < (jτ τ).imJ := by
  simp only [jτ]
  have := τ.im_pos
  positivity

theorem iotaR_jτ (τ : UpperHalfPlane) : iotaR (jτ τ) =
    !![τ.re / τ.im, -(τ.re ^ 2 + τ.im ^ 2) / τ.im; 1 / τ.im, -τ.re / τ.im] := by
  have ht : τ.im ≠ 0 := τ.im_pos.ne'
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [iotaR, jτ, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> (try simp only [h2]) <;> ring

end LP

section LemmaP

open HDec.HSyn.G0Split.FibreQM (qmMat IotaCompatible)

/-- `P ↦ P ≫ f` on `A(ℂ)`, a continuous map. -/
def ptMapC {A : AbVar ℂ} (f : AbVar.End A) : C(A.Pt ℂ, A.Pt ℂ) :=
  ⟨fun P => P ≫ f.hom, continuous_postcomp (X := A.X) (Y := A.X) f.hom⟩

theorem ptMapC_one {A : AbVar ℂ} (f : AbVar.End A) : ptMapC f 1 = 1 :=
  map_one (AbVar.ptMap (L := ℂ) f)

/-- **`f_* : H₁(A(ℂ), ℤ) → H₁(A(ℂ), ℤ)`**, functoriality of `π₁` (Mathlib's `FundamentalGroup.mapOfEq`) and of the
abelianization, for an endomorphism `f` of `A`. -/
def h1Act {A : AbVar ℂ} (f : AbVar.End A) : H1 A →* H1 A :=
  Abelianization.map (FundamentalGroup.mapOfEq (ptMapC f) (ptMapC_one f))

theorem h1Act_loopClass {A : AbVar ℂ} (f : AbVar.End A) (lp : Path (1 : A.Pt ℂ) 1) :
    h1Act f (loopClass lp) = loopClass (pushLoop f lp) := by
  have h := Abelianization.map_of (FundamentalGroup.mapOfEq (ptMapC f) (ptMapC_one f))
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk lp))
  refine h.trans (congrArg Abelianization.of ?_)
  rw [FundamentalGroup.mapOfEq_apply]
  rfl

/-- Straight loops add: `[t ↦ e(t(u + v))] = [t ↦ e(tu)] · [t ↦ e(tv)]` in `H₁` (monodromy is a homomorphism and
injective). -/
theorem loopClass_add (hU : Uniformization.UniformizationLeafAll) {A : AbVar ℂ} {n : ℕ}
    {e : (Fin n → ℂ) → CPts A (RingHom.id ℂ)} (he : IsAnalyticHom (RingHom.id ℂ) e)
    {u v : Fin n → ℂ} (lu lv luv : Path (1 : A.Pt ℂ) 1)
    (hu : ∀ t : unitInterval, lu t = e (((t : ℝ) : ℂ) • u))
    (hv : ∀ t : unitInterval, lv t = e (((t : ℝ) : ℂ) • v))
    (huv : ∀ t : unitInterval, luv t = e (((t : ℝ) : ℂ) • (u + v))) :
    loopClass luv = loopClass lu * loopClass lv := by
  obtain ⟨g, Λ', hd, hz, φ, hφ⟩ := hU A
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong
    (ZInQ.HomLattice.isStrongUnif_of_bp hφ) he
  have hD' : ∀ w, pmap φ (D w) = e w := hD
  have hcov := isCov hφ
  set Θ := hcov.fundamentalGroupToMulOpposite e0 with hΘ
  have hΘinj : Function.Injective Θ := hcov.fundamentalGroupToMulOpposite_injective e0
  let Θ' : H1 A →* (Multiplicative Λ'.toAddSubgroup)ᵐᵒᵖ := Abelianization.lift Θ
  have hΘ' : ∀ x, Θ' (Abelianization.of x) = Θ x := fun x => Abelianization.lift_apply_of Θ x
  have hΘ'inj : Function.Injective Θ' := by
    intro x y hxy
    obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
    have h2 : Θ' (Abelianization.of x0) = Θ' (Abelianization.of y0) := hxy
    rw [hΘ', hΘ'] at h2
    show Abelianization.of x0 = Abelianization.of y0
    rw [hΘinj h2]
  have mem : ∀ (w : Fin n → ℂ) (l : Path (1 : A.Pt ℂ) 1),
      (∀ t : unitInterval, l t = e (((t : ℝ) : ℂ) • w)) → D w ∈ Λ' := by
    intro w l hl
    refine (pmap_eq_one_iff (φ := φ) _).mp ?_
    have h1 := hl 1
    simp only [Set.Icc.coe_one, Complex.ofReal_one, one_smul] at h1
    rw [hD', ← h1]; exact l.target
  have key : ∀ (w : Fin n → ℂ) (l : Path (1 : A.Pt ℂ) 1) (hl : ∀ t : unitInterval, l t = e (((t : ℝ) : ℂ) • w)),
      Θ' (loopClass l) = MulOpposite.op (Multiplicative.ofAdd (⟨D w, mem w l hl⟩ : Λ'.toAddSubgroup)) := by
    intro w l hl
    simp only [loopClass, hΘ']
    refine monodromy_line hφ (D w) (mem w l hl) l fun t => ?_
    rw [hl t, ← hD', map_smul, Complex.coe_smul]
  apply hΘ'inj
  rw [map_mul, key _ _ huv, key _ _ hu, key _ _ hv, ← MulOpposite.op_mul, ← ofAdd_add]
  congr 2
  apply Subtype.ext
  simp [map_add, add_comm]

/-- The print's data `(n, e, β, c)` of `IsHodgeH1Print`. -/
def HodgeData (P : QML3 ℂ) (τ : UpperHalfPlane) (n : ℕ) (e : (Fin n → ℂ) → CPts P.A (RingHom.id ℂ))
    (β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ)) (c : O → Path (1 : P.A.Pt ℂ) 1) : Prop :=
  IsAnalyticHom (RingHom.id ℂ) e ∧
    (∀ (b : O) (t : unitInterval), c b t = e (((t : ℝ) : ℂ) • β (BPAnalytic.QM.iota (b : B)))) ∧
    Function.Bijective (fun b => loopClass (c b)) ∧
    (∀ a b : O, loopClass (pushLoop (P.q.iota a) (c b)) = loopClass (c (a * b))) ∧
    (∀ M, β (M * Y3Fix.Jmat τ) = Complex.I • β M)

theorem isHodgeH1Print_iff (P : QML3 ℂ) (τ : UpperHalfPlane) :
    IsHodgeH1Print P τ ↔ ∃ n e β c, HodgeData P τ n e β c := Iff.rfl

theorem iota_add (x y : B) : BPAnalytic.QM.iota (x + y) = BPAnalytic.QM.iota x + BPAnalytic.QM.iota y := by
  simp only [BPAnalytic.QM.iota, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
    QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add, Rat.cast_add, add_smul]
  abel

/-- The iso `c : 𝒪 → H₁(A, ℤ)` of the print's data is additive. -/
theorem cl_add (hU : Uniformization.UniformizationLeafAll) {P : QML3 ℂ} {τ : UpperHalfPlane} {n : ℕ}
    {e : (Fin n → ℂ) → CPts P.A (RingHom.id ℂ)} {β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ)}
    {c : O → Path (1 : P.A.Pt ℂ) 1} (hD : HodgeData P τ n e β c) (b b' : O) :
    loopClass (c (b + b')) = loopClass (c b) * loopClass (c b') := by
  obtain ⟨he, hc, -, -, -⟩ := hD
  refine loopClass_add hU he (c b) (c b') (c (b + b')) (hc b) (hc b') fun t => ?_
  rw [hc, Subring.coe_add, iota_add, map_add]


/-! ### The data of the polarization -/

/-- N5's `ℤ`-basis `1, i, (1+j)/2, (i+k)/2` of `𝒪` (`RvQMPolar.oBasis`), as elements of `𝒪`. -/
def oB (r : Fin 4) : O :=
  ⟨RvQMPolar.oBasis r, RvQMPolar.mem_O.mpr ⟨Pi.single r 1, by
    fin_cases r <;> ext <;> simp [RvQMPolar.oBasis, LeafQM.ofInt, Pi.single_apply] <;> norm_num⟩⟩

/-- `i, j, k ∈ 𝒪`. -/
def iO : O := ⟨⟨0, 1, 0, 0⟩, RvQMPolar.mem_O.mpr ⟨![0, 1, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩
def jO : O := ⟨⟨0, 0, 1, 0⟩, RvQMPolar.mem_O.mpr ⟨![-1, 0, 2, 0], by ext <;> simp [LeafQM.ofInt]⟩⟩
def kO : O := ⟨⟨0, 0, 0, 1⟩, RvQMPolar.mem_O.mpr ⟨![0, -1, 0, 2], by ext <;> simp [LeafQM.ofInt]⟩⟩

/-- `†` on `𝒪` (`RvQMPolar.dag_mem`). -/
def dagO (a : O) : O := ⟨RvQMPolar.dag (a : B), RvQMPolar.dag_mem a.2⟩

/-- **A principal polarization of type `μ` on `H₁(A(ℂ), ℤ)`, as a Riemann form** (Mumford, *Abelian varieties*,
§1 and §21: a Riemann form `E` on `H₁` is alternating, `E(ix, iy) = E(x, y)` and `E(ix, x) > 0`; principal: Gram
determinant `1` on a `ℤ`-basis; type `μ`: its Rosati involution restricts to `x ↦ x† = μ⁻¹ x̄ μ` on `𝒪`): `E` is a
biadditive alternating `ℤ`-valued form on the genuine `H₁(A(ℂ), ℤ)`; `ι_A(a)_*` (`h1Act`) has adjoint `ι_A(a†)_*`;
the Gram determinant on the `ℤ`-basis `c(1), c(i), c((1+j)/2), c((i+k)/2)` is `1`; and its real extension `F` to
`H₁(A, ℝ) = Lie A = ℂⁿ` (through the data `e`, `β`, `c` of the print's identification) is `i`-invariant and positive
(`F(iv, v) > 0`). -/
def IsPrincipalRiemannMu {P : QML3 ℂ} {n : ℕ} (β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ))
    (c : O → Path (1 : P.A.Pt ℂ) 1) (E : H1 P.A → H1 P.A → ℤ) : Prop :=
  (∀ x y z, E (x * y) z = E x z + E y z) ∧ (∀ x y z, E x (y * z) = E x y + E x z) ∧
  (∀ x, E x x = 0) ∧
  (∀ a : O, ∀ x y, E (h1Act (P.q.iota a) x) y = E x (h1Act (P.q.iota (dagO a)) y)) ∧
  (Matrix.of fun r s => (E (loopClass (c (oB r))) (loopClass (c (oB s))) : ℚ)).det = 1 ∧
  ∃ F : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ,
    (∀ b b' : O, F (β (BPAnalytic.QM.iota (b : B))) (β (BPAnalytic.QM.iota (b' : B))) =
      E (loopClass (c b)) (loopClass (c b'))) ∧
    (∀ v w, F (Complex.I • v) (Complex.I • w) = F v w) ∧ ∀ v, v ≠ 0 → 0 < F (Complex.I • v) v

/-! ### Real-linear algebra on `B_ℝ` -/

/-- `B → B_ℝ`. -/
def embR (x : B) : RvQMPolar.BR := ⟨(x.re : ℝ), (x.imI : ℝ), (x.imJ : ℝ), (x.imK : ℝ)⟩

theorem E0R_embR (x y : B) : RvQMPolar.E0R (embR x) (embR y) = (RvQMPolar.E0 x y : ℝ) := by
  simp [RvQMPolar.E0R, RvQMPolar.E0, RvQMPolar.trd, RvQMPolar.muInvR, RvQMPolar.muInv, embR]

/-- `E0R` as an `ℝ`-bilinear form. -/
def E0RL : LinearMap.BilinForm ℝ RvQMPolar.BR :=
  LinearMap.mk₂ ℝ RvQMPolar.E0R
    (fun x x' y => by simp [RvQMPolar.E0R, RvQMPolar.muInvR]; ring)
    (fun c x y => by simp [RvQMPolar.E0R, RvQMPolar.muInvR]; ring)
    (fun x y y' => by simp [RvQMPolar.E0R, RvQMPolar.muInvR]; ring)
    (fun c x y => by simp [RvQMPolar.E0R, RvQMPolar.muInvR]; ring)

theorem E0RL_apply (x y : RvQMPolar.BR) : E0RL x y = RvQMPolar.E0R x y := rfl

/-- `ι_ℝ` as an `ℝ`-linear map. -/
def iotaRL : RvQMPolar.BR →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun := LP.iotaR
  map_add' x y := by
    simp only [LP.iotaR, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, add_smul]
    abel
  map_smul' c x := by
    simp only [LP.iotaR, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
      QuaternionAlgebra.imK_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

theorem iotaR_jτ_eq (τ : UpperHalfPlane) : LP.iotaR (LP.jτ τ) = Y3Fix.Jmat τ := by
  rw [LP.iotaR_jτ]; rfl

theorem iotaR_one : LP.iotaR 1 = 1 := by
  simp [LP.iotaR]

/-- The standard basis vectors `1, i, j, k` of `B_ℝ` come from `𝒪`. -/
def stdO : Fin 4 → O := ![1, iO, jO, kO]

theorem basisOneIJK_eq (r : Fin 4) :
    QuaternionAlgebra.basisOneIJK (2 : ℝ) 0 (-3) r = embR (stdO r : B) := by
  fin_cases r <;> ext <;> simp [QuaternionAlgebra.basisOneIJK, embR, stdO, iO, jO, kO]


/-! ### Lemma P on `H₁`: uniqueness -/

theorem O_two_smul_decomp (z : O) : ∃ m : Fin 4 → ℤ,
    (2 : ℤ) • z = (2 * m 0 + m 2) • (1 : O) + (2 * m 1 + m 3) • iO + m 2 • jO + m 3 • kO ∧
    (z : B).imJ = (m 2 : ℚ) / 2 ∧ (z : B).imK = (m 3 : ℚ) / 2 := by
  obtain ⟨m, hm⟩ := RvQMPolar.mem_O.mp z.2
  refine ⟨m, Subtype.ext ?_, by rw [hm]; simp [LeafQM.ofInt], by rw [hm]; simp [LeafQM.ofInt]⟩
  simp only [AddSubgroupClass.coe_zsmul, Subring.coe_add, OneMemClass.coe_one, ← Int.cast_smul_eq_zsmul ℚ]
  rw [hm]
  ext <;> simp [LeafQM.ofInt, iO, jO, kO] <;> ring

/-- **Lemma P on `H₁`, uniqueness half (GLUE, proved).** A principal Riemann form of type `μ` on the genuine
`H₁(A(ℂ), ℤ)` is `E₀ = trd(μ⁻¹ x ȳ)` under the print's identification `c : 𝒪 ≅ H₁(A, ℤ)`. The argument of
`RvQMPolar.eq_smul_E0` run on `𝒪` (Rosati: `E(x, y) = f(x† y)`, alternation at `1, 1+i, 1+j` gives
`E = r E₀`), principal gives `r = ±1` (`det(r · gram) = r⁴`), and the real extension `F` restricted along
`β ∘ ι_ℝ` is `r · E₀ ⊗ ℝ` (equal on the basis `1, i, j, k ∈ 𝒪`); positivity at `x = 1` with
`F(i v, v) = r E₀(j_τ, 1)` and `RvQMPolar.riemann_sign` (`imJ(j_τ) > 0`) gives `r = 1`. -/
theorem eq_E0_of_principalRiemann (hU : Uniformization.UniformizationLeafAll) {P : QML3 ℂ}
    {τ : UpperHalfPlane} {n : ℕ} {e : (Fin n → ℂ) → CPts P.A (RingHom.id ℂ)}
    {β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ)} {c : O → Path (1 : P.A.Pt ℂ) 1}
    (hD : HodgeData P τ n e β c) {E : H1 P.A → H1 P.A → ℤ} (hE : IsPrincipalRiemannMu β c E) :
    ∀ b b' : O, (E (loopClass (c b)) (loopClass (c b')) : ℚ) = RvQMPolar.E0 b b' := by
  obtain ⟨hbl, hbr, halt, hros, hdet, F, hF1, hF2, hF3⟩ := hE
  have hact := hD.2.2.2.1
  have hJ := hD.2.2.2.2
  set EO : O → O → ℚ := fun b b' => (E (loopClass (c b)) (loopClass (c b')) : ℚ) with hEO
  have hadd2 : ∀ b b' b'', EO b (b' + b'') = EO b b' + EO b b'' := by
    intro b b' b''; simp only [hEO, cl_add hU hD, hbr]; push_cast; ring
  have hrosO : ∀ a b b'' : O, EO (a * b) b'' = EO b (dagO a * b'') := by
    intro a b b''
    simp only [hEO]
    rw [← hact a b, ← h1Act_loopClass, hros a, h1Act_loopClass, hact]
  let fO : O →+ ℚ :=
    { toFun := EO 1
      map_zero' := by
        have h := hadd2 1 0 0
        simp only [add_zero] at h
        linarith
      map_add' := hadd2 1 }
  have hfO : ∀ x, fO x = EO 1 x := fun x => rfl
  have hE1 : ∀ x y : O, EO x y = fO (dagO x * y) := by
    intro x y; rw [hfO, ← hrosO x 1 y, _root_.mul_one]
  have hf0 : ∀ x : O, fO (dagO x * x) = 0 := by
    intro x; rw [← hE1]; simp only [hEO, halt, Int.cast_zero]
  have e1 : dagO 1 * 1 = (1 : O) := Subtype.ext (by simp [dagO, RvQMPolar.dag_one])
  have r1 : fO 1 = 0 := by have h := hf0 1; rwa [e1] at h
  have e2 : dagO (1 + iO) * (1 + iO) = (3 : ℤ) • (1 : O) + (2 : ℤ) • iO := by
    apply Subtype.ext
    simp only [dagO, Subring.coe_mul, Subring.coe_add, OneMemClass.coe_one, AddSubgroupClass.coe_zsmul,
      ← Int.cast_smul_eq_zsmul ℚ]
    ext <;> simp [RvQMPolar.dag, RvQMPolar.muInv, RvQMPolar.mu, iO] <;> norm_num
  have r2 : fO iO = 0 := by
    have h := hf0 (1 + iO)
    rw [e2, map_add, map_zsmul, map_zsmul, r1] at h
    simp at h
    linarith
  have e3 : dagO (1 + jO) * (1 + jO) = (10 : ℤ) • (1 : O) + (6 : ℤ) • iO + (-2 : ℤ) • (jO + kO) := by
    apply Subtype.ext
    simp only [dagO, Subring.coe_mul, Subring.coe_add, OneMemClass.coe_one, AddSubgroupClass.coe_zsmul,
      ← Int.cast_smul_eq_zsmul ℚ]
    ext <;> simp [RvQMPolar.dag, RvQMPolar.muInv, RvQMPolar.mu, iO, jO, kO] <;> norm_num
  have r3 : fO kO = - fO jO := by
    have h := hf0 (1 + jO)
    rw [e3, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_add, r1, r2] at h
    simp at h
    linarith
  have hfz : ∀ z : O, fO z = ((z : B).imJ - (z : B).imK) * fO jO := by
    intro z
    obtain ⟨m, hm, hJ', hK'⟩ := O_two_smul_decomp z
    have h := congrArg fO hm
    rw [map_zsmul, map_add, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul, r1, r2, r3] at h
    rw [hJ', hK']
    simp only [smul_eq_mul, zsmul_eq_mul] at h
    push_cast at h
    linarith
  set r : ℚ := -(fO jO) / 2 with hr
  have hEr : ∀ x y : O, EO x y = r * RvQMPolar.E0 x y := by
    intro x y
    rw [hE1, hfz]
    simp only [dagO, Subring.coe_mul, hr]
    simp only [RvQMPolar.E0, RvQMPolar.trd, RvQMPolar.dag, RvQMPolar.muInv, RvQMPolar.mu]
    simp
    ring
  -- principal: `r = ±1`
  have hM : (Matrix.of fun r' s => (E (loopClass (c (oB r'))) (loopClass (c (oB s))) : ℚ)) =
      r • RvQMPolar.gram := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show ((E (loopClass (c (oB a))) (loopClass (c (oB b))) : ℚ)) = EO (oB a) (oB b) from rfl, hEr]
    rw [show ((oB a : O) : B) = RvQMPolar.oBasis a from rfl, show ((oB b : O) : B) = RvQMPolar.oBasis b from rfl,
      RvQMPolar.E0_gram]
  rw [hM, Matrix.det_smul, RvQMPolar.gram_det, Fintype.card_fin, _root_.mul_one] at hdet
  have hr4 : (r ^ 2 - 1) * (r ^ 2 + 1) = 0 := by linear_combination hdet
  have hr2 : r ^ 2 = 1 := by
    rcases mul_eq_zero.1 hr4 with h | h
    · linarith
    · nlinarith [sq_nonneg r]
  -- the real extension: `F ∘ (β ∘ ι_ℝ) = r · E₀ ⊗ ℝ`
  let Lβ : RvQMPolar.BR →ₗ[ℝ] (Fin n → ℂ) := β.toLinearMap ∘ₗ iotaRL
  have hG : F.compl₁₂ Lβ Lβ = (r : ℝ) • E0RL := by
    refine LinearMap.BilinForm.ext_basis (QuaternionAlgebra.basisOneIJK (2 : ℝ) 0 (-3)) fun i j => ?_
    rw [basisOneIJK_eq, basisOneIJK_eq]
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul, E0RL_apply, E0R_embR]
    show F (β (LP.iotaR (embR _))) (β (LP.iotaR (embR _))) = _
    simp only [show ∀ x : B, LP.iotaR (embR x) = BPAnalytic.QM.iota x from LP.iotaR_ofB]
    rw [hF1]
    have h := hEr (stdO i) (stdO j)
    simp only [hEO] at h
    rw [show ((E (loopClass (c (stdO i))) (loopClass (c (stdO j))) : ℤ) : ℝ) =
      (((E (loopClass (c (stdO i))) (loopClass (c (stdO j))) : ℤ) : ℚ) : ℝ) by push_cast; rfl, h]
    push_cast; ring
  -- positivity fixes the sign
  have hv : Lβ 1 ≠ 0 := by
    show β (LP.iotaR 1) ≠ 0
    rw [iotaR_one, Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
  have hpos := hF3 _ hv
  have hIv : Complex.I • Lβ 1 = Lβ (1 * LP.jτ τ) := by
    show Complex.I • β (LP.iotaR 1) = β (LP.iotaR (1 * LP.jτ τ))
    rw [LP.iotaR_mul, iotaR_jτ_eq, hJ]
  rw [hIv] at hpos
  have hpos' : 0 < (r : ℝ) * RvQMPolar.E0R (1 * LP.jτ τ) 1 := by
    have h := congrArg (fun B => B (1 * LP.jτ τ) 1) hG
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul, E0RL_apply] at h
    rw [← h]; exact hpos
  have hE0pos : 0 < RvQMPolar.E0R (1 * LP.jτ τ) 1 := by
    rcases RvQMPolar.riemann_sign (LP.jτ τ) (LP.jτ_sq τ) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h 1 one_ne_zero
    · exact absurd h (not_lt.2 (LP.jτ_imJ_pos τ).le)
  have hrpos : (0 : ℝ) < r := pos_of_mul_pos_left hpos' hE0pos.le
  have hr1 : r = 1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · have : (r : ℝ) = -1 := by exact_mod_cast (by linarith : r = -1)
      linarith
  intro b b'
  have h := hEr b b'
  rw [hr1, _root_.one_mul] at h
  exact h


/-! ### Lemma P on `H₁`: existence -/

theorem iotaR_injective : Function.Injective LP.iotaR := by
  have hs : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  intro x y h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [LP.iotaR, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hre : x.re = y.re := by nlinarith
  have hI : x.imI = y.imI := by
    have : (x.imI - y.imI) * √2 = 0 := by linear_combination (h00 - h11) / 2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
  have hK : x.imK = y.imK := by
    have : (x.imK - y.imK) * √2 = 0 := by linear_combination -(h01 + 3 * h10) / 6
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
  have hJ : x.imJ = y.imJ := by linear_combination h10 + √2 * hK
  ext <;> assumption

/-- `ι_ℝ : B_ℝ ≅ M₂(ℝ)`. -/
def iotaRE : RvQMPolar.BR ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  LinearEquiv.ofBijective iotaRL ⟨iotaR_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]; simp)).1 iotaR_injective⟩

theorem iotaRE_apply (x : RvQMPolar.BR) : iotaRE x = LP.iotaR x := rfl

theorem iotaRE_symm_iota (b : B) : iotaRE.symm (BPAnalytic.QM.iota b) = embR b := by
  apply iotaRE.injective
  rw [LinearEquiv.apply_symm_apply, iotaRE_apply]
  exact (LP.iotaR_ofB b).symm

theorem iotaRE_symm_mul_J (τ : UpperHalfPlane) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    iotaRE.symm (X * Y3Fix.Jmat τ) = iotaRE.symm X * LP.jτ τ := by
  apply iotaRE.injective
  rw [LinearEquiv.apply_symm_apply, iotaRE_apply, LP.iotaR_mul, iotaR_jτ_eq, ← iotaRE_apply,
    LinearEquiv.apply_symm_apply]

/-- `E₀` on `𝒪` is `ℤ`-valued. -/
theorem E0_intO (b b' : O) : ∃ z : ℤ, RvQMPolar.E0 b b' = z := by
  obtain ⟨n, hn⟩ := RvQMPolar.mem_O.mp b.2
  obtain ⟨m, hm⟩ := RvQMPolar.mem_O.mp b'.2
  rw [hn, hm]; exact RvQMPolar.E0_int n m

/-- `E₀ : 𝒪 × 𝒪 → ℤ`. -/
def E0Z (b b' : O) : ℤ := Classical.choose (E0_intO b b')

theorem E0Z_spec (b b' : O) : (E0Z b b' : ℚ) = RvQMPolar.E0 b b' := (Classical.choose_spec (E0_intO b b')).symm

theorem E0Z_add_left (a b c : O) : E0Z (a + b) c = E0Z a c + E0Z b c := by
  have h : (E0Z (a + b) c : ℚ) = E0Z a c + E0Z b c := by
    rw [E0Z_spec, E0Z_spec, E0Z_spec, Subring.coe_add, ← RvQMPolar.E0bil_apply, map_add,
      LinearMap.add_apply, RvQMPolar.E0bil_apply, RvQMPolar.E0bil_apply]
  exact_mod_cast h

theorem E0Z_add_right (a b c : O) : E0Z a (b + c) = E0Z a b + E0Z a c := by
  have h : (E0Z a (b + c) : ℚ) = E0Z a b + E0Z a c := by
    rw [E0Z_spec, E0Z_spec, E0Z_spec, Subring.coe_add, ← RvQMPolar.E0bil_apply, map_add,
      RvQMPolar.E0bil_apply, RvQMPolar.E0bil_apply]
  exact_mod_cast h

/-- **Lemma P on `H₁`, existence half (GLUE, proved).** `E₀`, transported to the genuine `H₁(A(ℂ), ℤ)` by the
print's `c`, is a principal Riemann form of type `μ`: its real extension is `E₀ ⊗ ℝ ∘ ι_ℝ⁻¹ ∘ β⁻¹`, `i`-invariant
by `RvQMPolar.E0R_mul_j` (`j_τ² = −1`) and positive by `RvQMPolar.riemann_sign` (`imJ(j_τ) > 0`). -/
theorem exists_principalRiemann (hU : Uniformization.UniformizationLeafAll) {P : QML3 ℂ}
    {τ : UpperHalfPlane} {n : ℕ} {e : (Fin n → ℂ) → CPts P.A (RingHom.id ℂ)}
    {β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ)} {c : O → Path (1 : P.A.Pt ℂ) 1}
    (hD : HodgeData P τ n e β c) : ∃ E : H1 P.A → H1 P.A → ℤ, IsPrincipalRiemannMu β c E := by
  have hbij := hD.2.2.1
  have hact := hD.2.2.2.1
  have hJ := hD.2.2.2.2
  let cl : O → H1 P.A := fun b => loopClass (c b)
  let ce : O ≃ H1 P.A := Equiv.ofBijective cl hbij
  have hce : ∀ b, ce b = loopClass (c b) := fun b => rfl
  have hinv : ∀ b, ce.symm (loopClass (c b)) = b := fun b => ce.symm_apply_apply b
  have hmul : ∀ x y, ce.symm (x * y) = ce.symm x + ce.symm y := by
    intro x y
    apply ce.injective
    rw [ce.apply_symm_apply, hce, cl_add hU hD, ← hce, ← hce, ce.apply_symm_apply, ce.apply_symm_apply]
  let E : H1 P.A → H1 P.A → ℤ := fun x y => E0Z (ce.symm x) (ce.symm y)
  have hEc : ∀ b b', E (loopClass (c b)) (loopClass (c b')) = E0Z b b' := fun b b' => by
    simp only [E, hinv]
  have hh1 : ∀ (a b : O), h1Act (P.q.iota a) (loopClass (c b)) = loopClass (c (a * b)) := fun a b => by
    rw [h1Act_loopClass, hact]
  -- the real extension
  let L : (Fin n → ℂ) →ₗ[ℝ] RvQMPolar.BR := iotaRE.symm.toLinearMap ∘ₗ β.symm.toLinearMap
  have hL : ∀ v, L v = iotaRE.symm (β.symm v) := fun v => rfl
  have hLI : ∀ v, L (Complex.I • v) = L v * LP.jτ τ := by
    intro v
    rw [hL, hL, ← iotaRE_symm_mul_J]
    congr 1
    apply β.injective
    rw [LinearEquiv.apply_symm_apply, hJ, LinearEquiv.apply_symm_apply]
  refine ⟨E, fun x y z => ?_, fun x y z => ?_, fun x => ?_, fun a x y => ?_, ?_,
    E0RL.compl₁₂ L L, fun b b' => ?_, fun v w => ?_, fun v hv => ?_⟩
  · simp only [E, hmul, E0Z_add_left]
  · simp only [E, hmul, E0Z_add_right]
  · have h : (E x x : ℚ) = 0 := by simp only [E, E0Z_spec, RvQMPolar.E0_alt]
    exact_mod_cast h
  · obtain ⟨b, rfl⟩ := hbij.2 x
    obtain ⟨b'', rfl⟩ := hbij.2 y
    simp only [hh1, hEc]
    have h : (E0Z (a * b) b'' : ℚ) = E0Z b (dagO a * b'') := by
      rw [E0Z_spec, E0Z_spec, Subring.coe_mul, Subring.coe_mul, RvQMPolar.E0_rosati]; rfl
    exact_mod_cast h
  · have hM : (Matrix.of fun r s => (E (loopClass (c (oB r))) (loopClass (c (oB s))) : ℚ)) =
        RvQMPolar.gram := by
      ext r s
      rw [Matrix.of_apply, hEc, E0Z_spec]
      exact RvQMPolar.E0_gram r s
    rw [hM, RvQMPolar.gram_det]
  · simp only [LinearMap.compl₁₂_apply, E0RL_apply, hL, LinearEquiv.symm_apply_apply, iotaRE_symm_iota,
      E0R_embR, hEc]
    rw [← E0Z_spec]; push_cast; rfl
  · simp only [LinearMap.compl₁₂_apply, E0RL_apply, hLI]
    exact RvQMPolar.E0R_mul_j _ _ _ (LP.jτ_sq τ)
  · simp only [LinearMap.compl₁₂_apply, E0RL_apply, hLI]
    have hx : L v ≠ 0 := by
      rw [hL, Ne, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff]; exact hv
    rcases RvQMPolar.riemann_sign (LP.jτ τ) (LP.jτ_sq τ) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h _ hx
    · exact absurd h (not_lt.2 (LP.jτ_imJ_pos τ).le)

/-- **Lemma P in the print's form (GLUE, proved).** For an abelian surface `A/ℂ` with QM by `𝒪` whose
`(H₁(A, ℤ), ι_*, h_A)` is identified with `(𝒪, left multiplication, h_τ)` (the print's data `HodgeData`), there is
**exactly one** principal Riemann form of type `μ` on the genuine `H₁(A(ℂ), ℤ)` (`IsPrincipalRiemannMu`), and it is
`E₀ = trd(μ⁻¹ x ȳ)` under the identification. By Riemann's theorem (polarizations of `A` = Riemann forms on
`H₁(A, ℤ)`, Mumford, *Abelian varieties*, §§2–3, STANDARD, not in Mathlib) this is the print's polarization `ψ = E₀`
at `[h_τ, u]`, and it is unique: the forgetful map from the print's polarized moduli points to the leaf's
polarization-free ones is injective at every complex point with this `H₁` description. -/
theorem lemmaP_H1 {P : QML3 ℂ} {τ : UpperHalfPlane} {n : ℕ} {e : (Fin n → ℂ) → CPts P.A (RingHom.id ℂ)}
    {β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ)} {c : O → Path (1 : P.A.Pt ℂ) 1}
    (hD : HodgeData P τ n e β c) :
    (∃! E : H1 P.A → H1 P.A → ℤ, IsPrincipalRiemannMu β c E) ∧
      ∀ E, IsPrincipalRiemannMu β c E →
        ∀ b b' : O, (E (loopClass (c b)) (loopClass (c b')) : ℚ) = RvQMPolar.E0 b b' := by
  have hU := uniformizationLeafAll_proof
  refine ⟨?_, fun E hE => eq_E0_of_principalRiemann hU hD hE⟩
  obtain ⟨E, hE⟩ := exists_principalRiemann hU hD
  refine ⟨E, hE, fun E' hE' => ?_⟩
  funext x y
  obtain ⟨b, rfl⟩ := hD.2.2.1.2 x
  obtain ⟨b', rfl⟩ := hD.2.2.1.2 y
  have h1 := eq_E0_of_principalRiemann hU hD hE b b'
  have h2 := eq_E0_of_principalRiemann hU hD hE' b b'
  exact_mod_cast h2.trans h1.symm

/-- Lemma P for every complex point in the print's `H₁` form: the print data exist and carry exactly one principal
Riemann form of type `μ` (`E₀`). -/
theorem lemmaP_of_isHodgeH1Print {P : QML3 ℂ} {τ : UpperHalfPlane} (h : IsHodgeH1Print P τ) :
    ∃ n e β c, HodgeData P τ n e β c ∧ ∃! E : H1 P.A → H1 P.A → ℤ, IsPrincipalRiemannMu β c E := by
  obtain ⟨n, e, β, c, hD⟩ := h
  exact ⟨n, e, β, c, hD, (lemmaP_H1 hD).1⟩

end LemmaP

/-! ## 9. The converse: the old leaf gives the print-form leaf (so the new leaf is not stronger) -/

section Converse

open LeafQM.AV.R1UnivRigid ShimuraCFT RayClassCFT UpperHalfPlane

theorem mobPM_mul (g h : GL (Fin 2) ℝ) (z : HPM) : mobPM (g * h) z = mobPM g (mobPM h z) := by
  apply Subtype.ext
  show num (g * h) z.1 / denom (g * h) z.1 = num g (num h z.1 / denom h z.1) / denom g (num h z.1 / denom h z.1)
  have h1 : denom h z.1 ≠ 0 := denom_ne_zero_of_im h z.2
  set N := num h z.1 with hN
  set D := denom h z.1 with hD
  have hn : num (g * h) z.1 = (g 0 0 : ℂ) * N + (g 0 1 : ℂ) * D := by
    simp only [hN, hD, num, denom, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast; ring
  have hd : denom (g * h) z.1 = (g 1 0 : ℂ) * N + (g 1 1 : ℂ) * D := by
    simp only [hN, hD, num, denom, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast; ring
  have hn' : num g (N / D) = ((g 0 0 : ℂ) * N + (g 0 1 : ℂ) * D) / D := by
    simp only [num]; field_simp
  have hd' : denom g (N / D) = ((g 1 0 : ℂ) * N + (g 1 1 : ℂ) * D) / D := by
    simp only [denom]; field_simp
  rw [hn, hd, hn', hd', div_div_div_cancel_right₀ h1]

theorem mobPM_one (z : HPM) : mobPM 1 z = z := by
  apply Subtype.ext
  show num 1 z.1 / denom 1 z.1 = z.1
  simp [num, denom]

theorem iotaGL_mul (x y : LeafQM.B) (hx : ShimuraGlue.nrdQ ℚ x ≠ 0) (hy : ShimuraGlue.nrdQ ℚ y ≠ 0)
    (hxy : ShimuraGlue.nrdQ ℚ (x * y) ≠ 0) :
    RayClassCFT.iotaGL (x * y) hxy = RayClassCFT.iotaGL x hx * RayClassCFT.iotaGL y hy :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    rw [Matrix.GeneralLinearGroup.coe_mul, RayClassCFT.iotaGL_coe, RayClassCFT.iotaGL_coe,
      RayClassCFT.iotaGL_coe, RayClassCFT.iota_mul]

theorem nrd_mul_ne (x y : LeafQM.B) (hx : ShimuraGlue.nrdQ ℚ x ≠ 0) (hy : ShimuraGlue.nrdQ ℚ y ≠ 0) :
    ShimuraGlue.nrdQ ℚ (x * y) ≠ 0 := by
  rw [map_mul]; exact mul_ne_zero hx hy

/-- Moving the left point by `a` (with inverse `a'`, `ua = a` in `G(𝔸_f)`) does not change the relation. -/
theorem dcRelPM_left {a a' : LeafQM.B} (haa : a * a' = 1) (haa' : a' * a = 1)
    (ha : ShimuraGlue.nrdQ ℚ a ≠ 0) {ua : BAQˣ} (hua : (ua : BAQ) = bEmb a)
    (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ) :
    DCRelPM z g z' g' ↔ DCRelPM (mobPM (RayClassCFT.iotaGL a ha) z) (ua * g) z' g' := by
  have ha' : ShimuraGlue.nrdQ ℚ a' ≠ 0 := by
    intro h; have := congrArg (ShimuraGlue.nrdQ ℚ) haa; rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  constructor
  · rintro ⟨gm, hγ, hmob, k, hk, hg⟩
    have hn := nrd_mul_ne gm a' hγ ha'
    refine ⟨gm * a', hn, ?_, k, hk, ?_⟩
    · have hn2 := nrd_mul_ne (gm * a') a hn ha
      rw [← mobPM_mul, ← iotaGL_mul (gm * a') a hn ha hn2]
      have hga : gm * a' * a = gm := by rw [_root_.mul_assoc, haa', _root_.mul_one]
      rw [show RayClassCFT.iotaGL (gm * a' * a) hn2 = RayClassCFT.iotaGL gm hγ from
        Matrix.GeneralLinearGroup.ext fun i j => by rw [RayClassCFT.iotaGL_coe, RayClassCFT.iotaGL_coe, hga]]
      exact hmob
    · rw [hg, Units.val_mul, hua, map_mul]
      simp only [_root_.mul_assoc]
      rw [← _root_.mul_assoc (bEmb a') (bEmb a), ← map_mul, haa', map_one, _root_.one_mul]
  · rintro ⟨dl, hδ, hmob, k, hk, hg⟩
    have hn := nrd_mul_ne dl a hδ ha
    refine ⟨dl * a, hn, ?_, k, hk, ?_⟩
    · rw [iotaGL_mul dl a hδ ha hn, mobPM_mul, hmob]
    · rw [hg, Units.val_mul, hua, map_mul]
      simp only [_root_.mul_assoc]

theorem iotaGL_eq_one {x : LeafQM.B} (hx : ShimuraGlue.nrdQ ℚ x ≠ 0) (h1 : x = 1) :
    RayClassCFT.iotaGL x hx = 1 :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    rw [RayClassCFT.iotaGL_coe, h1]
    simp [BPAnalytic.QM.iota]

/-- Moving the right point by `a` does not change the relation. -/
theorem dcRelPM_right {a a' : LeafQM.B} (haa : a * a' = 1) (haa' : a' * a = 1)
    (ha : ShimuraGlue.nrdQ ℚ a ≠ 0) {ua : BAQˣ} (hua : (ua : BAQ) = bEmb a)
    (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ) :
    DCRelPM z g z' g' ↔ DCRelPM z g (mobPM (RayClassCFT.iotaGL a ha) z') (ua * g') := by
  have ha' : ShimuraGlue.nrdQ ℚ a' ≠ 0 := by
    intro h; have := congrArg (ShimuraGlue.nrdQ ℚ) haa; rw [map_mul, h, mul_zero, map_one] at this
    exact zero_ne_one this
  constructor
  · rintro ⟨gm, hγ, hmob, k, hk, hg⟩
    have hn := nrd_mul_ne a gm ha hγ
    refine ⟨a * gm, hn, ?_, k, hk, ?_⟩
    · rw [iotaGL_mul a gm ha hγ hn, mobPM_mul, hmob]
    · rw [Units.val_mul, hg, hua, map_mul]
      simp only [_root_.mul_assoc]
  · rintro ⟨dl, hδ, hmob, k, hk, hg⟩
    have hn := nrd_mul_ne a' dl ha' hδ
    refine ⟨a' * dl, hn, ?_, k, hk, ?_⟩
    · rw [iotaGL_mul a' dl ha' hδ hn, mobPM_mul, hmob, ← mobPM_mul, ← iotaGL_mul a' a ha' ha (nrd_mul_ne _ _ ha' ha),
        iotaGL_eq_one _ haa', mobPM_one]
    · have h2 : (g' : BAQ) = bEmb a' * ((ua : BAQ) * g') := by
        rw [hua, ← _root_.mul_assoc, ← map_mul, haa', map_one, _root_.one_mul]
      rw [h2, ← Units.val_mul, hg, map_mul]
      simp only [_root_.mul_assoc]

theorem nrd_mu_ne : ShimuraGlue.nrdQ ℚ RayClassCFT.mu ≠ 0 := by rw [RayClassCFT.nrd_mu]; norm_num

/-- `μ = 1 + i` as an element of `G(𝔸_f)`. -/
def uMu : BAQˣ := ⟨bEmb RayClassCFT.mu, bEmb RayClassCFT.muInv,
  by rw [← map_mul, RayClassCFT.mu_mul, map_one], by rw [← map_mul, RayClassCFT.mul_mu, map_one]⟩

theorem mob_mu_pos (z : HPM) (h : ¬ 0 < z.1.im) :
    0 < (mobPM (RayClassCFT.iotaGL RayClassCFT.mu nrd_mu_ne) z).1.im := by
  have hneg : z.1.im < 0 := lt_of_le_of_ne (not_lt.mp h) z.2
  simp only [mobPM]
  rw [im_num_div_denom, det_iotaGL, RayClassCFT.nrd_mu]
  have h3 := normSq_denom_pos (RayClassCFT.iotaGL RayClassCFT.mu nrd_mu_ne) z.2
  push_cast
  exact div_pos (by nlinarith) h3

/-- The retraction `ℍ^± × G(𝔸_f) → ℍ × G(𝔸_f)`: the identity on `ℍ`, `(z, g) ↦ (μz, μg)` on `ℍ⁻`. -/
def rPM (z : HPM) (g : BAQˣ) : UpperHalfPlane × BAQˣ :=
  if h : 0 < z.1.im then (⟨z.1, h⟩, g)
  else (⟨(mobPM (RayClassCFT.iotaGL RayClassCFT.mu nrd_mu_ne) z).1, mob_mu_pos z h⟩, uMu * g)

theorem rPM_toPM (τ : UpperHalfPlane) (g : BAQˣ) : rPM (toPM τ) g = (τ, g) := by
  unfold rPM toPM
  rw [dif_pos (show 0 < (τ : ℂ).im from τ.im_pos)]

theorem rel_rPM (z : HPM) (g : BAQˣ) (z' : HPM) (g' : BAQˣ) :
    DCRelPM z g z' g' ↔
      DCRelPM (toPM (rPM z g).1) (rPM z g).2 (toPM (rPM z' g').1) (rPM z' g').2 := by
  have hL := dcRelPM_left RayClassCFT.mu_mul RayClassCFT.mul_mu nrd_mu_ne (ua := uMu) rfl
  have hR := dcRelPM_right RayClassCFT.mu_mul RayClassCFT.mul_mu nrd_mu_ne (ua := uMu) rfl
  unfold rPM
  split_ifs with h h'
  · exact Iff.rfl
  · exact hR z g z' g'
  · exact hL z g z' g'
  · exact (hL z g z' g').trans (hR _ _ z' g')

/-- **The print-form leaf from the old leaf** (GLUE, proved): `Ψ±(z, g) = Ψ(r(z, g))` with the retraction `r`;
fibres by `rel_rPM` and `dcRelPM_iff`, moduli by `print_iff_hodge`. -/
theorem print_of_deligneH (h : Y3Fix.DeligneCanonicalModelY3EveryH) : DeligneCanonicalModelY3EveryPrint := by
  intro Y Φ hY
  obtain ⟨Ψ, ⟨h1, h2, h3, ⟨hm, hh⟩, h5⟩, hU⟩ := h Y Φ hY
  refine ⟨fun z g => Ψ (rPM z g).1 (rPM z g).2, ⟨fun y => ?_, fun z g z' g' => ?_, fun g => ?_,
    ⟨fun τ => ?_, ?_⟩, ?_⟩, fun u hu τ => ?_⟩
  · obtain ⟨τ, g, rfl⟩ := h1 y
    exact ⟨toPM τ, g, by simp only [rPM_toPM]⟩
  · rw [h2, ← dcRelPM_iff, ← rel_rPM]
  · simpa only [rPM_toPM] using h3 g
  · obtain ⟨P, hP, hH⟩ := hm τ
    exact ⟨P, by simpa only [rPM_toPM] using hP, (print_iff_hodge P τ).2 hH⟩
  · simpa only [rPM_toPM] using hh
  · obtain ⟨ε, δ, hr⟩ := h5
    refine ⟨ε, δ, fun K _ _ _ hK κ q z hz σ s hs g => ?_⟩
    simpa only [rPM_toPM] using hr K hK κ q z hz σ s hs g
  · obtain ⟨P, hP, hH⟩ := hU u hu τ
    exact ⟨P, by simpa only [rPM_toPM] using hP, (print_iff_hodge P τ).2 hH⟩

/-- **The print-form leaf is equivalent to the old leaf** (both directions proved): the restatement adds no
strength. -/
theorem print_iff_deligneH : DeligneCanonicalModelY3EveryPrint ↔ Y3Fix.DeligneCanonicalModelY3EveryH :=
  ⟨deligneH_of_print, print_of_deligneH⟩

/-- With y3-fix's `print_iff_field`: the two printed leaves together are equivalent to the research field. -/
theorem printPM_iff_field (hM : AvSplit.MumfordTorsionAlgClosed) :
    (Y3Fix.Y3FineModuliAbP ∧ DeligneCanonicalModelY3EveryPrint) ↔ ShimuraMainThmIDeligneY3AbU := by
  rw [print_iff_deligneH]; exact Y3Fix.print_iff_field hM

end Converse

end Y3Hodge
