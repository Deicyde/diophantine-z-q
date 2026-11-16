import ZInQKernel.Contrib.OneProof.UniformizationPrinted
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.TailC

set_option linter.all false
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

example (A : AbVar ℂ) : TopologicalSpace (A.Pt ℂ) := inferInstance

def H1 (A : AbVar ℂ) : Type := Abelianization (FundamentalGroup (A.Pt ℂ) 1)

instance (A : AbVar ℂ) : CommGroup (H1 A) := by unfold H1; infer_instance

def loopClass {A : AbVar ℂ} (lp : Path (1 : A.Pt ℂ) 1) : H1 A :=
  Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk lp))

def IsHodgeFibre (τ : UpperHalfPlane) (P : QML3 ℂ) : Prop :=
  ∃ e : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
    IsAnalyticHom (RingHom.id ℂ) e ∧ HDec.HSyn.G0Split.FibreQM.IotaCompatible P e ∧
    (∀ v ∈ QM.qmLattice τ.im_pos.ne', e v = 1) ∧
    ∃ lp : QM.qmLattice τ.im_pos.ne' → Path (1 : P.A.Pt ℂ) 1,
      (∀ v (t : unitInterval), lp v t = e (((t : ℝ) : ℂ) • (v : Fin 2 → ℂ))) ∧
      Function.Bijective (fun v => loopClass (lp v))

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

end PELHodge
