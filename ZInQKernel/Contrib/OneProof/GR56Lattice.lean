import ZInQKernel.Contrib.OneProof.QMLattice
import ZInQKernel.Contrib.OneProof.GRCountX6
import ZInQKernel.Contrib.HeightBC.G0StableBC
import ZInQKernel.Contrib.OneProof.RayClassShimura

/-!
# gr56-prove: González–Rotger Prop. 5.6 on `X₆` from Eichler's count and the lattice model

The research field `gonzalezRotgerProp56X6 : GRCountX6.GonzalezRotgerProp56X6` (González–Rotger 2006 Prop. 5.6
at `(D, N) = (6, 1)`: `#CM(R) = 2^{b(k)} h(R)` on every witness of `X₀(6,1)`) is proved from

* `GRCountX6.EichlerOptEmbCount6` (Eichler's count of `𝒪^×`-classes of optimal embeddings `R ↪ 𝒪`, pure
  quaternion-order algebra, defined by gt-grcount in `GRCountX6.lean`; the only new leaf), and
* fields already in the bundles: `shimuraMainThmIDeligneY3AbU` (research), `shimuraTaniyamaQbar` (added),
  `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed` (textbook):

`gonzalezRotgerProp56X6_of_main`. The content is the **CM-point correspondence**
`CM(R) ≃ Emb(R, 𝒪)/𝒪^×` (gt-grcount's `CMPointsOptEmb6`, proved here: `cmPointsOptEmb6_of_main`), through the
lattice model of QM abelian surfaces (gt-qm, `QMLattice.lean`):

* §1-§4: lattice data `LatData` of a QM surface over `ℂ` (uniformization with kernel `ι(𝒪)(τ, 1)ᵀ`), isomorphisms
  of QM pairs from scalars between normalized lattices (`qmIso_of_scalar`), base change along the fixed
  `σQ : ℚ̄ → ℂ` and descent of isomorphisms (T11(b), `qmIso_descend`), `End_𝒪(A)` acting by scalars;
* §5-§7: orders in quadratic fields, the optimal embedding `a ↦ b`, `ι(b)v = ψ(a)v`, of a CM point (`emb`,
  `emb_opt`), and the lattice argument: conjugate embeddings give proportional lattices (`iso_of_conj`);
* §8: the CM-point map `cmMap` is injective from the three textbook fields (`cmMap_injective`), and surjective
  from `QMTorusAbelian` (QM tori are abelian surfaces) and `CMPairDescendsQbar` (CM points are algebraic)
  (`cmMap_surjective`); `QMTorusAbelian` is the moduli clause of `shimuraMainThmIDeligneY3AbU`
  (`qmTorusAbelian_of_main`) and `CMPairDescendsQbar` follows from `shimuraTaniyamaQbar`
  (`cmPairDescendsQbar_of_st`); then `GRCountX6.r5fpCount_of_eichler` and `GRCountX6.prop56X6_of_r5fpCount`;
* §9-§10: the upper bound `R5fpCountLe` (the only half the chain uses) from Eichler's count and the textbook
  fields alone, and the chain's one consumer (`HDec.FS5NoCM.nocm_on_witness`, TailC) rerouted to it.

No `sorry`; standard axioms only.
-/

set_option linter.all false

noncomputable section

namespace GR56

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open HDec.QMSplit.CNO (act act_add act_mul act_one act_smul act_eq_zero act_sub act_zero act_neg
  mem_qmOrbit_iff)

/-! ## §1 Lattice data of a QM pair over `ℂ` -/

/-- The orbit lattice `ι(𝒪)v`. -/
abbrev L (v : Fin 2 → ℂ) : Submodule ℤ (Fin 2 → ℂ) := HDec.FibreQMNorm.qmOrbit v

/-- **Lattice data of a QM abelian surface over `ℂ`** (all fields come from T35, T11(a) and the chain's
`QMLatticeAlgebra`): a uniformization `Φ : ℂ² → A(ℂ)` with kernel `Λ`, the analytic representation `ρ`, and a
`ℂ`-linear change of coordinates `Fl` carrying `Λ` onto `ι(𝒪)(τ, 1)ᵀ` and `ρ(ι(a))` to `ι(a)`. -/
structure LatData (A : PkgI3.AbVar ℂ) (q : QMStr A) where
  Λ : Submodule ℤ (Fin 2 → ℂ)
  disc : DiscreteTopology Λ
  Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A (RingHom.id ℂ)
  hΦ : ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) Λ Φ
  ρ : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ)
  hρ : ∀ e z, Φ (ρ e z) = Φ z ≫ e.hom
  hρΛ : ∀ e, ∀ z ∈ Λ, ρ e z ∈ Λ
  Fl : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)
  τ : ℂ
  hτ : 0 < τ.im
  hΛ : ∀ z, z ∈ Λ ↔ Fl z ∈ L ![τ, 1]
  hFρ : ∀ (a : O) z, Fl (ρ (q.iota a) z) = act (a : B) (Fl z)

theorem exists_latData (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : PkgI3.AbVar ℂ) (hA : A.dim = 2) (q : QMStr A) : Nonempty (LatData A q) := by
  have hE : HDec.HSyn.G0Split.FibreQM.UniformizationExistsT35 := AvSplit.Final.h38 hU hM
  have hR : HDec.HSyn.G0Split.FibreQM.T11aRiemannEnd :=
    ZInQ.HomUnify.t11a_riemannEnd_of_corr (AvSplit.Final.h69 hU hG)
  have hL : HDec.HSyn.G0Split.FibreQM.QMLatticeAlgebra :=
    HDec.HSyn.G0Split.FibreQM.qmLatticeAlgebra_of_free
      (HDec.HSyn.G0Split.FibreQM.qmLatticeFree_of HDec.HSyn.G0Split.FibreQM.qmSkolemNoetherC_proof
        HDec.QMSplit.CNO.qmClassNumberOne_proof)
  obtain ⟨Λ, Φu, hd, hlat, hΦ⟩ := hE ℂ A (RingHom.id ℂ) 2 hA
  haveI := hd
  obtain ⟨ρ, hρ, hpres⟩ := HDec.HSyn.G0Split.FibreQM.unif_ring_hom hR A hA Λ Φu hΦ
  obtain ⟨τ, hτ, Fl, hF, hFρ⟩ := hL Λ hlat (ρ.comp q.iota) (fun a z hz => hpres (q.iota a) z hz)
  have hΛ : ∀ z, z ∈ Λ ↔ Fl z ∈ L ![τ, 1] := by
    intro z
    rw [L, ← HDec.FibreQMNorm.qmLattice_eq_orbit hτ.ne', ← hF]
    constructor
    · intro h; exact ⟨z, h, rfl⟩
    · rintro ⟨w, hw, he⟩
      have : w = z := Fl.injective he
      rw [← this]; exact hw
  exact ⟨⟨Λ, hd, Φu, hΦ, ρ, hρ, hpres, Fl, τ, hτ, hΛ, fun a z => hFρ a z⟩⟩

namespace LatData

variable {A : PkgI3.AbVar ℂ} {q : QMStr A} (D : LatData A q)

/-- The base vector `v = (τ, 1)ᵀ`. -/
abbrev v : Fin 2 → ℂ := ![D.τ, 1]

theorem v_ne : D.v ≠ 0 := fun h => by simpa using congrFun h 1

/-- The normalized analytic representation `ρ' = Fl ∘ ρ ∘ Fl⁻¹`. -/
def ρn : PkgI3.AbVar.End A →+* Module.End ℂ (Fin 2 → ℂ) where
  toFun e := D.Fl.toLinearMap ∘ₗ D.ρ e ∘ₗ D.Fl.symm.toLinearMap
  map_one' := LinearMap.ext fun z => by simp
  map_mul' e e' := LinearMap.ext fun z => by simp [map_mul]
  map_zero' := LinearMap.ext fun z => by simp
  map_add' e e' := LinearMap.ext fun z => by simp [map_add]

theorem ρn_apply (e : PkgI3.AbVar.End A) (z : Fin 2 → ℂ) : D.ρn e z = D.Fl (D.ρ e (D.Fl.symm z)) := rfl

theorem ρn_iota (a : O) (z : Fin 2 → ℂ) : D.ρn (q.iota a) z = act (a : B) z := by
  rw [ρn_apply, D.hFρ, LinearEquiv.apply_symm_apply]

theorem hT11 (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) :
    ∀ M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ), (∀ z ∈ D.Λ, M z ∈ D.Λ) →
      ∃! f : PkgI3.AbVar.End A, ∀ z, D.Φ (M z) = D.Φ z ≫ f.hom :=
  fun M hM => hC.2 A A 2 2 D.Λ D.Λ D.Φ D.Φ hA hA D.hΦ D.hΦ M hM

theorem ρ_injective (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) : Function.Injective D.ρ :=
  fun e e' h => (D.hT11 hC hA (D.ρ e) (D.hρΛ e)).unique (D.hρ e) (fun z => by rw [h]; exact D.hρ e' z)

theorem ρn_injective (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) : Function.Injective D.ρn := by
  intro e e' h
  apply D.ρ_injective hC hA
  refine LinearMap.ext fun w => ?_
  have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => D.Fl.symm (T (D.Fl w))) h
  simpa [ρn_apply] using this

theorem ρn_range (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) (N : Module.End ℂ (Fin 2 → ℂ)) :
    (∀ z ∈ L D.v, N z ∈ L D.v) ↔ ∃ e, D.ρn e = N := by
  haveI := D.disc
  constructor
  · intro hN
    have hN' : ∀ z ∈ D.Λ, (D.Fl.symm.toLinearMap ∘ₗ N ∘ₗ D.Fl.toLinearMap) z ∈ D.Λ := by
      intro z hz
      rw [D.hΛ]
      simpa using hN _ ((D.hΛ z).1 hz)
    obtain ⟨f, hf, -⟩ := D.hT11 hC hA _ hN'
    have hfe : D.ρ f = D.Fl.symm.toLinearMap ∘ₗ N ∘ₗ D.Fl.toLinearMap :=
      HDec.HSyn.G0Split.FibreQM.lift_unique D.hΦ (fun z => by rw [D.hρ, hf])
    refine ⟨f, LinearMap.ext fun z => ?_⟩
    rw [ρn_apply, hfe]
    simp
  · rintro ⟨e, rfl⟩ z hz
    rw [ρn_apply, ← D.hΛ]
    apply D.hρΛ
    rw [D.hΛ]
    simpa using hz

end LatData

/-! ## §2 Isomorphisms of QM pairs over `ℂ` from scalars between the normalized lattices -/

theorem realize (hC : ZInQ.HomUnify.HomLatticeCorr) {A A' : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    (hA' : A'.dim = 2) {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) (hM : ∀ z ∈ D.Λ, M z ∈ D'.Λ) :
    ∃! f : PkgI3.AbVar.Hom A A', ∀ z, D'.Φ (M z) = D.Φ z ≫ f.hom :=
  hC.2 A A' 2 2 D.Λ D'.Λ D.Φ D'.Φ hA hA' D.hΦ D'.hΦ M hM

/-- The scalar change of normalized coordinates as a map of raw coordinates. -/
def scalM {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (μ : ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  D'.Fl.symm.toLinearMap ∘ₗ (μ • LinearMap.id) ∘ₗ D.Fl.toLinearMap

theorem scalM_apply {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (D : LatData A q)
    (D' : LatData A' q') (μ : ℂ) (z : Fin 2 → ℂ) : scalM D D' μ z = D'.Fl.symm (μ • D.Fl z) := rfl

theorem scalM_mem {A A' : PkgI3.AbVar ℂ} {q : QMStr A} {q' : QMStr A'} (D : LatData A q)
    (D' : LatData A' q') (μ : ℂ) (h : ∀ w ∈ L D.v, μ • w ∈ L D'.v) : ∀ z ∈ D.Λ, scalM D D' μ z ∈ D'.Λ := by
  intro z hz
  rw [D'.hΛ, scalM_apply, LinearEquiv.apply_symm_apply]
  exact h _ ((D.hΛ z).1 hz)

/-- **An isomorphism of QM pairs over `ℂ` from a scalar `μ` with `μ·ι(𝒪)v = ι(𝒪)v'`.** -/
theorem qmIso_of_scalar (hC : ZInQ.HomUnify.HomLatticeCorr) {A A' : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    (hA' : A'.dim = 2) {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (μ : ℂ) (hμ : μ ≠ 0) (h1 : ∀ w ∈ L D.v, μ • w ∈ L D'.v) (h2 : ∀ w ∈ L D'.v, μ⁻¹ • w ∈ L D.v) :
    Nonempty (QMIso q q') := by
  obtain ⟨f, hf, hfu⟩ := realize hC hA hA' D D' (scalM D D' μ) (scalM_mem D D' μ h1)
  obtain ⟨g, hg, -⟩ := realize hC hA' hA D' D (scalM D' D μ⁻¹) (scalM_mem D' D μ⁻¹ h2)
  have hgf : ∀ z, scalM D' D μ⁻¹ (scalM D D' μ z) = z := fun z => by
    simp [scalM_apply, smul_smul, mul_inv_cancel₀ hμ]
  have hfg : ∀ z, scalM D D' μ (scalM D' D μ⁻¹ z) = z := fun z => by
    simp [scalM_apply, smul_smul, inv_mul_cancel₀ hμ]
  have left : f.hom ≫ g.hom = 𝟙 _ := by
    obtain ⟨e, -, he⟩ := D.hT11 hC hA LinearMap.id (fun z hz => hz)
    have e1 := he (PkgI3.AbVar.Hom.mk' (f.hom ≫ g.hom)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hf, ← hg, hgf]; rfl)
    have e2 := he (PkgI3.AbVar.Hom.mk' (𝟙 _)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', Category.comp_id]; rfl)
    exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)
  have right : g.hom ≫ f.hom = 𝟙 _ := by
    obtain ⟨e, -, he⟩ := D'.hT11 hC hA' LinearMap.id (fun z hz => hz)
    have e1 := he (PkgI3.AbVar.Hom.mk' (g.hom ≫ f.hom)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hg, ← hf, hfg]; rfl)
    have e2 := he (PkgI3.AbVar.Hom.mk' (𝟙 _)) (fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', Category.comp_id]; rfl)
    exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)
  refine ⟨⟨f, g, left, right, fun a => ?_⟩⟩
  -- both sides realize `scalM ∘ ρ(ι a) = ρ'(ι a) ∘ scalM`
  have hcomm : ∀ z, scalM D D' μ (D.ρ (q.iota a) z) = D'.ρ (q'.iota a) (scalM D D' μ z) := by
    intro z
    apply D'.Fl.injective
    rw [D'.hFρ, scalM_apply, scalM_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      D.hFρ]
    simp [act, Matrix.mulVec_smul]
  let N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := scalM D D' μ ∘ₗ D.ρ (q.iota a)
  have hN : ∀ z ∈ D.Λ, N z ∈ D'.Λ := fun z hz =>
    scalM_mem D D' μ h1 _ (D.hρΛ _ z hz)
  obtain ⟨e, -, he⟩ := realize hC hA hA' D D' N hN
  have e1 := he (PkgI3.AbVar.Hom.mk' ((q.iota a).hom ≫ f.hom)) (fun z => by
    rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← D.hρ, ← hf]; rfl)
  have e2 := he (PkgI3.AbVar.Hom.mk' (f.hom ≫ (q'.iota a).hom)) (fun z => by
    rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hf, ← D'.hρ]
    show D'.Φ (scalM D D' μ (D.ρ (q.iota a) z)) = _
    rw [hcomm])
  exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)

/-! ## §3 Base change `ℚ̄ → ℂ` and descent of isomorphisms (T11(b), proved in the chain) -/

/-- The fixed embedding `ℚ̄ → ℂ` (the one of `CMStab.lat_model` and `QMLattice.yuB6Alg_of`). -/
def σQ : Qbar →+* ℂ := (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom

/-- `ℂ` as a `ℚ̄`-algebra through `σQ` (local instance of this file). -/
abbrev algQC : Algebra Qbar ℂ := σQ.toAlgebra

attribute [local instance] algQC

/-- The base change of a QM pair along `σQ`, with `ι_ℂ = endBC ∘ ι`. -/
def bcQ (P : QMPair Qbar) : QMPair ℂ where
  A := P.A.baseChange ℂ
  surface := by rw [PkgI3.AbVar.dim_baseChange]; exact P.surface
  q := ⟨(HDec.G0ModField.KernelField.endBC P.A ℂ).comp P.q.iota,
    (HDec.G0ModField.KernelField.endBC_injective P.A ℂ).comp P.q.injective⟩

theorem bcQ_iota_hom (P : QMPair Qbar) (a : O) :
    ((bcQ P).q.iota a).hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map (P.q.iota a).hom := rfl

theorem t11b : ZInQ.LeafPush2.T11b_Rigidity := HDec.AVB2.t11b_of_exists HDec.HSyn.t11bExists_lf8

theorem pb_map_inj {A A' : PkgI3.AbVar Qbar} {a b : A.X ⟶ A'.X}
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map a =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map b) : a = b :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map_injective h

/-- **Isomorphisms of base changes descend** (T11(b): every homomorphism `A_ℂ → B_ℂ` descends). -/
theorem qmIso_descend (P Q : QMPair Qbar) (f : QMIso (bcQ P).q (bcQ Q).q) : Nonempty (QMIso P.q Q.q) := by
  obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := t11b Qbar ℂ P.A Q.A f.φ.hom (Additive.toMul f.φ).2
  obtain ⟨ψ, ⟨hψ, hψe⟩, -⟩ := t11b Qbar ℂ Q.A P.A f.ψ.hom (Additive.toMul f.ψ).2
  refine ⟨⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.mk' ψ, ?_, ?_, fun a => ?_⟩⟩
  · apply pb_map_inj
    rw [PkgI3.AbVar.Hom.hom_mk', PkgI3.AbVar.Hom.hom_mk', CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_id, hφe, hψe]
    exact f.left
  · apply pb_map_inj
    rw [PkgI3.AbVar.Hom.hom_mk', PkgI3.AbVar.Hom.hom_mk', CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_id, hφe, hψe]
    exact f.right
  · apply pb_map_inj
    rw [PkgI3.AbVar.Hom.hom_mk', CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hφe,
      ← bcQ_iota_hom,
      ← bcQ_iota_hom]
    exact f.equivariant a

theorem endBC_bijective (A : PkgI3.AbVar Qbar) :
    Function.Bijective (HDec.G0ModField.KernelField.endBC A ℂ) := by
  refine ⟨HDec.G0ModField.KernelField.endBC_injective A ℂ, fun g => ?_⟩
  obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := t11b Qbar ℂ A A g.hom (Additive.toMul g).2
  exact ⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.ext' hφe⟩

/-- **`End_𝒪` is unchanged by base change to `ℂ`.** -/
theorem com_bcQ (P : QMPair Qbar) : Nonempty (com P.q ≃+* com (bcQ P).q) := by
  let e := HDec.G0ModField.KernelField.endBC P.A ℂ
  have he := endBC_bijective P.A
  have hmem : ∀ x, x ∈ com P.q ↔ e x ∈ com (bcQ P).q := by
    intro x
    simp only [com, Subring.mem_centralizer_iff]
    constructor
    · rintro hx _ ⟨a, rfl⟩
      change e (P.q.iota a) * e x = e x * e (P.q.iota a)
      rw [← map_mul, ← map_mul, hx _ ⟨a, rfl⟩]
    · rintro hx _ ⟨a, rfl⟩
      apply he.1
      rw [map_mul, map_mul]
      exact hx _ ⟨a, rfl⟩
  let F : com P.q →+* com (bcQ P).q :=
    (e.comp (com P.q).subtype).codRestrict _ (fun x => (hmem x).1 x.2)
  refine ⟨RingEquiv.ofBijective F ⟨fun x y h => Subtype.ext (he.1 (congrArg Subtype.val h)), ?_⟩⟩
  rintro ⟨g, hg⟩
  obtain ⟨x, rfl⟩ := he.2 g
  exact ⟨⟨x, (hmem x).2 hg⟩, rfl⟩

/-! ## §4 `End_𝒪(A)` acts by scalars (gt-qm's `com_embed`, with the data fixed) -/

namespace LatData

variable {A : PkgI3.AbVar ℂ} {q : QMStr A} (D : LatData A q)

theorem ρn_comm (e : com q) (x : B) (hx : x ∈ O) (z : Fin 2 → ℂ) :
    D.ρn e (act x z) = act x (D.ρn e z) := by
  have hcm : q.iota ⟨x, hx⟩ * e = e * q.iota ⟨x, hx⟩ := by
    exact (Subring.mem_centralizer_iff.mp e.2) _ ⟨⟨x, hx⟩, rfl⟩
  have h1 : act x z = D.ρn (q.iota ⟨x, hx⟩) z := (D.ρn_iota ⟨x, hx⟩ z).symm
  have h2 : act x (D.ρn e z) = D.ρn (q.iota ⟨x, hx⟩) (D.ρn e z) := (D.ρn_iota ⟨x, hx⟩ _).symm
  rw [h1, h2, ← Module.End.mul_apply, ← map_mul, ← hcm, map_mul, Module.End.mul_apply]

/-- The scalar by which `e ∈ End_𝒪(A)` acts. -/
def scal (e : com q) : ℂ := D.ρn e D.v 1

theorem scal_spec (e : com q) (w : Fin 2 → ℂ) : D.ρn e w = D.scal e • w := by
  obtain ⟨c0, h0⟩ := HDec.QMLattice.commutant (D.ρn e) (fun x hx z => D.ρn_comm e x hx z)
  have : D.scal e = c0 := by
    show D.ρn e ![D.τ, 1] 1 = c0
    rw [h0]; simp
  rw [this, h0]

theorem smul_v_inj {a b : ℂ} (h : a • D.v = b • D.v) : a = b := smul_left_injective ℂ D.v_ne h

/-- `scal` as a ring homomorphism. -/
def scalHom : com q →+* ℂ where
  toFun := D.scal
  map_one' := D.smul_v_inj (by rw [← D.scal_spec, OneMemClass.coe_one, map_one, one_smul]; rfl)
  map_mul' e e' := D.smul_v_inj (by
    rw [← D.scal_spec, MulMemClass.coe_mul, map_mul, Module.End.mul_apply, D.scal_spec e',
      map_smul, D.scal_spec e, smul_smul, mul_comm])
  map_zero' := D.smul_v_inj (by rw [← D.scal_spec, ZeroMemClass.coe_zero, map_zero, zero_smul]; rfl)
  map_add' e e' := D.smul_v_inj (by
    rw [← D.scal_spec, AddMemClass.coe_add, map_add, LinearMap.add_apply, D.scal_spec e,
      D.scal_spec e', add_smul])

theorem scalHom_apply (e : com q) : D.scalHom e = D.scal e := rfl

theorem v_mem : D.v ∈ L D.v := by
  rw [mem_qmOrbit_iff]; exact ⟨1, LeafQM.O.one_mem, (act_one _).symm⟩

theorem exists_O (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) (e : com q) :
    ∃ x ∈ O, act x D.v = D.scal e • D.v := by
  have h2 := (D.ρn_range hC hA (D.ρn e)).2 ⟨e, rfl⟩ _ D.v_mem
  rw [D.scal_spec, mem_qmOrbit_iff] at h2
  obtain ⟨x, hx, hxe⟩ := h2
  exact ⟨x, hx, hxe.symm⟩

theorem exists_com (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) {x : B} (hxO : x ∈ O) {c0 : ℂ}
    (hc0 : act x D.v = c0 • D.v) : ∃ e : com q, D.scal e = c0 := by
  let N : Module.End ℂ (Fin 2 → ℂ) := c0 • LinearMap.id
  have hN : ∀ z ∈ L D.v, N z ∈ L D.v := by
    intro z hz
    rw [mem_qmOrbit_iff] at hz ⊢
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨y * x, LeafQM.O.mul_mem hy hxO, ?_⟩
    show c0 • act y D.v = _
    rw [act_mul, hc0, HDec.QMLattice.act_smul_vec]
  obtain ⟨e0, he0⟩ := (D.ρn_range hC hA N).1 hN
  have he0com : e0 ∈ com q := by
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    apply D.ρn_injective hC hA
    rw [map_mul, map_mul, he0]
    refine LinearMap.ext fun w => ?_
    simp [N]
  refine ⟨⟨e0, he0com⟩, D.smul_v_inj ?_⟩
  rw [← D.scal_spec]
  show D.ρn e0 D.v = _
  rw [he0]; rfl

theorem scal_injective (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) :
    Function.Injective D.scal := by
  intro e e' h
  apply Subtype.ext
  apply D.ρn_injective hC hA
  refine LinearMap.ext fun w => ?_
  rw [D.scal_spec, D.scal_spec, h]

end LatData

/-! ## §5 Orders in an imaginary quadratic field -/

section NT

variable {k : Type} [Field k] [NumberField k]

/-- An integral element of a quadratic field satisfies `r² − t r + n = 0` with `t, n ∈ ℤ`. -/
theorem quad_rel (hk : Module.finrank ℚ k = 2) (r : k) (hr : IsIntegral ℤ r) :
    ∃ t n : ℤ, r * r - (t : k) * r + (n : k) = 0 := by
  have hm := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hr
  have hdeg : (minpoly ℚ r).natDegree ≤ 2 := hk ▸ minpoly.natDegree_le r
  have hmon : (minpoly ℤ r).Monic := minpoly.monic hr
  have hpd : (minpoly ℤ r).natDegree ≤ 2 := by
    rw [hm, Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at hdeg
    exact hdeg
  have hpos : 0 < (minpoly ℤ r).natDegree := minpoly.natDegree_pos hr
  have hev : Polynomial.aeval r (minpoly ℤ r) = 0 := minpoly.aeval ℤ r
  have hlc : (minpoly ℤ r).coeff (minpoly ℤ r).natDegree = 1 := hmon.coeff_natDegree
  rw [Polynomial.aeval_eq_sum_range] at hev
  generalize (minpoly ℤ r) = p at *
  interval_cases h : p.natDegree
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hev
    rw [hlc, one_smul, zsmul_eq_mul, mul_one] at hev
    refine ⟨-2 * p.coeff 0, p.coeff 0 * p.coeff 0, ?_⟩
    have : r = -(p.coeff 0 : k) := by linear_combination hev
    rw [this]; push_cast; ring
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hev
    rw [hlc, one_smul, zsmul_eq_mul, zsmul_eq_mul, mul_one] at hev
    refine ⟨-p.coeff 1, p.coeff 0, ?_⟩
    push_cast
    linear_combination hev

theorem roots_cases {x y t n : ℂ} (h1 : x * x - t * x + n = 0) (h2 : y * y - t * y + n = 0) :
    x = y ∨ x = t - y := by
  have : (x - y) * (x - (t - y)) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.1 this with h | h
  · left; linear_combination h
  · right; linear_combination h

/-- **Two embeddings of an order in `ℂ` have the same image.** -/
theorem image_cross (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hR : R ≤ (integralClosure ℤ k).toSubring) (ψ : k →+* ℂ) (χ : R →+* ℂ) (r : R) :
    (∃ s : R, χ s = ψ r) ∧ (∃ s : R, ψ s = χ r) := by
  have hr : IsIntegral ℤ (r : k) := hR r.2
  obtain ⟨t, n, htn⟩ := quad_rel hk _ hr
  have hrel : r * r - (t : R) * r + (n : R) = 0 := Subtype.ext (by push_cast; exact htn)
  have hχ : χ r * χ r - (t : ℂ) * χ r + (n : ℂ) = 0 := by
    have := congrArg χ hrel
    simpa using this
  have hψ : ψ r * ψ r - (t : ℂ) * ψ r + (n : ℂ) = 0 := by
    have := congrArg ψ htn
    simpa using this
  refine ⟨?_, ?_⟩
  · rcases roots_cases hψ hχ with h | h
    · exact ⟨r, h.symm⟩
    · exact ⟨(t : R) - r, by rw [map_sub, map_intCast, h]⟩
  · rcases roots_cases hχ hψ with h | h
    · exact ⟨r, h.symm⟩
    · exact ⟨(t : R) - r, by
        rw [h]; push_cast; rw [map_sub, map_intCast]⟩

/-- Every element of `k` has a positive integer multiple in an order of finite index. -/
theorem exists_nat_mul_mem (R : Subring k) (hc : Nat.Coprime (conductor R) 6) (a : k) :
    ∃ n : ℕ, 0 < n ∧ (n : k) * a ∈ R := by
  have hc0 : conductor R ≠ 0 := by
    intro h0; rw [h0] at hc; norm_num at hc
  have hx : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ k |>.mpr (.of_finite ℚ a)
  obtain ⟨m, s, hm, hms⟩ := hx.exists_nsmul_eq (integralClosure ℤ k)
  have hmem : m • a ∈ (integralClosure ℤ k).toSubring.toAddSubgroup := by
    rw [hms]; exact s.2
  have h2 := R.toAddSubgroup.nsmul_relIndex_mem hmem
  refine ⟨conductor R * m, Nat.mul_pos (Nat.pos_of_ne_zero hc0) (Nat.pos_of_ne_zero hm), ?_⟩
  have : (((conductor R * m : ℕ)) : k) * a = conductor R • (m • a) := by
    rw [smul_smul, nsmul_eq_mul]
  rw [this]
  exact h2

/-- An element of `k` outside `ℚ`. -/
theorem exists_not_rat (hk : Module.finrank ℚ k = 2) : ∃ a : k, ∀ r : ℚ, a ≠ algebraMap ℚ k r := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (Algebra.linearMap ℚ k) := fun a => by
    obtain ⟨r, hr⟩ := h a; exact ⟨r, hr.symm⟩
  let e := LinearEquiv.ofBijective (Algebra.linearMap ℚ k) ⟨(algebraMap ℚ k).injective, hs⟩
  have := e.finrank_eq
  rw [Module.finrank_self, hk] at this
  norm_num at this

end NT

/-! ## §6 The optimal embedding of a CM point -/

section Emb

variable {k : Type} [Field k] [NumberField k] {A : PkgI3.AbVar ℂ} {q : QMStr A} (D : LatData A q)
  (hC : ZInQ.HomUnify.HomLatticeCorr) (hA : A.dim = 2) (R : Subring k)
  (hc : Nat.Coprime (conductor R) 6) (ψ : k →+* ℂ)
  (hψ : ∀ r : R, ∃ e : com q, D.scal e = ψ r)

include hC hA hc hψ in
theorem exists_B (a : k) : ∃ b : B, act b D.v = ψ a • D.v := by
  obtain ⟨n, hn, hna⟩ := exists_nat_mul_mem R hc a
  obtain ⟨e, he⟩ := hψ ⟨_, hna⟩
  obtain ⟨x, -, hxe⟩ := D.exists_O hC hA e
  refine ⟨((n : ℚ)⁻¹) • x, ?_⟩
  rw [act_smul, hxe, he, smul_smul]
  congr 1
  simp only [map_mul, map_natCast]
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

/-- The embedding `k → B`: `a ↦` the unique `b` with `ι(b)v = ψ(a)v`. -/
def embF (a : k) : B := Classical.choose (exists_B D hC hA R hc ψ hψ a)

theorem embF_spec (a : k) : act (embF D hC hA R hc ψ hψ a) D.v = ψ a • D.v :=
  Classical.choose_spec (exists_B D hC hA R hc ψ hψ a)

/-- The embedding as a `ℚ`-algebra map. -/
def emb : k →ₐ[ℚ] B where
  toFun := embF D hC hA R hc ψ hψ
  map_one' := HDec.QMLattice.act_inj D.v_ne (by rw [embF_spec, act_one, map_one, one_smul])
  map_mul' a b := HDec.QMLattice.act_inj D.v_ne (by
    rw [embF_spec, act_mul, embF_spec, HDec.QMLattice.act_smul_vec, embF_spec, smul_smul, map_mul,
      mul_comm])
  map_zero' := HDec.QMLattice.act_inj D.v_ne (by rw [embF_spec, act_zero, map_zero, zero_smul])
  map_add' a b := HDec.QMLattice.act_inj D.v_ne (by
    rw [embF_spec, act_add, embF_spec, embF_spec, map_add, add_smul])
  commutes' r := HDec.QMLattice.act_inj D.v_ne (by
    rw [embF_spec, HDec.QMLattice.act_algebraMap, eq_ratCast (algebraMap ℚ k) r, map_ratCast])

theorem emb_spec (a : k) : act (emb D hC hA R hc ψ hψ a) D.v = ψ a • D.v := embF_spec D hC hA R hc ψ hψ a

include hψ in
theorem emb_opt (hψ' : ∀ e : com q, ∃ r : R, ψ r = D.scal e) :
    LeafQM.O.comap (emb D hC hA R hc ψ hψ).toRingHom = R := by
  ext a
  rw [Subring.mem_comap]
  constructor
  · intro ha
    obtain ⟨e, he⟩ := D.exists_com hC hA ha (emb_spec D hC hA R hc ψ hψ a)
    obtain ⟨r, hr⟩ := hψ' e
    have : (r : k) = a := ψ.injective (hr.trans he)
    rw [← this]; exact r.2
  · intro ha
    obtain ⟨e, he⟩ := hψ ⟨a, ha⟩
    obtain ⟨x, hx, hxe⟩ := D.exists_O hC hA e
    have : x = emb D hC hA R hc ψ hψ a :=
      HDec.QMLattice.act_inj D.v_ne (by rw [hxe, emb_spec, he])
    show emb D hC hA R hc ψ hψ a ∈ LeafQM.O
    rw [← this]; exact hx

end Emb

/-! ## §7 Conjugate optimal embeddings give isomorphic QM pairs -/

/-- An element of `B = (2, −3)` commuting with everything is rational. -/
theorem central_of_comm {b : B} (h : ∀ x : B, b * x = x * b) : b ∈ Set.range (algebraMap ℚ B) := by
  have hi := h ⟨0, 1, 0, 0⟩
  have hj := h ⟨0, 0, 1, 0⟩
  have e1 := congrArg QuaternionAlgebra.imJ hi
  have e2 := congrArg QuaternionAlgebra.imK hi
  have e3 := congrArg QuaternionAlgebra.imK hj
  have e4 := congrArg QuaternionAlgebra.imI hj
  simp at e1 e2 e3 e4
  refine ⟨b.re, ?_⟩
  rw [QuaternionAlgebra.algebraMap_eq]
  ext <;> simp <;> linarith

/-- A non-central `b ∈ B` has one-dimensional eigenlines on `(τ, 1)ᵀ`: a second eigenvector for the same
eigenvalue is proportional to it (otherwise `ι(b)` is scalar and `b` central). -/
theorem eig_line {b : B} (hb : b ∉ Set.range (algebraMap ℚ B)) {τ c : ℂ} {w : Fin 2 → ℂ}
    (hw : act b w = c • w) (hv : act b ![τ, 1] = c • ![τ, 1]) : w = w 1 • ![τ, 1] := by
  by_contra hne
  have hd : w 0 - τ * w 1 ≠ 0 := by
    intro h0; apply hne; ext i; fin_cases i <;> simp <;> linear_combination h0
  have hall : ∀ z, act b z = c • z := by
    intro z
    have hz : z = (z 1 - (z 0 - τ * z 1) / (w 0 - τ * w 1) * w 1) • ![τ, 1] +
        ((z 0 - τ * z 1) / (w 0 - τ * w 1)) • w := by
      ext i; fin_cases i <;> simp <;> field_simp <;> ring
    rw [hz, HDec.QMLattice.act_add_vec, HDec.QMLattice.act_smul_vec, HDec.QMLattice.act_smul_vec, hv, hw]
    simp only [smul_add, smul_smul, mul_comm]
  apply hb
  apply central_of_comm
  intro x
  have hv0 : (![τ, 1] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 1
  apply HDec.QMLattice.act_inj hv0
  rw [act_mul, act_mul, hall, hv, HDec.QMLattice.act_smul_vec]

/-- **The lattice argument.** If `ι(b₁)v = c·v`, `ι(b₂)v' = c·v'`, `b₂ = u b₁ u⁻¹` with `u ∈ 𝒪^×` and `b₂ ∉ ℚ`,
then `ι(u)v = μ v'` and `μ⁻¹ ι(𝒪)v = ι(𝒪)v'`, so the pairs are isomorphic. -/
theorem iso_of_conj (hC : ZInQ.HomUnify.HomLatticeCorr) {A A' : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    (hA' : A'.dim = 2) {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (b1 b2 : B) (hb : b2 ∉ Set.range (algebraMap ℚ B)) (c : ℂ) (h1 : act b1 D.v = c • D.v)
    (h2 : act b2 D'.v = c • D'.v) (u : (↥LeafQM.O)ˣ)
    (hu : b2 = ((u : LeafQM.O) : B) * b1 * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B)) :
    Nonempty (QMIso q q') := by
  set U : B := ((u : LeafQM.O) : B) with hUdef
  set Ui : B := (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) with hUidef
  have hUiU : Ui * U = 1 := GRCountX6.unit_inv_mul u
  set w := act U D.v with hwdef
  have hw : act b2 w = c • w := by
    rw [hu, act_mul, act_mul, hwdef, ← act_mul Ui U, hUiU, act_one, h1, HDec.QMLattice.act_smul_vec]
  have hline : w = w 1 • D'.v := eig_line hb hw h2
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℂ, μ = w 1 := ⟨_, rfl⟩
  rw [← hμdef] at hline
  have hw0 : w ≠ 0 := by
    intro h0
    apply D.v_ne
    have : act Ui w = D.v := by rw [hwdef, ← act_mul, hUiU, act_one]
    rw [← this, h0]
    simp [act]
  have hμ : μ ≠ 0 := by intro h0; apply hw0; rw [hline, h0, zero_smul]
  have hv' : D'.v = μ⁻¹ • w := by
    rw [hline, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hUiw : act Ui w = D.v := by rw [hwdef, ← act_mul, hUiU, act_one]
  refine qmIso_of_scalar hC hA hA' D D' μ⁻¹ (inv_ne_zero hμ) ?_ ?_
  · intro z hz
    rw [mem_qmOrbit_iff] at hz ⊢
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨x * Ui, LeafQM.O.mul_mem hx (u⁻¹ : (↥LeafQM.O)ˣ).1.2, ?_⟩
    rw [act_mul, hv', HDec.QMLattice.act_smul_vec, hUiw, HDec.QMLattice.act_smul_vec]
  · intro z hz
    rw [mem_qmOrbit_iff] at hz ⊢
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨y * U, LeafQM.O.mul_mem hy u.1.2, ?_⟩
    rw [inv_inv, ← HDec.QMLattice.act_smul_vec, ← hline, hwdef, act_mul]

/-! ## §8 The injection of CM points into optimal embeddings, and the bound -/

/-- The CM points by `R` on `X₆`, read through the moduli interpretation: isomorphism classes of QM pairs over
`ℚ̄` with `End_𝒪(A) ≅ R` (the set counted by `LeafQM.AV.R5fpCount`). -/
abbrev CMSet {k : Type} [Field k] (R : Subring k) :=
  {c : Quotient (pairSetoid Qbar) // ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)}

/-! ## §8b Comparison of two lattice models along an isomorphism -/

/-- **Two lattice models of isomorphic QM pairs differ by a unit of `𝒪`**: if `g : (A, ι) ≅ (A', ι')` and
`Φ₁, Φ₂` are embeddings with `ι(Φ₁ a)v = ψ(a)v` and `ι(Φ₂ a)v' = ψ(a)v'`, then `Φ₂ = u Φ₁ u⁻¹` with `u ∈ 𝒪^×`.
(The lift of `g` to `ℂ²` commutes with `ι(𝒪)`, so it is a scalar `s` with `s·ι(𝒪)v = ι(𝒪)v'`.) -/
theorem conj_of_iso (hC : ZInQ.HomUnify.HomLatticeCorr) {A A' : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    (hA' : A'.dim = 2) {q : QMStr A} {q' : QMStr A'} (D : LatData A q) (D' : LatData A' q')
    (g : QMIso q q') {k : Type} [Field k] [NumberField k] {R : Subring k} (ψ : k →+* ℂ)
    (Φ₁ Φ₂ : GRCountX6.OptEmb k R) (h₁ : ∀ a, act (Φ₁.1 a) D.v = ψ a • D.v)
    (h₂ : ∀ a, act (Φ₂.1 a) D'.v = ψ a • D'.v) : GRCountX6.ConjRel R Φ₁ Φ₂ := by
  haveI := D.disc
  haveI := D'.disc
  obtain ⟨M, hM⟩ := hC.1 ℂ A A' (RingHom.id ℂ) 2 2 D.Λ D'.Λ D.Φ D'.Φ hA hA' D.hΦ D'.hΦ g.φ
  obtain ⟨M', hM'⟩ := hC.1 ℂ A' A (RingHom.id ℂ) 2 2 D'.Λ D.Λ D'.Φ D.Φ hA' hA D'.hΦ D.hΦ g.ψ
  -- normalized lifts
  let N : Module.End ℂ (Fin 2 → ℂ) := D'.Fl.toLinearMap ∘ₗ M ∘ₗ D.Fl.symm.toLinearMap
  let N' : Module.End ℂ (Fin 2 → ℂ) := D.Fl.toLinearMap ∘ₗ M' ∘ₗ D'.Fl.symm.toLinearMap
  have hNapp : ∀ z, N z = D'.Fl (M (D.Fl.symm z)) := fun z => rfl
  have hN'app : ∀ z, N' z = D.Fl (M' (D'.Fl.symm z)) := fun z => rfl
  -- `M` intertwines `ρ(ι a)`
  have hMι : ∀ (a : O) z, M (D.ρ (q.iota a) z) = D'.ρ (q'.iota a) (M z) := by
    intro a z
    have := HDec.HSyn.G0Split.FibreQM.lift_unique D'.hΦ
      (M := M ∘ₗ D.ρ (q.iota a)) (M' := D'.ρ (q'.iota a) ∘ₗ M) (fun z => by
        simp only [LinearMap.comp_apply]
        rw [hM, D.hρ, D'.hρ, hM, Category.assoc, Category.assoc, g.equivariant a])
    exact congrArg (fun T => T z) this
  have hM'ι : ∀ (a : O) z, M' (D'.ρ (q'.iota a) z) = D.ρ (q.iota a) (M' z) := by
    intro a z
    have := HDec.HSyn.G0Split.FibreQM.lift_unique D.hΦ
      (M := M' ∘ₗ D'.ρ (q'.iota a)) (M' := D.ρ (q.iota a) ∘ₗ M') (fun z => by
        simp only [LinearMap.comp_apply]
        rw [hM', D'.hρ, D.hρ, hM', Category.assoc, Category.assoc]
        exact congrArg (D'.Φ z ≫ ·) (g.symm.equivariant a))
    exact congrArg (fun T => T z) this
  have hNc : ∀ x ∈ O, ∀ z, N (act x z) = act x (N z) := by
    intro x hx z
    have e1 : act x z = D.Fl (D.ρ (q.iota ⟨x, hx⟩) (D.Fl.symm z)) := by
      rw [D.hFρ, LinearEquiv.apply_symm_apply]
    rw [hNapp, e1, LinearEquiv.symm_apply_apply, hMι, D'.hFρ, hNapp]
  have hN'c : ∀ x ∈ O, ∀ z, N' (act x z) = act x (N' z) := by
    intro x hx z
    have e1 : act x z = D'.Fl (D'.ρ (q'.iota ⟨x, hx⟩) (D'.Fl.symm z)) := by
      rw [D'.hFρ, LinearEquiv.apply_symm_apply]
    rw [hN'app, e1, LinearEquiv.symm_apply_apply, hM'ι, D.hFρ, hN'app]
  obtain ⟨s, hs⟩ := HDec.QMLattice.commutant N hNc
  obtain ⟨s', hs'⟩ := HDec.QMLattice.commutant N' hN'c
  -- `M' ∘ M = id`
  have hMM : ∀ z, M' (M z) = z := by
    intro z
    have := HDec.HSyn.G0Split.FibreQM.lift_unique D.hΦ (M := M' ∘ₗ M) (M' := LinearMap.id) (fun z => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hM', hM, Category.assoc, g.left, Category.comp_id])
    exact congrArg (fun T => T z) this
  have hMM' : ∀ z, M (M' z) = z := by
    intro z
    have := HDec.HSyn.G0Split.FibreQM.lift_unique D'.hΦ (M := M ∘ₗ M') (M' := LinearMap.id) (fun z => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hM, hM', Category.assoc, g.right, Category.comp_id])
    exact congrArg (fun T => T z) this
  have hss : s' * s = 1 := by
    have e : N' (N D.v) = D.v := by rw [hNapp, hN'app]; simp [hMM]
    rw [hs, hs', smul_smul] at e
    exact D.smul_v_inj (e.trans (one_smul ℂ _).symm)
  -- lattices
  have hNL : ∀ w ∈ L D.v, N w ∈ L D'.v := by
    intro w hw
    rw [hNapp, ← D'.hΛ]
    have hz : D.Fl.symm w ∈ D.Λ := by rw [D.hΛ, LinearEquiv.apply_symm_apply]; exact hw
    rw [← D'.hΦ.2.1, hM, (D.hΦ.2.1 _).2 hz]
    exact MonObj.one_comp _
  have hN'L : ∀ w ∈ L D'.v, N' w ∈ L D.v := by
    intro w hw
    rw [hN'app, ← D.hΛ]
    have hz : D'.Fl.symm w ∈ D'.Λ := by rw [D'.hΛ, LinearEquiv.apply_symm_apply]; exact hw
    rw [← D.hΦ.2.1, hM', (D'.hΦ.2.1 _).2 hz]
    exact MonObj.one_comp _
  obtain ⟨x, hx, hxe⟩ := (mem_qmOrbit_iff _ _).1 (hNL _ D.v_mem)
  obtain ⟨y, hy, hye⟩ := (mem_qmOrbit_iff _ _).1 (hN'L _ D'.v_mem)
  rw [hs] at hxe
  rw [hs'] at hye
  -- `x y = 1 = y x`
  have hxy : x * y = 1 := by
    apply HDec.QMLattice.act_inj D.v_ne
    rw [act_mul, ← hye, HDec.QMLattice.act_smul_vec, ← hxe, smul_smul, hss, one_smul, act_one]
  have hss' : s * s' = 1 := by rw [mul_comm]; exact hss
  have hyx : y * x = 1 := by
    apply HDec.QMLattice.act_inj D'.v_ne
    rw [act_mul, ← hxe, HDec.QMLattice.act_smul_vec, ← hye, smul_smul, hss', one_smul, act_one]
  let u : (↥LeafQM.O)ˣ := ⟨⟨y, hy⟩, ⟨x, hx⟩, Subtype.ext hyx, Subtype.ext hxy⟩
  refine ⟨u, fun a => ?_⟩
  -- `D'.v = s • ι(y) D.v`
  have hv' : D'.v = s • act y D.v := by
    rw [← hye, smul_smul, hss', one_smul]
  apply HDec.QMLattice.act_inj D'.v_ne
  rw [h₂]
  show ψ a • D'.v = act (y * Φ₁.1 a * x) D'.v
  rw [hv', HDec.QMLattice.act_smul_vec, act_mul, act_mul, ← act_mul x y, hxy, act_one, h₁,
    HDec.QMLattice.act_smul_vec, smul_comm]

/-- Base change of an isomorphism of QM pairs along `σQ`. -/
def qmIsoBC {P Q : QMPair Qbar} (f : QMIso P.q Q.q) : QMIso (bcQ P).q (bcQ Q).q where
  φ := @PkgI3.AbVar.Hom.mk' ℂ _ (bcQ P).A (bcQ Q).A
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.φ.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ))))
      (f := f.φ.hom))
  ψ := @PkgI3.AbVar.Hom.mk' ℂ _ (bcQ Q).A (bcQ P).A
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.ψ.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ))))
      (f := f.ψ.hom))
  left := by
    change (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.φ.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.ψ.hom =
      𝟙 ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).obj P.A.X)
    rw [← CategoryTheory.Functor.map_comp, f.left, CategoryTheory.Functor.map_id]
  right := by
    change (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.ψ.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.φ.hom =
      𝟙 ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).obj Q.A.X)
    rw [← CategoryTheory.Functor.map_comp, f.right, CategoryTheory.Functor.map_id]
  equivariant a := by
    change (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map (P.q.iota a).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.φ.hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map f.φ.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))).map (Q.q.iota a).hom
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, f.equivariant a]

/-! ## §8c Eigenvectors of optimal embeddings -/

section Eig

variable {k : Type} [Field k] [NumberField k]

/-- `k = ℚ ⊕ ℚ a₁` for `a₁ ∉ ℚ`. -/
theorem decomp (hk : Module.finrank ℚ k = 2) {a1 : k} (ha1 : ∀ r : ℚ, a1 ≠ algebraMap ℚ k r) (a : k) :
    ∃ s t : ℚ, a = algebraMap ℚ k s + t • a1 := by
  have hli : LinearIndependent ℚ ![(1 : k), a1] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro r h
    apply ha1 r
    rw [← h, Algebra.smul_def, mul_one]
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hk])
  have hmem : a ∈ Submodule.span ℚ (Set.range ![(1 : k), a1]) := hspan ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc]
  simp [Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]

theorem sqrt2_sq : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- **An optimal embedding has an eigenvector `(τ, 1)ᵀ` with `Im τ ≠ 0`**: `ι(Φ(a))(τ, 1)ᵀ = ψ(a)(τ, 1)ᵀ`
for all `a ∈ k` (`k` totally complex, so `ψ(a₁)` is not real for `a₁ ∉ ℚ`). -/
theorem exists_eigvec [NumberField.IsTotallyComplex k] (hk : Module.finrank ℚ k = 2) (Φ : k →ₐ[ℚ] B)
    (ψ : k →+* ℂ) : ∃ τ : ℂ, τ.im ≠ 0 ∧ ∀ a : k, act (Φ a) ![τ, 1] = ψ a • ![τ, 1] := by
  obtain ⟨a0, ha0⟩ := exists_not_rat hk
  set r := (Φ a0).re with hrdef
  set a1 := a0 - algebraMap ℚ k r with ha1def
  have ha1 : ∀ s : ℚ, a1 ≠ algebraMap ℚ k s := by
    intro s h
    apply ha0 (s + r)
    rw [map_add, ← h, ha1def]; ring
  set y0 := Φ a1 with hy0def
  have hy0 : y0 = Φ a0 - algebraMap ℚ B r := by rw [hy0def, ha1def, map_sub, AlgHom.commutes]
  have hre : y0.re = 0 := by
    rw [hy0, QuaternionAlgebra.algebraMap_eq]; simp [hrdef]
  set d := HDec.QMLattice.sqForm y0 with hddef
  have hsq : a1 * a1 = algebraMap ℚ k d := by
    apply Φ.toRingHom.injective
    change Φ (a1 * a1) = Φ (algebraMap ℚ k d)
    rw [map_mul, AlgHom.commutes, ← hy0def]
    exact HDec.QMLattice.pure_sq hre
  set c := ψ a1 with hcdef
  have hc2 : c * c = (d : ℂ) := by
    have := congrArg ψ hsq
    rwa [map_mul, eq_ratCast (algebraMap ℚ k) d, map_ratCast] at this
  have hcim : c.im ≠ 0 := by
    intro h0
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal ψ
    rw [NumberField.ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun a => ?_
    obtain ⟨s, t, rfl⟩ := decomp hk ha1 a
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
    rw [map_add, eq_ratCast (algebraMap ℚ k) s, map_ratCast, Algebra.smul_def, map_mul,
      eq_ratCast (algebraMap ℚ k) t, map_ratCast, ← hcdef]
    simp [h0]
  have hcre : c.re = 0 := by
    have h := congrArg Complex.im hc2
    rw [Complex.mul_im, Complex.ratCast_im] at h
    have h' : c.re * c.im = 0 := by linarith
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact h1
    · exact absurd h1 hcim
  -- the explicit matrix entries
  set A : ℂ := (y0.imI : ℂ) * ((√2 : ℝ) : ℂ) with hAdef
  set Bc : ℂ := -3 * (y0.imJ : ℂ) - 3 * ((√2 : ℝ) : ℂ) * (y0.imK : ℂ) with hBdef
  set C : ℂ := (y0.imJ : ℂ) - ((√2 : ℝ) : ℂ) * (y0.imK : ℂ) with hCdef
  have hid : A * A + Bc * C = (d : ℂ) := by
    rw [hAdef, hBdef, hCdef, hddef, HDec.QMLattice.sqForm]
    push_cast
    linear_combination ((y0.imI : ℂ) ^ 2 + 3 * (y0.imK : ℂ) ^ 2) * sqrt2_sq
  have hAim : A.im = 0 := by simp [hAdef]
  have hBim : Bc.im = 0 := by simp [hBdef]
  have hcA : c - A ≠ 0 := by
    intro h0
    apply hcim
    have := congrArg Complex.im h0
    simpa [hAim] using this
  have hB0 : Bc ≠ 0 := by
    intro h0
    rw [h0, zero_mul, add_zero] at hid
    have hA2 : (A * A).re ≥ 0 := by
      have : A = (A.re : ℂ) := Complex.ext rfl (by simpa using hAim)
      rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]; exact mul_self_nonneg _
    have hc2re : (c * c).re < 0 := by
      have : (c * c).re = -(c.im * c.im) := by rw [Complex.mul_re, hcre]; ring
      rw [this]; exact neg_neg_of_pos (mul_self_pos.mpr hcim)
    rw [hid, ← hc2] at hA2
    linarith
  set τ := Bc / (c - A) with hτdef
  have hτB : τ * (c - A) = Bc := by rw [hτdef]; field_simp
  have hτim : τ.im ≠ 0 := by
    intro h0
    have hτr : τ = (τ.re : ℂ) := Complex.ext rfl (by simpa using h0)
    have hτ0 : τ ≠ 0 := by intro h; rw [h, zero_mul] at hτB; exact hB0 hτB.symm
    have : c - A = Bc / τ := by rw [eq_div_iff hτ0, mul_comm]; exact hτB
    apply hcim
    have him := congrArg Complex.im this
    rw [hτr] at him
    have hBr : Bc = (Bc.re : ℂ) := Complex.ext rfl (by simpa using hBim)
    rw [hBr, ← Complex.ofReal_div] at him
    simpa [hAim] using him
  have heig : act y0 ![τ, 1] = c • ![τ, 1] := by
    have e0 : act y0 ![τ, 1] 0 = (c • ![τ, 1]) 0 := by
      rw [HDec.QMLattice.act_apply0]
      simp only [hre, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
        smul_eq_mul, Rat.cast_zero, zero_add, mul_one]
      rw [← hAdef]
      have : -3 * (y0.imJ : ℂ) - 3 * ((√2 : ℝ) : ℂ) * (y0.imK : ℂ) = Bc := hBdef.symm
      rw [this]
      linear_combination -hτB
    have e1 : act y0 ![τ, 1] 1 = (c • ![τ, 1]) 1 := by
      rw [HDec.QMLattice.act_apply1]
      simp only [hre, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
        smul_eq_mul, Rat.cast_zero, zero_sub, mul_one]
      have hC' : (y0.imJ : ℂ) - ((√2 : ℝ) : ℂ) * (y0.imK : ℂ) = C := hCdef.symm
      have hA' : (y0.imI : ℂ) * ((√2 : ℝ) : ℂ) = A := hAdef.symm
      rw [hC', hA']
      have hd' : (d : ℂ) = 2 * (y0.imI : ℂ) ^ 2 - 3 * (y0.imJ : ℂ) ^ 2 + 6 * (y0.imK : ℂ) ^ 2 := by
        rw [hddef, HDec.QMLattice.sqForm]; push_cast; ring
      rw [hτdef]
      field_simp
      linear_combination ((y0.imI : ℂ) ^ 2 + 3 * (y0.imK : ℂ) ^ 2) * sqrt2_sq - hc2 - hd'
    funext i
    fin_cases i
    · exact e0
    · exact e1
  refine ⟨τ, hτim, fun a => ?_⟩
  obtain ⟨s, t, rfl⟩ := decomp hk ha1 a
  have hψa : ψ (algebraMap ℚ k s + t • a1) = (s : ℂ) + (t : ℂ) * c := by
    rw [map_add, Algebra.smul_def, map_mul, eq_ratCast (algebraMap ℚ k) s, map_ratCast,
      eq_ratCast (algebraMap ℚ k) t, map_ratCast]
  rw [map_add, AlgHom.commutes, map_smul, act_add, HDec.QMLattice.act_algebraMap, act_smul, ← hy0def, heig,
    hψa, add_smul, mul_smul]

end Eig

/-! ## §8d The two existence statements (new LEAFs) and the lattice model they give -/

/-- **LEAF (QM complex tori are abelian surfaces).** For every `τ` in the upper half plane, the complex torus
`ℂ²/ι(𝒪)(τ, 1)ᵀ` with its `𝒪`-action is the analytic space of an abelian surface with QM by `𝒪`: there are an
abelian surface `A/ℂ`, `ι : 𝒪 ↪ End(A)` and an analytic uniformization `Φ : ℂ² → A(ℂ)` with kernel
`Λ_τ = ι(𝒪)(τ, 1)ᵀ` such that `ι(a) ∘ Φ = Φ ∘ ι(a)`.
*Published statement*: Shimura, *On analytic families of polarized abelian varieties and automorphic functions*,
Ann. of Math. 78 (1963), §§2-4 (every QM torus `ℂ²/𝒪v` by a maximal order of an indefinite quaternion algebra
over `ℚ` carries a polarization, of the form `E(x, y) = tr(μ x̄ y)`); with Riemann's theorem and GAGA (Serre 1956)
the polarized torus is the analytic space of an abelian surface and `ι` is algebraic. See also Birkenhake–Lange,
*Complex abelian varieties*, 2nd ed. (2004), Ch. 9 (abelian varieties with endomorphism structure).
Theorem numbers UNVERIFIED. A consequence of the published statements (it asserts nothing about polarizations).
It is also the moduli clause of the research field `shimuraMainThmIDeligneY3AbU` at `u = 1`
(`qmTorusAbelian_of_main`), so the fold `gonzalezRotgerProp56X6_of_main` does not add it as a leaf; the alternative
spec `scratch/gr56-prove/autofold-alt-torus.json` does. -/
def QMTorusAbelian : Prop :=
  ∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (A : PkgI3.AbVar ℂ) (_ : A.dim = 2) (q : QMStr A)
    (Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A (RingHom.id ℂ)),
    ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice hτ.ne') Φ ∧
    ∀ (a : LeafQM.O) (z : Fin 2 → ℂ),
      Φ ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec z) = Φ z ≫ (q.iota a).hom

/-- **LEAF (CM points are algebraic).** A QM abelian surface `(A, ι)` over `ℂ` with complex multiplication
(`End_𝒪(A) ≠ ℤ`) is the base change, along the fixed embedding `σQ : ℚ̄ → ℂ`, of a QM pair over `ℚ̄`.
*Published statement*: Shimura, *Construction of class fields and zeta functions of algebraic curves*, Ann. of
Math. 85 (1967), §§1-3, and Shimura–Taniyama (1961): an abelian variety with complex multiplication is defined
over a number field (the CM points of the Shimura curve are algebraic). Since `σQ(ℚ̄)` is the algebraic closure of
`ℚ` in `ℂ`, a model over a number field inside `ℂ` gives one over `ℚ̄`, and `ι` descends by T11(b) (proved in the
chain). Theorem numbers UNVERIFIED. A consequence of the published statement; **proved below** from the bundle's
existing LEAF `shimuraTaniyamaQbar` (`cmPairDescendsQbar_of_st`), so it is not a new leaf. CM is given as an
element `ψ ∈ End_𝒪(A)` with `ψ² = d < 0`, `d ∈ ℤ` (then `ℚ(√2, √d) ⊂ End⁰(A)` has degree `4 = 2 dim A`). -/
def CMPairDescendsQbar : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (_ : A.dim = 2) (q : QMStr A),
    (∃ d : ℤ, d < 0 ∧ ∃ ψ ∈ com q, ψ * ψ = (d : PkgI3.AbVar.End A)) →
      ∃ P : QMPair Qbar, Nonempty (QMIso (bcQ P).q q)

/-- The lattice data given by `QMTorusAbelian` (with `Fl = id`). -/
theorem latData_of_torus (hC : ZInQ.HomUnify.HomLatticeCorr) {A : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    {q : QMStr A} {τ : ℂ} (hτ : 0 < τ.im) (Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A (RingHom.id ℂ))
    (hΦ : ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice hτ.ne') Φ)
    (hι : ∀ (a : LeafQM.O) (z : Fin 2 → ℂ),
      Φ ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec z) = Φ z ≫ (q.iota a).hom) :
    ∃ D : LatData A q, D.τ = τ := by
  have hR : HDec.HSyn.G0Split.FibreQM.T11aRiemannEnd := ZInQ.HomUnify.t11a_riemannEnd_of_corr hC
  obtain ⟨ρ, hρ, hpres⟩ := HDec.HSyn.G0Split.FibreQM.unif_ring_hom hR A hA _ Φ hΦ
  have hFρ : ∀ (a : O) z, ρ (q.iota a) z = act (a : B) z := by
    intro a z
    have := HDec.HSyn.G0Split.FibreQM.lift_unique hΦ (M := ρ (q.iota a))
      (M' := HDec.QMLattice.actHom (a : B)) (fun z => by
        rw [hρ, HDec.QMLattice.actHom_apply, ← hι a z]; rfl)
    rw [this, HDec.QMLattice.actHom_apply]
  refine ⟨⟨BPAnalytic.QM.qmLattice hτ.ne', inferInstance, Φ, hΦ, ρ, hρ, hpres, LinearEquiv.refl ℂ _, τ, hτ,
    fun z => ?_, fun a z => ?_⟩, rfl⟩
  · rw [HDec.FibreQMNorm.qmLattice_eq_orbit hτ.ne']; rfl
  · exact hFρ a z

/-- **`End_𝒪(A) ≅ R` on the lattice model of an optimal embedding.** If `ι(Φ(a))v = ψ(a)v` for an optimal
embedding `Φ` of `R`, then the scalars of `End_𝒪(A)` are exactly `ψ(R)`, so `End_𝒪(A) ≅ R`, and `A` has CM. -/
theorem com_equiv_of_eig (hC : ZInQ.HomUnify.HomLatticeCorr) {A : PkgI3.AbVar ℂ} (hA : A.dim = 2)
    {q : QMStr A} (D : LatData A q) {k : Type} [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2)
    {R : Subring k} (hc : Nat.Coprime (conductor R) 6) (Φ : GRCountX6.OptEmb k R) (ψ : k →+* ℂ)
    (heig : ∀ a, act (Φ.1 a) D.v = ψ a • D.v) :
    Nonempty (com q ≃+* R) ∧ ∃ d : ℤ, d < 0 ∧ ∃ ψ ∈ com q, ψ * ψ = (d : PkgI3.AbVar.End A) := by
  have hmemO : ∀ a : k, Φ.1 a ∈ LeafQM.O ↔ a ∈ R := by
    intro a
    have h := Φ.2
    constructor
    · intro ha; rw [← h]; exact ha
    · intro ha; rw [← h] at ha; exact ha
  have hψ : ∀ r : R, ∃ e : com q, D.scal e = ψ r := fun r =>
    D.exists_com hC hA ((hmemO r).2 r.2) (heig r)
  obtain ⟨a0, ha0⟩ := exists_not_rat hk
  set y0 := Φ.1 a0 - algebraMap ℚ B (Φ.1 a0).re with hy0def
  have hy0 : y0 = Φ.1 (a0 - algebraMap ℚ k (Φ.1 a0).re) := by rw [map_sub, AlgHom.commutes]
  have hre : y0.re = 0 := by rw [hy0def, QuaternionAlgebra.algebraMap_eq]; simp
  have hy0ne : ¬ (y0.imI = 0 ∧ y0.imJ = 0 ∧ y0.imK = 0) := by
    rintro ⟨h1, h2, h3⟩
    have hz : y0 = 0 := by ext <;> simp [hre, h1, h2, h3]
    have hz' : Φ.1 (a0 - algebraMap ℚ k (Φ.1 a0).re) = Φ.1 0 := by rw [← hy0, hz, map_zero]
    exact ha0 _ (sub_eq_zero.1 (Φ.1.toRingHom.injective hz'))
  have hy0S : y0 ∈ HDec.QMLattice.S D.v := by
    rw [hy0]; exact ⟨_, heig _⟩
  have hψ' : ∀ e : com q, ∃ r : R, ψ r = D.scal e := by
    intro e
    obtain ⟨x, hx, hxe⟩ := D.exists_O hC hA e
    have hxS : x ∈ HDec.QMLattice.S D.v := ⟨_, hxe⟩
    obtain ⟨α, β, hαβ⟩ := HDec.QMLattice.comm_span hre hy0ne
      (HDec.QMLattice.S_comm D.v_ne hxS hy0S)
    set a := algebraMap ℚ k α + β • (a0 - algebraMap ℚ k (Φ.1 a0).re) with hadef
    have hΦa : Φ.1 a = x := by rw [hadef, map_add, AlgHom.commutes, map_smul, ← hy0, hαβ]
    have haR : a ∈ R := (hmemO a).1 (hΦa ▸ hx)
    refine ⟨⟨a, haR⟩, D.smul_v_inj ?_⟩
    rw [← heig, hΦa, hxe]
  -- the ring isomorphism
  obtain ⟨Ψ, hΨ⟩ := HDec.QMLattice.exists_lift D.scalHom (ψ.comp R.subtype)
    (ψ.injective.comp Subtype.val_injective) (fun e => by
      obtain ⟨r, hr⟩ := hψ' e; exact ⟨r, hr⟩)
  have hΨinj : Function.Injective Ψ := by
    intro e e' h
    apply D.scal_injective hC hA
    rw [← LatData.scalHom_apply, ← LatData.scalHom_apply, ← hΨ, ← hΨ, h]
  have hΨsurj : Function.Surjective Ψ := by
    intro r
    obtain ⟨e, he⟩ := hψ r
    refine ⟨e, Subtype.val_injective (ψ.injective ?_)⟩
    have := hΨ e
    simp only [RingHom.comp_apply, Subring.coe_subtype, LatData.scalHom_apply] at this
    rw [this, he]
  refine ⟨⟨RingEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩⟩, ?_⟩
  -- an element of `End_𝒪(A)` with square a negative integer
  obtain ⟨n, hn, hna⟩ := exists_nat_mul_mem R hc (a0 - algebraMap ℚ k (Φ.1 a0).re)
  set y := Φ.1 ((n : k) * (a0 - algebraMap ℚ k (Φ.1 a0).re)) with hydef
  have hy : y = (n : ℚ) • y0 := by
    rw [hydef, map_mul, map_natCast, ← hy0, Algebra.smul_def, map_natCast]
  have hyO : y ∈ LeafQM.O := (hmemO _).2 hna
  have hyre : y.re = 0 := by rw [hy]; simp [hre]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hyne : ¬ (y.imI = 0 ∧ y.imJ = 0 ∧ y.imK = 0) := by
    rintro ⟨h1, h2, h3⟩
    apply hy0ne
    rw [hy] at h1 h2 h3
    simp only [QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul,
      mul_eq_zero, hn0, false_or] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hyS : y ∈ HDec.QMLattice.S D.v := ⟨_, heig _⟩
  have hneg := HDec.QMLattice.sqForm_neg D.hτ.ne' hyre hyS hyne
  have hyy := HDec.QMLattice.pure_sq hyre
  obtain ⟨m, hm⟩ := HDec.QMLattice.int_of_O (LeafQM.O.mul_mem hyO hyO)
    (by rw [hyy]; simp [QuaternionAlgebra.algebraMap_eq])
    (by rw [hyy]; simp [QuaternionAlgebra.algebraMap_eq])
    (by rw [hyy]; simp [QuaternionAlgebra.algebraMap_eq])
  have hmd : (m : ℚ) = HDec.QMLattice.sqForm y := by
    have := congrArg QuaternionAlgebra.re (hyy.symm.trans hm)
    simpa [QuaternionAlgebra.algebraMap_eq] using this.symm
  obtain ⟨c, hc'⟩ := hyS
  obtain ⟨e, he⟩ := D.exists_com hC hA hyO hc'
  refine ⟨m, by exact_mod_cast (hmd ▸ hneg), e, e.2, ?_⟩
  have hee : e * e = ((m : com q)) := by
    apply D.scal_injective hC hA
    rw [← LatData.scalHom_apply, ← LatData.scalHom_apply, map_mul, map_intCast, LatData.scalHom_apply, he]
    apply D.smul_v_inj
    have h1 : act (y * y) D.v = (c * c) • D.v := by
      rw [act_mul, hc', HDec.QMLattice.act_smul_vec, hc', smul_smul]
    have h2 : act (y * y) D.v = (m : ℂ) • D.v := by
      rw [hm, show ((m : B)) = algebraMap ℚ B (m : ℚ) by simp, HDec.QMLattice.act_algebraMap]; push_cast; rfl
    rw [← h1, h2]
  have := congrArg Subtype.val hee
  simpa using this

/-! ## §8e The CM-point map and its bijectivity -/

section Map

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)

/-- The fixed embedding `k → ℂ`. -/
def ψk (k : Type) [Field k] [NumberField k] : k →+* ℂ := (IsAlgClosed.lift : k →ₐ[ℚ] ℂ).toRingHom

/-- The chosen lattice data of the base change `P_ℂ` of a pair. -/
def datQ (P : QMPair Qbar) : LatData (bcQ P).A (bcQ P).q :=
  (exists_latData hU hG hM _ (bcQ P).surface (bcQ P).q).some

variable {k : Type} [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) {R : Subring k}
  (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)

include hk hR in
theorem hψ_datQ (P : QMPair Qbar) (θ : com P.q ≃+* R) :
    (∀ r : R, ∃ e : com (bcQ P).q, (datQ hU hG hM P).scal e = ψk k r) ∧
      (∀ e : com (bcQ P).q, ∃ r : R, ψk k r = (datQ hU hG hM P).scal e) := by
  let θc : com (bcQ P).q ≃+* R := (com_bcQ P).some.symm.trans θ
  let χ : R →+* ℂ := (datQ hU hG hM P).scalHom.comp θc.symm.toRingHom
  refine ⟨fun r => ?_, fun e => ?_⟩
  · obtain ⟨s, hs⟩ := (image_cross hk R hR (ψk k) χ r).1
    exact ⟨θc.symm s, hs⟩
  · obtain ⟨s, hs⟩ := (image_cross hk R hR (ψk k) χ (θc e)).2
    refine ⟨s, hs.trans ?_⟩
    simp [χ, LatData.scalHom_apply]

/-- The optimal embedding of a pair with `End_𝒪 ≅ R`: `a ↦ b` with `ι(b)v = ψ(a)v` on its lattice model. -/
def embP (P : QMPair Qbar) (θ : com P.q ≃+* R) : GRCountX6.OptEmb k R :=
  ⟨emb (datQ hU hG hM P) (AvSplit.Final.h69 hU hG) (bcQ P).surface R hc (ψk k)
      (hψ_datQ hU hG hM hk hR P θ).1,
    emb_opt (datQ hU hG hM P) (AvSplit.Final.h69 hU hG) (bcQ P).surface R hc (ψk k)
      (hψ_datQ hU hG hM hk hR P θ).1 (hψ_datQ hU hG hM hk hR P θ).2⟩

theorem embP_spec (P : QMPair Qbar) (θ : com P.q ≃+* R) (a : k) :
    act ((embP hU hG hM hk hR hc P θ).1 a) (datQ hU hG hM P).v = ψk k a • (datQ hU hG hM P).v :=
  emb_spec _ _ _ _ _ _ _ a

/-- **The CM-point map** `CM(R) → Emb(R, 𝒪)/𝒪^×`, `[(A, ι)] ↦ [Φ_{(A, ι)}]`. -/
def cmMap (c : CMSet R) : Quot (GRCountX6.ConjRel R) :=
  Quot.mk _ (embP hU hG hM hk hR hc c.2.choose c.2.choose_spec.2.some)

/-- **The CM-point map is injective** (glue, from the textbook fields `uniformizationLeafAll`,
`gagaMorphism`, `mumfordTorsionAlgClosed`): conjugate embeddings give proportional lattices, hence isomorphic
pairs over `ℂ`, hence over `ℚ̄` (T11(b)). -/
theorem cmMap_injective : Function.Injective (cmMap hU hG hM hk hR hc) := by
  intro c1 c2 h
  have hC := AvSplit.Final.h69 hU hG
  obtain ⟨a0, ha0⟩ := exists_not_rat hk
  have hrel := (GRCountX6.conjRel_equivalence R).eqvGen_iff.mp (Quot.eqvGen_exact h)
  obtain ⟨u, hu⟩ := hrel
  set Φ2 := embP hU hG hM hk hR hc c2.2.choose c2.2.choose_spec.2.some
  have hb : Φ2.1 a0 ∉ Set.range (algebraMap ℚ B) := by
    rintro ⟨r, hr⟩
    apply ha0 r
    apply Φ2.1.toRingHom.injective
    change Φ2.1 a0 = Φ2.1 (algebraMap ℚ k r)
    rw [AlgHom.commutes, hr]
  obtain ⟨f⟩ := iso_of_conj hC (bcQ c1.2.choose).surface (bcQ c2.2.choose).surface
    (datQ hU hG hM c1.2.choose) (datQ hU hG hM c2.2.choose) _ (Φ2.1 a0) hb (ψk k a0)
    (embP_spec hU hG hM hk hR hc _ _ a0) (embP_spec hU hG hM hk hR hc _ _ a0) u (hu a0)
  obtain ⟨g⟩ := qmIso_descend _ _ f
  apply Subtype.ext
  rw [← c1.2.choose_spec.1, ← c2.2.choose_spec.1]
  exact Quotient.sound ⟨g⟩

end Map

/-- **The CM points by `R` inject into the `𝒪^×`-classes of optimal embeddings `R ↪ 𝒪`** (glue, from the
textbook fields `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`). -/
theorem exists_injective_optEmb (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (k : Type) [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6) :
    ∃ F : CMSet R → Quot (GRCountX6.ConjRel R), Function.Injective F :=
  ⟨cmMap hU hG hM hk hR hc, cmMap_injective hU hG hM hk hR hc⟩

/-- **`#CM(R) ≤ #(optimal embeddings mod 𝒪^×)`**, whenever the right side is finite. -/
theorem card_cmSet_le (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (k : Type) [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    (hfin : Finite (Quot (GRCountX6.ConjRel R))) :
    Finite (CMSet R) ∧ Nat.card (CMSet R) ≤ Nat.card (Quot (GRCountX6.ConjRel R)) := by
  obtain ⟨F, hF⟩ := exists_injective_optEmb hU hG hM k hk R hR hc
  exact ⟨Finite.of_injective F hF, Nat.card_le_card_of_injective F hF⟩

/-! ## §8f Surjectivity of the CM-point map from the two existence leaves -/

/-- The unit `1 + i` of `𝒪` (reduced norm `−1`). -/
def uI : (↥LeafQM.O)ˣ :=
  ⟨⟨LeafQM.ofInt ![1, 1, 0, 0], ![1, 1, 0, 0], rfl⟩, ⟨LeafQM.ofInt ![-1, 1, 0, 0], ![-1, 1, 0, 0], rfl⟩,
    Subtype.ext GRCountX6.one_add_i_mem_units.1, Subtype.ext GRCountX6.one_add_i_mem_units.2.1⟩

section ConjEmb

variable {k : Type} [Field k] [NumberField k] {R : Subring k}

/-- Conjugation by a unit of `𝒪` as a `ℚ`-algebra map of `B`. -/
def conjAlg (u : (↥LeafQM.O)ˣ) : B →ₐ[ℚ] B where
  toFun x := ((u : LeafQM.O) : B) * x * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B)
  map_one' := by simp only [mul_one]; exact GRCountX6.unit_mul_inv u
  map_mul' x y := by
    have hUiU := GRCountX6.unit_inv_mul u
    calc ((u : LeafQM.O) : B) * (x * y) * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B)
        = ((u : LeafQM.O) : B) * x * ((((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) * ((u : LeafQM.O) : B)) * y *
            (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) := by rw [hUiU, mul_one]; noncomm_ring
      _ = _ := by noncomm_ring
  map_zero' := by simp only [mul_zero, zero_mul]
  map_add' x y := by simp only [mul_add, add_mul]
  commutes' r := by
    show ((u : LeafQM.O) : B) * algebraMap ℚ B r * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) = algebraMap ℚ B r
    rw [← Algebra.commutes r ((u : LeafQM.O) : B), mul_assoc, GRCountX6.unit_mul_inv u, mul_one]

theorem conjAlg_apply (u : (↥LeafQM.O)ˣ) (x : B) :
    conjAlg u x = ((u : LeafQM.O) : B) * x * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) := rfl

theorem conjAlg_mem (u : (↥LeafQM.O)ˣ) (x : B) : conjAlg u x ∈ LeafQM.O ↔ x ∈ LeafQM.O := by
  rw [conjAlg_apply]
  have hUiU := GRCountX6.unit_inv_mul u
  constructor
  · intro h
    have : x = (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) *
        (((u : LeafQM.O) : B) * x * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B)) * ((u : LeafQM.O) : B) := by
      calc x = ((((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) * ((u : LeafQM.O) : B)) * x *
            ((((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) * ((u : LeafQM.O) : B)) := by
            rw [hUiU, one_mul, mul_one]
        _ = _ := by noncomm_ring
    rw [this]
    exact LeafQM.O.mul_mem (LeafQM.O.mul_mem (u⁻¹ : (↥LeafQM.O)ˣ).1.2 h) u.1.2
  · intro h
    exact LeafQM.O.mul_mem (LeafQM.O.mul_mem u.1.2 h) (u⁻¹ : (↥LeafQM.O)ˣ).1.2

theorem optEmb_mem (Φ : GRCountX6.OptEmb k R) (a : k) : Φ.1 a ∈ LeafQM.O ↔ a ∈ R := by
  have h := Φ.2
  constructor
  · intro ha; rw [← h]; exact ha
  · intro ha; rw [← h] at ha; exact ha

/-- Conjugating an optimal embedding by a unit of `𝒪`. -/
def conjEmb (u : (↥LeafQM.O)ˣ) (Φ : GRCountX6.OptEmb k R) : GRCountX6.OptEmb k R :=
  ⟨(conjAlg u).comp Φ.1, Subring.ext fun a => by
    show conjAlg u (Φ.1 a) ∈ LeafQM.O ↔ a ∈ R
    rw [conjAlg_mem, optEmb_mem]⟩

theorem conjEmb_apply (u : (↥LeafQM.O)ˣ) (Φ : GRCountX6.OptEmb k R) (a : k) :
    (conjEmb u Φ).1 a = ((u : LeafQM.O) : B) * Φ.1 a * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : B) := rfl

theorem conjRel_conjEmb (u : (↥LeafQM.O)ˣ) (Φ : GRCountX6.OptEmb k R) :
    GRCountX6.ConjRel R Φ (conjEmb u Φ) := ⟨u, fun _ => rfl⟩

theorem act_uI (τ : ℂ) :
    act ((uI : LeafQM.O) : B) ![τ, 1] = ![(1 + ((√2 : ℝ) : ℂ)) * τ, 1 - ((√2 : ℝ) : ℂ)] := by
  have hU : ((uI : LeafQM.O) : B) = ⟨1, 1, 0, 0⟩ := by
    ext <;> simp [uI, LeafQM.ofInt]
  have e0 : act ((uI : LeafQM.O) : B) ![τ, 1] 0 = (1 + ((√2 : ℝ) : ℂ)) * τ := by
    rw [HDec.QMLattice.act_apply0, hU]; simp; try ring
  have e1 : act ((uI : LeafQM.O) : B) ![τ, 1] 1 = 1 - ((√2 : ℝ) : ℂ) := by
    rw [HDec.QMLattice.act_apply1, hU]; simp; try ring
  funext i
  fin_cases i
  · exact e0
  · exact e1

/-- **From the lower to the upper half plane**: conjugating by `1 + i` (norm `−1`) moves the eigenvector. -/
theorem eig_conj_uI (Φ : GRCountX6.OptEmb k R) (ψ : k →+* ℂ) {τ : ℂ} (hτ : τ.im < 0)
    (heig : ∀ a, act (Φ.1 a) ![τ, 1] = ψ a • ![τ, 1]) :
    ∃ τ' : ℂ, 0 < τ'.im ∧ ∀ a, act ((conjEmb uI Φ).1 a) ![τ', 1] = ψ a • ![τ', 1] := by
  set s : ℝ := √2 with hs
  have hs1 : (1 : ℝ) < s := by
    rw [hs, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hden : (1 - (s : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  set κ : ℝ := (1 + s) / (1 - s) with hκ
  have hκneg : κ < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
  refine ⟨(κ : ℂ) * τ, ?_, fun a => ?_⟩
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos_of_neg_of_neg hκneg hτ
  · have hv : (![(κ : ℂ) * τ, 1] : Fin 2 → ℂ) =
        (1 - (s : ℂ))⁻¹ • act ((uI : LeafQM.O) : B) ![τ, 1] := by
      rw [act_uI, ← hs]
      funext i; fin_cases i
      · simp [hκ]; field_simp
      · simp; field_simp
    have hUiU := GRCountX6.unit_inv_mul uI
    rw [hv, conjEmb_apply, HDec.QMLattice.act_smul_vec, act_mul, act_mul, ← act_mul _ ((uI : LeafQM.O) : B), hUiU, act_one,
      heig, HDec.QMLattice.act_smul_vec, smul_comm]

end ConjEmb

section Surj

variable (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed)
  {k : Type} [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) {R : Subring k}
  (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)

/-- **The CM-point map is surjective** (from `QMTorusAbelian`, `CMPairDescendsQbar` and the textbook fields):
an optimal embedding `Φ` has an eigenvector `(τ, 1)ᵀ`, `Im τ > 0` after conjugating by `1 + i`; the QM torus
`ℂ²/ι(𝒪)(τ, 1)ᵀ` is an abelian surface with `End_𝒪 ≅ R`, it descends to `ℚ̄`, and its lattice model compares to
the chosen one by a unit of `𝒪`. -/
theorem cmMap_surjective [NumberField.IsTotallyComplex k] (hE1 : QMTorusAbelian)
    (hE2 : CMPairDescendsQbar) : Function.Surjective (cmMap hU hG hM hk hR hc) := by
  have hC := AvSplit.Final.h69 hU hG
  have pos : ∀ (Φ : GRCountX6.OptEmb k R) (τ : ℂ) (hτ : 0 < τ.im),
      (∀ a, act (Φ.1 a) ![τ, 1] = ψk k a • ![τ, 1]) →
        ∃ c, cmMap hU hG hM hk hR hc c = Quot.mk _ Φ := by
    intro Φ τ hτ heig
    obtain ⟨A, hA, q, Φu, hΦu, hι⟩ := hE1 τ hτ
    obtain ⟨D', hD'⟩ := latData_of_torus hC hA hτ Φu hΦu hι
    have heig' : ∀ a, act (Φ.1 a) D'.v = ψk k a • D'.v := by
      intro a; rw [LatData.v, hD']; exact heig a
    obtain ⟨⟨θ⟩, hd⟩ := com_equiv_of_eig hC hA D' hk hc Φ (ψk k) heig'
    obtain ⟨Q, ⟨g⟩⟩ := hE2 A hA q hd
    let θQ : com Q.q ≃+* R := ((com_bcQ Q).some.trans (comEquiv g)).trans θ
    let c : CMSet R := ⟨Quotient.mk _ Q, Q, rfl, ⟨θQ⟩⟩
    refine ⟨c, ?_⟩
    have hP0 : Quotient.mk (pairSetoid Qbar) c.2.choose = Quotient.mk _ Q := c.2.choose_spec.1
    have hiso : Nonempty (QMIso c.2.choose.q Q.q) := Quotient.exact hP0
    obtain ⟨f0⟩ := hiso
    exact Quot.sound (conj_of_iso hC (bcQ c.2.choose).surface hA (datQ hU hG hM c.2.choose) D'
      ((qmIsoBC f0).trans g) (ψk k) _ Φ (embP_spec hU hG hM hk hR hc _ _) heig')
  intro x
  induction x using Quot.ind with
  | mk Φ =>
    obtain ⟨τ0, hτ0, heig0⟩ := exists_eigvec hk Φ.1 (ψk k)
    rcases lt_or_gt_of_ne hτ0 with hneg | hpos
    · obtain ⟨τ1, hτ1, heig1⟩ := eig_conj_uI Φ (ψk k) hneg heig0
      obtain ⟨c, hc'⟩ := pos (conjEmb uI Φ) τ1 hτ1 heig1
      exact ⟨c, hc'.trans (Quot.sound (conjRel_conjEmb uI Φ)).symm⟩
    · exact pos Φ τ0 hpos heig0

end Surj

/-- **`CMPointsOptEmb6` (gt-grcount's consequence statement) proved** from the two existence leaves and the
textbook fields: the CM-point map is a bijection. -/
theorem cmPointsOptEmb6_of (hE1 : QMTorusAbelian) (hE2 : CMPairDescendsQbar)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : GRCountX6.CMPointsOptEmb6 := by
  intro k _ _ _ hk R hR hc
  exact ⟨Equiv.ofBijective (cmMap hU hG hM hk hR hc)
    ⟨cmMap_injective hU hG hM hk hR hc, cmMap_surjective hU hG hM hk hR hc hE1 hE2⟩⟩

/-- **`R5fpCount` from Eichler's count, the two existence leaves and the textbook fields.** -/
theorem r5fpCount_of_leaves (hE : GRCountX6.EichlerOptEmbCount6) (hE1 : QMTorusAbelian)
    (hE2 : CMPairDescendsQbar) (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : R5fpCount :=
  GRCountX6.r5fpCount_of_eichler hE (cmPointsOptEmb6_of hE1 hE2 hU hG hM)

/-- **The field `gonzalezRotgerProp56X6` from Eichler's count, the two existence leaves and the textbook
fields** (`uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed` of `OpenTextbookLeaves11`). -/
theorem gonzalezRotgerProp56X6_of_leaves (hE : GRCountX6.EichlerOptEmbCount6) (hE1 : QMTorusAbelian)
    (hE2 : CMPairDescendsQbar) (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    GRCountX6.GonzalezRotgerProp56X6 :=
  GRCountX6.prop56X6_of_r5fpCount (r5fpCount_of_leaves hE hE1 hE2 hU hG hM)

/-! ## §8g `CMPairDescendsQbar` from the bundle's LEAF `shimuraTaniyamaQbar` -/

/-- Two embeddings `ℚ̄ → ℂ` differ by an endomorphism of `ℚ̄`: both land in the algebraic closure `E` of `ℚ` in
`ℂ`, and `σQ : ℚ̄ → E` is bijective (`E` is integral over the algebraically closed `ℚ̄`). -/
theorem exists_alpha (ιe : Qbar →+* ℂ) : ∃ α : Qbar →+* Qbar, σQ.comp α = ιe := by
  let E : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ
  have hmem : ∀ (g : Qbar →+* ℂ) (x : Qbar), g x ∈ E := fun g x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic x).algHom g.toRatAlgHom
  let fσ : Qbar →+* E := σQ.codRestrict E (hmem σQ)
  have hint : fσ.IsIntegral := by
    intro z
    have hz : IsIntegral ℚ z := (IntermediateField.isIntegral_iff (S := E)).2
      ((mem_algebraicClosure_iff' (F := ℚ) (E := ℂ)).1 z.2)
    have hcomp : fσ.comp (algebraMap ℚ Qbar) = algebraMap ℚ E := Subsingleton.elim _ _
    apply RingHom.isIntegralElem.of_comp (algebraMap ℚ Qbar) fσ
    rw [hcomp]; exact hz
  have hbij : Function.Bijective fσ := IsAlgClosed.ringHom_bijective_of_isIntegral fσ hint
  let e := RingEquiv.ofBijective fσ hbij
  refine ⟨e.symm.toRingHom.comp (ιe.codRestrict E (hmem ιe)), RingHom.ext fun x => ?_⟩
  have h1 : fσ (e.symm ⟨ιe x, hmem ιe x⟩) = ⟨ιe x, hmem ιe x⟩ := e.apply_symm_apply _
  exact congrArg Subtype.val h1

section STQ

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

/-- `f ↦ e⁻¹ ∘ f ∘ e`, `End B → End A`, for an isomorphism of group objects `e : A ≅ B` (copied from
`RayClassCFT.conjEnd`, `ZInQKernel/Contrib/OneProof/RayClassShimura.lean` L2526). -/
def conjEnd {L : Type} [Field L] {A B : PkgI3.AbVar L} (e : A.X ≅ B.X) (h1 : IsMonHom e.hom)
    (h2 : IsMonHom e.inv) : PkgI3.AbVar.End B →+* PkgI3.AbVar.End A where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ A A (e.hom ≫ f.hom ≫ e.inv) inferInstance
  map_one' := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ 𝟙 _ ≫ e.inv = 𝟙 _
    simp)
  map_mul' f g := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ (g.hom ≫ f.hom) ≫ e.inv = (e.hom ≫ g.hom ≫ e.inv) ≫ (e.hom ≫ f.hom ≫ e.inv)
    simp)
  map_zero' := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ (1 : B.X ⟶ B.X) ≫ e.inv = 1
    rw [MonObj.one_comp, MonObj.comp_one])
  map_add' f g := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ (f.hom * g.hom) ≫ e.inv = (e.hom ≫ f.hom ≫ e.inv) * (e.hom ≫ g.hom ≫ e.inv)
    rw [MonObj.mul_comp, MonObj.comp_mul])

theorem conjEnd_hom {L : Type} [Field L] {A B : PkgI3.AbVar L} (e : A.X ≅ B.X) (h1 : IsMonHom e.hom)
    (h2 : IsMonHom e.inv) (f : PkgI3.AbVar.End B) : (conjEnd e h1 h2 f).hom = e.hom ≫ f.hom ≫ e.inv := rfl

/-- `A₀ ×_{ℚ̄, α} ℚ̄`. -/
abbrev bcα (α : Qbar →+* Qbar) (A₀ : PkgI3.AbVar Qbar) : PkgI3.AbVar Qbar :=
  @PkgI3.AbVar.baseChange Qbar _ A₀ Qbar _ α.toAlgebra

/-- **Base change along `σQ ∘ α` is base change along `α`, then along `σQ`** (as group objects; G0StableBC's
pasting lemma `exists_pbPaste`, which avoids the kernel timeout of a direct proof). -/
theorem bc_comp_iso (α : Qbar →+* Qbar) (ιe : Qbar →+* ℂ) (hα : σQ.comp α = ιe) (A₀ : PkgI3.AbVar Qbar) :
    ∃ I : ((bcα α A₀).baseChange ℂ).X ≅ (HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.bcC ιe A₀).X,
      IsMonHom I.hom := by
  have sq : Spec.map (CommRingCat.ofHom σQ) ≫ Spec.map (CommRingCat.ofHom α) =
      Spec.map (CommRingCat.ofHom ιe) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hα]
  exact G0StableBC.exists_pbPaste _ _ _ sq A₀.X

/-- **`CMPairDescendsQbar` from the bundle's LEAF `shimuraTaniyamaQbar`** (Shimura–Taniyama, model over `ℚ̄` of a
CM abelian variety; field of `OpenAddedLeaves17`). The CM element `ψ`, `ψ² = d < 0`, and `ι(i)` give
`ℚ(√2, √d) ⊂ End⁰(A)` of degree 4 (`QMSplitSTQM.embed_Ed`), so `A ≅ A₀ ×_{ℚ̄, ιe} ℂ`; writing `ιe = σQ ∘ α`
(`exists_alpha`), `A ≅ (A₀ ×_α ℚ̄) ×_{σQ} ℂ` (`bc_comp_iso`), and `ι` descends by T11(b) (`endBC_bijective`). -/
theorem cmPairDescendsQbar_of_st
    (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar) : CMPairDescendsQbar := by
  intro A hA q hcm
  obtain ⟨d, hd, ψ, hψ, hψψ⟩ := hcm
  haveI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (algebraMap ℚ
      HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.K1 (d : ℚ)))) :=
    ⟨HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.irr_d d (by exact_mod_cast hd)⟩
  obtain ⟨f, hf⟩ := HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.embed_Ed q d hd ψ hψ hψψ
  obtain ⟨ιe, A₀, e, e', h1, h2⟩ := hST A hA (HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.Ed (d : ℚ))
    (HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.Ed_finrank (d : ℚ)) ⟨f, hf⟩
  obtain ⟨α, hα⟩ := exists_alpha ιe
  obtain ⟨I, hI⟩ := bc_comp_iso α ιe hα A₀
  let F : ((bcα α A₀).baseChange ℂ).X ≅ A.X := I ≪≫ ⟨e.hom, e'.hom, h1, h2⟩
  have hF1 : IsMonHom F.hom := (inferInstance : IsMonHom (I.hom ≫ e.hom))
  have hF2 : IsMonHom F.inv := inferInstance
  have hdim : (bcα α A₀).dim = 2 := by
    rw [← PkgI3.AbVar.dim_baseChange (bcα α A₀) ℂ]
    have he : topologicalKrullDim ((bcα α A₀).baseChange ℂ).X.left = topologicalKrullDim A.X.left :=
      IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso ((Over.forget _).mapIso F)).isHomeomorph
    exact he.trans hA
  let qC : LeafQM.O →+* PkgI3.AbVar.End ((bcα α A₀).baseChange ℂ) := (conjEnd F hF1 hF2).comp q.iota
  have hqC : Function.Injective qC := by
    intro a b hab
    apply q.injective
    apply PkgI3.AbVar.Hom.ext'
    have := congrArg PkgI3.AbVar.Hom.hom hab
    simp only [qC, RingHom.comp_apply, conjEnd_hom] at this
    simpa using this
  let eBC := RingEquiv.ofBijective _ (endBC_bijective (bcα α A₀))
  let q₀ : QMStr (bcα α A₀) := ⟨eBC.symm.toRingHom.comp qC, eBC.symm.injective.comp hqC⟩
  have hq₀ : ∀ a, HDec.G0ModField.KernelField.endBC (bcα α A₀) ℂ (q₀.iota a) = qC a := fun a =>
    eBC.apply_symm_apply (qC a)
  refine ⟨⟨bcα α A₀, hdim, q₀⟩, ⟨⟨@PkgI3.AbVar.Hom.mk' ℂ _ _ _ F.hom hF1,
    @PkgI3.AbVar.Hom.mk' ℂ _ _ _ F.inv hF2, F.hom_inv_id, F.inv_hom_id, fun a => ?_⟩⟩⟩
  change (HDec.G0ModField.KernelField.endBC (bcα α A₀) ℂ (q₀.iota a)).hom ≫ F.hom = F.hom ≫ (q.iota a).hom
  rw [hq₀]
  change (F.hom ≫ (q.iota a).hom ≫ F.inv) ≫ F.hom = F.hom ≫ (q.iota a).hom
  simp

end STQ

/-- **The field `gonzalezRotgerProp56X6` from Eichler's count, `QMTorusAbelian`, the bundle's LEAF
`shimuraTaniyamaQbar` and the textbook fields.** The form for the fold: one new leaf besides Eichler's. -/
theorem gonzalezRotgerProp56X6_of_st (hE : GRCountX6.EichlerOptEmbCount6) (hE1 : QMTorusAbelian)
    (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : GRCountX6.GonzalezRotgerProp56X6 :=
  gonzalezRotgerProp56X6_of_leaves hE hE1 (cmPairDescendsQbar_of_st hST) hU hG hM

/-- `CMPointsOptEmb6` from `QMTorusAbelian`, `shimuraTaniyamaQbar` and the textbook fields. -/
theorem cmPointsOptEmb6_of_st (hE1 : QMTorusAbelian)
    (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : GRCountX6.CMPointsOptEmb6 :=
  cmPointsOptEmb6_of hE1 (cmPairDescendsQbar_of_st hST) hU hG hM

/-- **`QMTorusAbelian` from the bundle's field `shimuraMainThmIDeligneY3AbU`** (its moduli clause `ModuliAtUnits`
at `u = 1`: the object at `Ψ(τ, 1)` is the QM torus `ℂ²/ι(𝒪)(τ, 1)ᵀ`). -/
theorem qmTorusAbelian_of_main (h : RayClassCFT.ShimuraMainThmIDeligneY3AbU) : QMTorusAbelian := by
  obtain ⟨Y, Φ, -, Ψ, -, hmod⟩ := h
  intro τ hτ
  obtain ⟨P, -, Φu, hΦu, hι⟩ := hmod 1 (by refine ⟨?_, ?_⟩ <;> simpa using RayClassCFT.OhatQ_one) ⟨τ, hτ⟩
  exact ⟨P.A, P.surface, P.q, Φu, hΦu, hι⟩

/-- **The field from Eichler's count and three fields already in the bundles**: `shimuraMainThmIDeligneY3AbU`
(research), `shimuraTaniyamaQbar` (added) and the textbook fields. The form for the fold: Eichler's count is
the only new leaf. -/
theorem gonzalezRotgerProp56X6_of_main (hE : GRCountX6.EichlerOptEmbCount6)
    (hS : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : GRCountX6.GonzalezRotgerProp56X6 :=
  gonzalezRotgerProp56X6_of_st hE (qmTorusAbelian_of_main hS) hST hU hG hM

/-- `CMPointsOptEmb6` from the bundle fields `shimuraMainThmIDeligneY3AbU`, `shimuraTaniyamaQbar` and the
textbook fields (no new leaf). -/
theorem cmPointsOptEmb6_of_main (hS : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : GRCountX6.CMPointsOptEmb6 :=
  cmPointsOptEmb6_of (qmTorusAbelian_of_main hS) (cmPairDescendsQbar_of_st hST) hU hG hM

/-! ## §9 The upper bound `#CM(R) ≤ 2^{b(k)} h(R)` from Eichler's count -/

/-- **`R5fpCountLe` (GLUE; the upper half of `LeafQM.AV.R5fpCount`, the only half the chain uses).** For an order
`R` of conductor prime to `6` in an imaginary quadratic field `k` with `h(R) ≠ 0`, the CM points by `R` on `X₆`
(isomorphism classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R`) are finitely many and at most
`2^{inertCount6 k} · h(R)`. Implied by `R5fpCount` (`r5fpCountLe_of_r5fpCount`) and so by the field
`gonzalezRotgerProp56X6` with any witness; proved from Eichler's count `GRCountX6.EichlerOptEmbCount6` and the
textbook fields (`r5fpCountLe_of_eichler`). -/
def R5fpCountLe : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      Nat.card (CommRing.Pic R) ≠ 0 →
        Finite {c : Quotient (pairSetoid Qbar) //
            ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} ∧
        Nat.card {c : Quotient (pairSetoid Qbar) //
            ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} ≤
          2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

/-- `R5fpCountLe` is weaker than the kernel's `R5fpCount` (hence than the field with any witness). -/
theorem r5fpCountLe_of_r5fpCount (h : R5fpCount) : R5fpCountLe := by
  intro k _ _ _ hk R hR hc hh
  by_cases hne : Nonempty (CMSet R)
  · obtain ⟨⟨c, P, hP, hθ⟩⟩ := hne
    have hcard := h k hk R hR hc ⟨P, hθ⟩
    have hpos : Nat.card (CMSet R) ≠ 0 := by
      rw [hcard]; exact Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) hh
    exact ⟨Nat.finite_of_card_ne_zero hpos, hcard.le⟩
  · rw [not_nonempty_iff] at hne
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

/-- `∏_{p ∣ 6} (1 − (k/p)) ≤ 2^{inertCount6 k}`. -/
theorem eichlerFactor6_le (k : Type) [Field k] [NumberField k] :
    GRCountX6.eichlerFactor6 k ≤ 2 ^ inertCount6 k := by
  unfold GRCountX6.eichlerFactor6 GRCountX6.eichlerLocal inertCount6
  split_ifs <;> norm_num

/-- **`R5fpCountLe` from Eichler's optimal-embedding count and the textbook fields.** -/
theorem r5fpCountLe_of_eichler (hE : GRCountX6.EichlerOptEmbCount6)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R5fpCountLe := by
  intro k _ _ _ hk R hR hc _
  obtain ⟨hfin, hcard⟩ := hE k hk R hR hc
  obtain ⟨hf, hle⟩ := card_cmSet_le hU hG hM k hk R hR hc hfin
  refine ⟨hf, hle.trans ?_⟩
  rw [hcard, mul_comm]
  exact Nat.mul_le_mul_right _ (eichlerFactor6_le k)

end GR56

/-! ## §10 The chain's consumer of the count, rerouted to `R5fpCountLe`

`HDec.FS5NoCM.nocm_on_witness` (TailC L1371) uses `R5fpCount` only to bound `#CM(R) ≤ 2`. Below: the same
proof with `GR56.R5fpCountLe` (copied from TailC L1371-1452 with the count step changed), and the four wrappers
up to `fibreComTrivialFull_of_leaves''` (TailC L1458, L1480, L2071, L2289), verbatim but for the hypothesis. -/

namespace HDec

namespace FS5NoCM

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin _root_.ZInQ ZInQ ZInQ.JHeight PkgI3

set_option maxHeartbeats 1000000 in
/-- `nocm_on_witness` (TailC L1371) with `R5fpCountLe` in place of `R5fpCount`. -/
theorem nocm_on_witness_le (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (hW : R1R2fpFullProps Y Φ X Ψ fY π₆)
    (u : ℚ) (hu : u ∉ contactSet) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar)
    (hP : Φ Qbar y = M3.mk P)
    (hv : (π₆.comp fY.left).val (K := Qbar) y.left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u))) :
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : AbVar.End P.A) := by
  obtain ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ := hW
  have hx : Ψ (y ≫ fY) = Quotient.mk _ P.forget := hX.2.2.2.2.2 y P hP
  have hv' : π₆.val (K := Qbar) (y ≫ fY).left =
      OnePoint.some (algebraMap ℚ Qbar (Jmap u)) := by
    exact (ToP1.val_comp_right π₆ fY.left y.left).symm.trans hv
  rcases hA P.forget with hZ | ⟨k, _, _, _, hk2, R, hR, hc0, ⟨e⟩⟩
  · exact hZ
  exfalso
  have hcop : Nat.Coprime (conductor R) 6 := hB P.forget k hk2 R hR hc0 ⟨e⟩
  obtain ⟨hdeg, hemb⟩ := h5 k hk2 R hR hcop (y ≫ fY) P.forget hx ⟨e⟩
  -- the fibre over `J(u)` (N2) and its residue field `ℚ(i)`
  obtain ⟨hres, f, hf, hfv⟩ := hK Y Φ X Ψ fY π₆ ⟨h1, hh, hX, h2, hE, hrec, hS, h5⟩ (Jmap u)
    (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u)
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos
  obtain ⟨ha, hb⟩ := elkies_sq u i hi
  have hresEq : residueImage (X := X.left) (y ≫ fY).left = IntermediateField.adjoin ℚ {i} := by
    rw [hres _ hv' _ _ ha hb]
    exact adjoin_pair_eq i _ _ (GlueRepo.PR.h₁_ne_zero u)
  have hfin : Module.finrank ℚ (residueImage (X := X.left) (y ≫ fY).left) = 2 := by
    rw [hresEq]; exact finrank_adjoin_sqrt_neg_one i hi
  rw [hfin] at hdeg
  -- four distinct classes with CM by `R`
  have hmemS : ∀ j : Fin 4, ∃ P' : QMPair Qbar, Quotient.mk _ P' = Ψ (f j) ∧
      Nonempty (com P'.q ≃+* R) := by
    intro j
    refine ⟨Quotient.out (Ψ (f j)), Quotient.out_eq _, ?_⟩
    have hQ : Ψ (f j) = Quotient.mk _ (Quotient.out (Ψ (f j))) := (Quotient.out_eq _).symm
    obtain ⟨α, ⟨g⟩⟩ := ((h2 (y ≫ fY) (f j) P.forget _ hx hQ).1).1 (hv'.trans (hfv j).symm)
    exact ⟨((comEquiv g).symm.trans (RingEquiv.subringCongr (com_twist P.forget.q α))).trans e⟩
  let F : Fin 4 → {c : Quotient (pairSetoid Qbar) //
      ∃ P' : QMPair Qbar, Quotient.mk _ P' = c ∧ Nonempty (com P'.q ≃+* R)} :=
    fun j => ⟨Ψ (f j), hmemS j⟩
  have hFinj : Function.Injective F := fun a b hab =>
    hf (Ψ.injective (congrArg Subtype.val hab))
  -- `2^{b(k)} h(R) = 2`
  have hval : 2 ^ inertCount6 k * Nat.card (CommRing.Pic R) = 2 := by
    by_cases hb0 : inertCount6 k = 0
    · simp only [hb0, ↓reduceIte] at hdeg
      rw [hb0]; omega
    · simp only [hb0, ↓reduceIte] at hdeg
      have hh1 : Nat.card (CommRing.Pic R) = 1 := by omega
      obtain ⟨e'⟩ := hemb hb0
      have hik : i ∈ residueImage (X := X.left) (y ≫ fY).left := by
        rw [hresEq]; exact IntermediateField.mem_adjoin_simple_self ℚ i
      have : FiniteDimensional ℚ (residueImage (X := X.left) (y ≫ fY).left) :=
        Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
      have hsurj : Function.Surjective e'.toLinearMap := by
        rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hk2, hfin])]
        exact e'.toRingHom.injective
      obtain ⟨ι, hι⟩ := hsurj ⟨i, hik⟩
      have hι2 : ι ^ 2 = -1 := by
        apply e'.toRingHom.injective
        change e' (ι ^ 2) = e' (-1)
        rw [map_pow, map_neg, map_one]
        have : e' ι = ⟨i, hik⟩ := hι
        rw [this]
        apply Subtype.ext
        simp [hi]
      have h2n := two_not_prime_of_sqrt_neg_one ι hι2
      have hb1 : inertCount6 k = 1 := by
        have : inertCount6 k ≤ 1 := by
          unfold inertCount6
          simp only [h2n, ↓reduceIte]
          split_ifs <;> omega
        omega
      rw [hb1, hh1]; norm_num
  have hh0 : Nat.card (CommRing.Pic R) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hval; exact absurd hval (by norm_num)
  obtain ⟨hfinS, hle⟩ := hC k hk2 R hR hcop hh0
  have := Nat.card_le_card_of_injective F hFinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- `fibreComTrivialOwn_of` (TailC L1458) with `R5fpCountLe`. -/
theorem fibreComTrivialOwn_of_le (hA : ComIntOrQuadOrder) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe) : FibreComTrivialOwn :=
  fun _ _ _ _ _ _ hW u hu y P hP hv => nocm_on_witness_le hA hB hK hC hW u hu y P hP hv

/-- `fibreComTrivialFull_of` (TailC L1480) with `R5fpCountLe`. -/
theorem fibreComTrivialFull_of_le (hL : R1R2fpFull) (hM : MobiusGlue) (hA : ComIntOrQuadOrder)
    (hB : CMConductorCoprime6) (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe) :
    FibreComTrivialFull :=
  fibreComTrivialFull_of_own hL hM (fibreComTrivialOwn_of_le hA hB hK hC)

/-- `fibreComTrivialFull_of_leaves'` (TailC L2071) with `R5fpCountLe`. -/
theorem fibreComTrivialFull_of_leaves'_le (hL : R1R2fpFull) (hM : MobiusGlue)
    (hYu : QMLattice.YuB6Alg) (t6 : PkgI3.HomFreeFinite) (hB : CMConductorCoprime6)
    (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe) : FibreComTrivialFull :=
  fibreComTrivialFull_of_le hL hM (comIntOrQuadOrder_of_leaves hYu t6) hB hK hC

/-- `fibreComTrivialFull_of_leaves''` (TailC L2289) with `R5fpCountLe`. -/
theorem fibreComTrivialFull_of_leaves''_le (hL : R1R2fpFull) (hM : LeafQM.AV.Pin.MobiusGlue)
    (hYu : QMLattice.YuB6Alg) (t6 : PkgI3.HomFreeFinite) (hE : CMOptimalEmbedding)
    (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe) : FibreComTrivialFull :=
  fibreComTrivialFull_of_leaves'_le hL hM hYu t6 (cmConductorCoprime6_of hE) hK hC

end FS5NoCM

end HDec
