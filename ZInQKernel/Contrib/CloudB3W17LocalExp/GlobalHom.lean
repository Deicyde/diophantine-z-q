import ZInQKernel.Contrib.CloudB3W17LocalExp.Globalization

/-!
# A given global analytic homomorphism `E → G` makes `G` a complex torus

Terminal form of the uniformization assembly, for a **provided** global homomorphism. Nothing here
constructs the exponential: `Φ` is a hypothesis.

Given a compact connected commutative complex Lie group `G` charted on a finite-dimensional complex
normed space `E`, and a homomorphism `Φ : E → G` which is analytic and has an analytic local inverse at
`0` (`LocalInverseData`, supplied either by `IsLocalDiffeomorphAt` or by the inverse function theorem from
an invertible `HasMFDerivAt` at `0`), the theorem `torus_diffeo_of_globalHom` returns:

* `Φ` is surjective (open subgroup of a connected group);
* its kernel is a discrete full lattice `Λ` (`CloudB3W17Lattice.isZLattice_of_exp`);
* an analytic group isomorphism `e : Torus Λ ≃ₘ^ω G` with `e (proj Λ v) = Φ v`.

`LocalInverseData` asks only for an analytic local section at `1` and injectivity near `0` — strictly less
than a local diffeomorphism, and exactly what the inverse function theorem produces at a single point.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Metric

noncomputable section

namespace CloudB3W17LocalExp

open BPAnalytic CloudB3W17Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G] [LieGroup 𝓘(ℂ, E) ω G]
  {Φ : E → G}

/-- The local data at the identity: an analytic local section of `Φ` at `1`, and injectivity of `Φ`
near `0`. -/
structure LocalInverseData (Φ : E → G) : Prop where
  /-- an analytic local section at `1` -/
  hasSection : ∃ (T : Set G) (σ : G → E), IsOpen T ∧ (1 : G) ∈ T ∧ σ 1 = 0 ∧
    (∀ g ∈ T, Φ (σ g) = g) ∧ ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω σ T
  /-- `Φ` is injective near `0` -/
  injOn : ∃ U ∈ nhds (0 : E), Set.InjOn Φ U

/-- A local diffeomorphism at `0` supplies the local data (`r` arbitrary positive). -/
theorem localInverseData_of_isLocalDiffeomorphAt (hΦ1 : Φ 0 = 1)
    (hloc : IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω Φ 0) : LocalInverseData Φ := by
  obtain ⟨Ψ, h0, hEq⟩ := hloc
  have hΨ0 : Ψ (0 : E) = 1 := by rw [← hEq h0, hΦ1]
  refine ⟨⟨Ψ.target, Ψ.invFun, Ψ.open_target, ?_, ?_, ?_, Ψ.contMDiffOn_invFun⟩, ?_⟩
  · rw [← hΨ0]; exact Ψ.toPartialEquiv.map_source h0
  · rw [← hΨ0]; exact Ψ.toPartialEquiv.left_inv h0
  · intro g hg
    have h1 : Φ (Ψ.invFun g) = Ψ.toPartialEquiv (Ψ.invFun g) :=
      hEq (Ψ.toPartialEquiv.map_target hg)
    rw [h1]
    exact Ψ.toPartialEquiv.right_inv hg
  · refine ⟨Ψ.source, Ψ.open_source.mem_nhds h0, ?_⟩
    intro x hx y hy hxy
    rw [hEq hx, hEq hy] at hxy
    exact Ψ.toPartialEquiv.injOn hx hy hxy

section Data

variable (hhom : ∀ u v, Φ (u + v) = Φ u * Φ v) (hΦ1 : Φ 0 = 1) (hdata : LocalInverseData Φ)

include hhom hΦ1 hdata

/-- **Openness**: `Φ` is open at `1` because it has a continuous local section there, hence open
everywhere by translation. -/
theorem isOpenMap_of_localData : IsOpenMap Φ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ, E) ω
  obtain ⟨T, σ, hTopen, h1T, hσ1, hσ, hσsm⟩ := hdata.hasSection
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro g ⟨v₀, hv₀U, rfl⟩
  set N : Set G := T ∩ σ ⁻¹' ((fun w : E => v₀ + w) ⁻¹' U) with hN
  have hNopen : IsOpen N :=
    hσsm.continuousOn.isOpen_inter_preimage hTopen (hU.preimage (continuous_const.add continuous_id))
  have h1N : (1 : G) ∈ N := by
    refine ⟨h1T, ?_⟩
    show σ 1 ∈ (fun w : E => v₀ + w) ⁻¹' U
    rw [hσ1]
    simpa using hv₀U
  have hsub : (fun h : G => Φ v₀ * h) '' N ⊆ Φ '' U := by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨v₀ + σ h, hh.2, by rw [hhom, hσ h hh.1]⟩
  refine Filter.mem_of_superset ?_ hsub
  exact ((isOpenMap_mul_left (Φ v₀)) N hNopen).mem_nhds ⟨1, h1N, by simp⟩

/-- **Surjectivity**: the range is an open, hence closed, subgroup of a connected group. -/
theorem surjective_of_localData [ConnectedSpace G] : Function.Surjective Φ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ, E) ω
  obtain ⟨T, σ, hTopen, h1T, hσ1, hσ, hσsm⟩ := hdata.hasSection
  have hinv : ∀ v : E, Φ (-v) = (Φ v)⁻¹ := by
    intro v
    have h : Φ v * Φ (-v) = 1 := by rw [← hhom]; simpa using hΦ1
    exact (inv_eq_of_mul_eq_one_right h).symm
  let H : Subgroup G :=
    { carrier := Set.range Φ
      one_mem' := ⟨0, hΦ1⟩
      mul_mem' := by rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u + v, hhom u v⟩
      inv_mem' := by rintro a ⟨v, rfl⟩; exact ⟨-v, hinv v⟩ }
  have hnhds : (H : Set G) ∈ nhds (1 : G) := by
    refine Filter.mem_of_superset (hTopen.mem_nhds h1T) ?_
    intro g hg
    exact ⟨σ g, hσ g hg⟩
  have hopen : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hnhds
  have hcl : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  have huniv : (H : Set G) = Set.univ := IsClopen.eq_univ ⟨hcl, hopen⟩ ⟨1, H.one_mem⟩
  intro g
  have hg : g ∈ (H : Set G) := huniv ▸ Set.mem_univ g
  exact hg

end Data

/-- **Terminal theorem (conditional).** A provided analytic homomorphism `Φ : E → G` with an analytic
local inverse at `0`, into a compact connected commutative complex Lie group, is surjective, has a
discrete full lattice as kernel, and identifies `G` with the complex torus `E ⧸ ker Φ` analytically.

The exponential `Φ` is **not** constructed here. For `E = Fin g → ℂ` the conclusion gives
`UnifPrinted.MumfordComplexTorus` in the commutative case. -/
theorem torus_diffeo_of_globalHom [FiniteDimensional ℂ E] [CompactSpace G] [ConnectedSpace G]
    (hhom : ∀ u v, Φ (u + v) = Φ u * Φ v) (hΦ1 : Φ 0 = 1)
    (hsm : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω Φ) (hdata : LocalInverseData Φ) :
    Function.Surjective Φ ∧
      ∃ (Λ : Submodule ℤ E) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
        (∀ v : E, v ∈ Λ ↔ Φ v = 1) ∧
        ∃ e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ G,
          (∀ a b, e (a + b) = e a * e b) ∧ ∀ v : E, e (proj Λ v) = Φ v := by
  have htop : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ, E) ω
  have hopen : IsOpenMap Φ := isOpenMap_of_localData hhom hΦ1 hdata
  have hsurj : Function.Surjective Φ := surjective_of_localData hhom hΦ1 hdata
  obtain ⟨T, σ, hTopen, h1T, hσ1, hσ, hσsm⟩ := hdata.hasSection
  obtain ⟨U, hUnhds, hUinj⟩ := hdata.injOn
  refine ⟨hsurj, ?_⟩
  -- `Φ` as an additive homomorphism into `Additive G`
  let π : E →+ Additive G :=
    { toFun := fun v => Additive.ofMul (Φ v)
      map_zero' := congrArg Additive.ofMul hΦ1
      map_add' := fun u v => congrArg Additive.ofMul (hhom u v) }
  set Λ : Submodule ℤ E := AddSubgroup.toIntSubmodule π.ker with hΛdef
  have hker : ∀ x : E, π x = 0 ↔ x ∈ Λ := by
    intro x
    rw [hΛdef]
    exact AddMonoidHom.mem_ker.symm
  have hmemΛ : ∀ v : E, v ∈ Λ ↔ Φ v = 1 := fun v => (hker v).symm
  have hπcont : Continuous (π : E → Additive G) := by
    have h := hsm.continuous
    exact h
  have hπopen : IsOpenMap (π : E → Additive G) := by
    have h := hopen
    exact h
  have hπsurj : Function.Surjective (π : E → Additive G) := by
    have h := hsurj
    exact h
  have hπinj : Set.InjOn (π : E → Additive G) U := by
    have h := hUinj
    exact h
  have hcompact : CompactSpace (Additive G) := inferInstanceAs (CompactSpace G)
  obtain ⟨hd, hZ, -⟩ := isZLattice_of_exp Λ π hker hπcont hπopen hπsurj hUnhds hπinj
  -- the induced analytic isomorphism
  have hFbij : Function.Bijective (fun q : Torus Λ => Additive.toMul (liftKer Λ π hker q)) := by
    refine ⟨fun a b hab => liftKer_injective Λ π hker hab, fun g => ?_⟩
    obtain ⟨q, hq⟩ := liftKer_surjective Λ π hker hπsurj (Additive.ofMul g)
    exact ⟨q, congrArg Additive.toMul hq⟩
  have hFsm : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
      (fun q : Torus Λ => Additive.toMul (liftKer Λ π hker q)) := by
    refine contMDiff_of_comp_proj Λ ?_
    have hcomp : ((fun q : Torus Λ => Additive.toMul (liftKer Λ π hker q)) ∘ proj Λ) = Φ := rfl
    rw [hcomp]
    exact hsm
  have hFinvsm : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (Equiv.ofBijective _ hFbij).symm := by
    intro g₀
    obtain ⟨v₀, rfl⟩ := hsurj g₀
    have hWopen : IsOpen ((fun g : G => (Φ v₀)⁻¹ * g) ⁻¹' T) :=
      hTopen.preimage (continuous_const.mul continuous_id)
    have hmemW : Φ v₀ ∈ (fun g : G => (Φ v₀)⁻¹ * g) ⁻¹' T := by simpa using h1T
    have hform : ∀ g ∈ (fun g : G => (Φ v₀)⁻¹ * g) ⁻¹' T,
        (Equiv.ofBijective _ hFbij).symm g = proj Λ (v₀ + σ ((Φ v₀)⁻¹ * g)) := by
      intro g hg
      refine (Equiv.symm_apply_eq _).mpr ?_
      show g = Φ (v₀ + σ ((Φ v₀)⁻¹ * g))
      rw [hhom, hσ _ hg, mul_inv_cancel_left]
    have m1 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun g : G => (Φ v₀)⁻¹ * g) (Φ v₀) :=
      contMDiff_mul_left.contMDiffAt
    have m2 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω σ ((Φ v₀)⁻¹ * Φ v₀) := by
      rw [inv_mul_cancel]
      exact hσsm.contMDiffAt (hTopen.mem_nhds h1T)
    have m3 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun w : E => v₀ + w) (σ ((Φ v₀)⁻¹ * Φ v₀)) :=
      (contMDiff_iff_contDiff.mpr (contDiff_const.add contDiff_id)).contMDiffAt
    have m4 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (proj Λ) (v₀ + σ ((Φ v₀)⁻¹ * Φ v₀)) :=
      (contMDiff_proj Λ).contMDiffAt
    have hsmloc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω
        (fun g : G => proj Λ (v₀ + σ ((Φ v₀)⁻¹ * g))) (Φ v₀) := by
      have := m4.comp (Φ v₀) (m3.comp (Φ v₀) (m2.comp (Φ v₀) m1))
      simpa [Function.comp_def] using this
    refine hsmloc.congr_of_eventuallyEq ?_
    filter_upwards [hWopen.mem_nhds hmemW] with g hg
    exact hform g hg
  refine ⟨Λ, hd, hZ, hmemΛ, ⟨Equiv.ofBijective _ hFbij, hFsm, hFinvsm⟩, ?_, fun v => rfl⟩
  intro a b
  show Additive.toMul (liftKer Λ π hker (a + b))
      = Additive.toMul (liftKer Λ π hker a) * Additive.toMul (liftKer Λ π hker b)
  rw [map_add]
  rfl

end CloudB3W17LocalExp
