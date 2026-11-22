import ZInQKernel.Contrib.CloudB3W17GAGA.Descent
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

/-!
# Arbitrary strong uniformizations in genuine regular complex-point models

All model inputs below are UNBUNDLED facts about the existing complex points,
regular evaluations, and Mathlib complex manifolds. No analytification/GAGA
leaf or new hypothesis structure is invented. The arbitrary analytic input
has only `DifferentiableOn` regular evaluations; it is treated as
`MDifferentiable`, not upgraded by a multivariable analyticity assumption.

The accepted Descent/Graph supplier at 6472606 is imported without modification.
-/

open scoped Manifold ContDiff Topology CommRingCat.HomTopology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cDom cEvalAt)
open ZInQ.HomLattice (IsAnalyticHom IsStrongUnif)
open BPAnalytic (Torus proj)

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17GAGA

/-- The existing complex points over the identity embedding. -/
abbrev APts (A : AbVar ℂ) : Type := CPts A (RingHom.id ℂ)

/-- The complex points in a genuine Zariski open of A. -/
def pointDom (A : AbVar ℂ) (U : A.X.left.Opens) : Set (APts A) :=
  {P | ⊤ ≤ P.left ⁻¹ᵁ U}

section PointTopology

variable (A : AbVar ℂ) [TopologicalSpace (APts A)]
variable (hNH : ∀ (P₀ : APts A) (N : Set (APts A)), N ∈ 𝓝 P₀ →
  ∃ (U : A.X.left.Opens) (k : ℕ) (s : Fin k → Γ(A.X.left, U)) (ε : ℝ),
    0 < ε ∧ P₀ ∈ pointDom A U ∧ ∀ P : APts A, P ∈ pointDom A U →
      (∀ i, ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε) → P ∈ N)

include hNH

/-- A finite regular-evaluation neighbourhood basis detects continuity.
This uses the supplied genuine point-model topology; it defines no new topology. -/
theorem continuous_of_regular_pullbacks {X : Type*} [TopologicalSpace X] (f : X → APts A)
    (hopen : ∀ U : A.X.left.Opens, IsOpen (f ⁻¹' pointDom A U))
    (heval : ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)),
      ContinuousOn (fun x => cEvalAt (f x) U s) (f ⁻¹' pointDom A U)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  obtain ⟨U, k, s, ε, hε, hU, hsep⟩ := hNH (f x₀) N hN
  have hdom : ∀ᶠ x in 𝓝 x₀, f x ∈ pointDom A U := (hopen U).mem_nhds hU
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ i,
      ‖cEvalAt (f x) U (s i) - cEvalAt (f x₀) U (s i)‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun x => cEvalAt (f x) U (s i)) x₀ :=
      (heval U (s i)).continuousAt ((hopen U).mem_nhds hU)
    simpa only [Metric.mem_ball, dist_eq_norm] using hc.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hdom, hall] with x hx hxi
  exact hsep (f x) hx hxi

/-- The exact repository `IsAnalyticHom` input is continuous for a regular point model. -/
theorem continuous_analyticHom {g : ℕ} {ψ : (Fin g → ℂ) → APts A}
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) : Continuous ψ := by
  exact continuous_of_regular_pullbacks A hNH ψ (fun U => hψ.2.1 U)
    (fun U s => (hψ.2.2 U s).continuousOn)

end PointTopology

section RegularDetection

variable (A : AbVar ℂ) (n : ℕ) [TopologicalSpace (APts A)]
variable [ChartedSpace (Fin n → ℂ) (APts A)] [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)]
variable (hcoords : ∀ P : APts A, ∃ (U : A.X.left.Opens) (s : Fin n → Γ(A.X.left, U)),
  P ∈ pointDom A U ∧ IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
    (fun Q i => cEvalAt Q U (s i)) P)

include hcoords

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] in
/-- Genuine regular coordinates detect manifold differentiability of an arbitrary map. -/
theorem mdifferentiableAt_of_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    (f : M → APts A) (x : M) (hcont : ContinuousAt f x)
    (hreg : ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)), f x ∈ pointDom A U →
      MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun y => cEvalAt (f y) U s) x) :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) f x := by
  obtain ⟨U, s, hU, hloc⟩ := hcoords (f x)
  let c : APts A → (Fin n → ℂ) := fun Q i => cEvalAt Q U (s i)
  have hvec : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) (fun y => c (f y)) x := by
    apply mdifferentiableAt_pi_space.mpr
    intro i
    exact hreg U (s i) hU
  have hinv : MDifferentiableAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ)
      hloc.localInverse (c (f x)) := hloc.mdifferentiableAt_localInverse (by simp)
  have heq : f =ᶠ[𝓝 x] (fun y => hloc.localInverse (c (f y))) := by
    have hev := hloc.localInverse_eventuallyEq_left.comp_tendsto hcont
    filter_upwards [hev] with y hy
    exact hy.symm
  exact (hinv.comp x hvec).congr_of_eventuallyEq heq

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] in
/-- The analytic-strength version, used only when pullbacks already have Cω regularity. -/
theorem contMDiffAt_of_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    (f : M → APts A) (x : M) (hcont : ContinuousAt f x)
    (hreg : ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)), f x ∈ pointDom A U →
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun y => cEvalAt (f y) U s) x) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ω f x := by
  obtain ⟨U, s, hU, hloc⟩ := hcoords (f x)
  let c : APts A → (Fin n → ℂ) := fun Q i => cEvalAt Q U (s i)
  have hvec : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ω (fun y => c (f y)) x := by
    apply contMDiffAt_pi_module_iff.mpr
    intro i
    exact hreg U (s i) hU
  have heq : f =ᶠ[𝓝 x] (fun y => hloc.localInverse (c (f y))) := by
    have hev := hloc.localInverse_eventuallyEq_left.comp_tendsto hcont
    filter_upwards [hev] with y hy
    exact hy.symm
  exact (hloc.contMDiffAt_localInverse.comp x hvec).congr_of_eventuallyEq heq

variable (hNH : ∀ (P₀ : APts A) (N : Set (APts A)), N ∈ 𝓝 P₀ →
  ∃ (U : A.X.left.Opens) (k : ℕ) (s : Fin k → Γ(A.X.left, U)) (ε : ℝ),
    0 < ε ∧ P₀ ∈ pointDom A U ∧ ∀ P : APts A, P ∈ pointDom A U →
      (∀ i, ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε) → P ∈ N)

include hNH

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] in
/-- An arbitrary `IsAnalyticHom` is holomorphic in the supplied genuine regular model.
Only its stated `DifferentiableOn` hypotheses are used. -/
theorem mdifferentiable_analyticHom {g : ℕ} {ψ : (Fin g → ℂ) → APts A}
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) :
    MDifferentiable 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin n → ℂ) ψ := by
  intro z
  apply mdifferentiableAt_of_regular A n hcoords ψ z
    ((continuous_analyticHom A hNH hψ).continuousAt)
  intro U s hz
  exact ((hψ.2.2 U s).differentiableAt ((hψ.2.1 U).mem_nhds hz)).mdifferentiableAt

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] in
/-- The immutable quotient descent is holomorphic into the regular point model,
without a uniformization of its target. Its regular-evaluation result is reused. -/
theorem mdifferentiable_quotientDescent {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    [DiscreteTopology Λ] {ψ : (Fin g → ℂ) → APts A}
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    MDifferentiable 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin n → ℂ)
      (fun q => Additive.toMul (descendHom hψ hΛ q)) := by
  let f : Torus Λ → APts A := fun q => Additive.toMul (descendHom hψ hΛ q)
  have hc : Continuous f := by
    apply (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff.mpr
    change Continuous ψ
    exact continuous_analyticHom A hNH hψ
  intro q
  apply mdifferentiableAt_of_regular A n hcoords f q hc.continuousAt
  intro U s hq
  have ho := isOpen_torusDom_descendHom hψ hΛ U
  have hd := mdifferentiableOn_torusEval_descendHom hψ hΛ U s
  exact hd.mdifferentiableAt (ho.mem_nhds hq)

end RegularDetection

section StrongMaps

variable {A : AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}

/-- The underlying point map of the given arbitrary group presentation. -/
def phiPts (φ : Torus Λ ≃+ Additive (APts A)) (q : Torus Λ) : APts A :=
  Additive.toMul (φ q)

/-- The actual inverse of that presentation, not a separately chosen uniformization. -/
def phiInv (φ : Torus Λ ≃+ Additive (APts A)) (P : APts A) : Torus Λ :=
  φ.symm (Additive.ofMul P)

@[simp]
theorem phiPts_phiInv (φ : Torus Λ ≃+ Additive (APts A)) (P : APts A) :
    phiPts φ (phiInv φ P) = P := by
  change Additive.toMul (φ (φ.symm (Additive.ofMul P))) = P
  rw [AddEquiv.apply_symm_apply]
  rfl

@[simp]
theorem phiInv_phiPts (φ : Torus Λ ≃+ Additive (APts A)) (q : Torus Λ) :
    phiInv φ (phiPts φ q) = q := by
  change φ.symm (φ q) = q
  exact φ.symm_apply_apply q

variable [DiscreteTopology Λ]

/-- Existing weak/strong glue turns the given presentation into the exact analytic input. -/
theorem isAnalyticHom_strongPhi (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) :
    IsAnalyticHom (RingHom.id ℂ) (fun v => phiPts φ (proj Λ v)) :=
  ZInQ.HomLattice.isAnalyticHom_of_unif
    (ZInQ.LeafPush2.isUniformization_of_bp A (ZInQ.HomLattice.bp_of_isStrongUnif hφ))

end StrongMaps

section StrongTopology

variable (A : AbVar ℂ) [TopologicalSpace (APts A)] {g : ℕ}
variable {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
variable (hopen : ∀ U : A.X.left.Opens, IsOpen (pointDom A U))
variable (heval : ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)),
  ContinuousOn (fun P : APts A => cEvalAt P U s) (pointDom A U))
variable (hNH : ∀ (P₀ : APts A) (N : Set (APts A)), N ∈ 𝓝 P₀ →
  ∃ (U : A.X.left.Opens) (k : ℕ) (s : Fin k → Γ(A.X.left, U)) (ε : ℝ),
    0 < ε ∧ P₀ ∈ pointDom A U ∧ ∀ P : APts A, P ∈ pointDom A U →
      (∀ i, ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε) → P ∈ N)

include hNH

/-- Forward continuity is detected by the supplied regular-function neighbourhood basis. -/
theorem continuous_phiPts (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) : Continuous (phiPts φ) := by
  apply (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff.mpr
  exact continuous_analyticHom A hNH (isAnalyticHom_strongPhi φ hφ)

omit hNH
include hopen heval

omit [DiscreteTopology Λ] in
/-- The strong `open_map` clause gives inverse continuity in an actual regular point model. -/
theorem continuous_phiInv (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) : Continuous (phiInv φ) := by
  rw [continuous_iff_continuousAt]
  intro P₀
  let q₀ := phiInv φ P₀
  let v₀ : Fin g → ℂ := q₀.out
  have hq₀ : proj Λ v₀ = q₀ := QuotientAddGroup.out_eq' q₀
  have hp₀ : Additive.toMul (φ (proj Λ v₀)) = P₀ := by
    change phiPts φ (proj Λ v₀) = P₀
    rw [hq₀]
    exact phiPts_phiInv φ P₀
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  have hN' : N ∈ 𝓝 (proj Λ v₀) := by rw [hq₀]; exact hN
  obtain ⟨U, k, s, ε, hε, hU, hsep⟩ := hφ.open_map v₀ N hN'
  rw [hp₀] at hU hsep
  have hdom : ∀ᶠ P in 𝓝 P₀, P ∈ pointDom A U := (hopen U).mem_nhds hU
  have hall : ∀ᶠ P in 𝓝 P₀, ∀ i,
      ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun P : APts A => cEvalAt P U (s i)) P₀ :=
      (heval U (s i)).continuousAt ((hopen U).mem_nhds hU)
    simpa only [Metric.mem_ball, dist_eq_norm] using hc.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hdom, hall] with P hP hPi
  obtain ⟨q, hqN, hqP⟩ := hsep P hP hPi
  have hq : phiInv φ P = q := by
    apply φ.injective
    change φ (φ.symm (Additive.ofMul P)) = φ q
    rw [AddEquiv.apply_symm_apply]
    exact Additive.toMul.injective hqP.symm
  show phiInv φ P ∈ N
  rw [hq]
  exact hqN

include hNH

/-- The given arbitrary strong presentation is a homeomorphism to the regular point model. -/
def strongUnifHomeomorph (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) : Torus Λ ≃ₜ APts A where
  toFun := phiPts φ
  invFun := phiInv φ
  left_inv := phiInv_phiPts φ
  right_inv := phiPts_phiInv φ
  continuous_toFun := continuous_phiPts A hNH φ hφ
  continuous_invFun := continuous_phiInv A hopen heval φ hφ

@[simp]
theorem strongUnifHomeomorph_apply (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) (q : Torus Λ) :
    strongUnifHomeomorph A hopen heval hNH φ hφ q = phiPts φ q := rfl

@[simp]
theorem strongUnifHomeomorph_symm_apply (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) (P : APts A) :
    (strongUnifHomeomorph A hopen heval hNH φ hφ).symm P = phiInv φ P := rfl

end StrongTopology

section StrongAnalytic

variable (A : AbVar ℂ) (n : ℕ) [TopologicalSpace (APts A)]
variable [ChartedSpace (Fin n → ℂ) (APts A)] [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)]
variable {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
variable (hopen : ∀ U : A.X.left.Opens, IsOpen (pointDom A U))
variable (hholo : ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)),
  ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω
    (fun P : APts A => cEvalAt P U s) (pointDom A U))
variable (hNH : ∀ (P₀ : APts A) (N : Set (APts A)), N ∈ 𝓝 P₀ →
  ∃ (U : A.X.left.Opens) (k : ℕ) (s : Fin k → Γ(A.X.left, U)) (ε : ℝ),
    0 < ε ∧ P₀ ∈ pointDom A U ∧ ∀ P : APts A, P ∈ pointDom A U →
      (∀ i, ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε) → P ∈ N)
variable (hcoords : ∀ P : APts A, ∃ (U : A.X.left.Opens) (s : Fin n → Γ(A.X.left, U)),
  P ∈ pointDom A U ∧ IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
    (fun Q i => cEvalAt Q U (s i)) P)

include hNH hcoords

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] in
/-- The given presentation is Cω in the regular model, using its own analytic Γ pullbacks. -/
theorem contMDiff_phiPts (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) :
    ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (phiPts φ) := by
  apply BPAnalytic.contMDiff_of_comp_proj Λ
  have hc : Continuous (fun v : Fin g → ℂ => phiPts φ (proj Λ v)) :=
    (continuous_phiPts A hNH φ hφ).comp (BPAnalytic.isLocalHomeomorph_proj Λ).continuous
  intro v
  apply contMDiffAt_of_regular A n hcoords (fun v => phiPts φ (proj Λ v)) v hc.continuousAt
  intro U s hv
  exact ((hφ.holo U s).2 v hv).contDiffAt.contMDiffAt

omit hNH hcoords
include hopen hholo

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] in
/-- Cω inverse for the original arbitrary φ. The inverse-function theorem is applied to
its g regular coordinates on ℂ^g; no equality between g and the model dimension n is used. -/
theorem contMDiff_phiInv (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω (phiInv φ) := by
  have hc : Continuous (phiInv φ) :=
    continuous_phiInv A hopen (fun U s => (hholo U s).continuousOn) φ hφ
  intro P₀
  let q₀ := phiInv φ P₀
  let v₀ : Fin g → ℂ := q₀.out
  have hq₀ : proj Λ v₀ = q₀ := QuotientAddGroup.out_eq' q₀
  have hp₀ : phiPts φ (proj Λ v₀) = P₀ := by
    rw [hq₀]
    exact phiPts_phiInv φ P₀
  obtain ⟨U, s, e, hU, hder⟩ := hφ.coords v₀
  let F : (Fin g → ℂ) → (Fin g → ℂ) := fun v i => cEvalAt (phiPts φ (proj Λ v)) U (s i)
  let G : APts A → (Fin g → ℂ) := fun P i => cEvalAt P U (s i)
  have hFP : F v₀ = G P₀ := by
    change G (phiPts φ (proj Λ v₀)) = G P₀
    rw [hp₀]
  have hUP : P₀ ∈ pointDom A U := by
    have hU' : phiPts φ (proj Λ v₀) ∈ pointDom A U := hU
    rwa [hp₀] at hU'
  have hF : HasFDerivAt F (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀ := hder
  have hFan : AnalyticAt ℂ F v₀ :=
    AnalyticAt.pi fun i => (hφ.holo U (s i)).2 v₀ hU
  have hstrict : HasStrictFDerivAt F (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀ := by
    have h := hFan.hasStrictFDerivAt
    rwa [hF.fderiv] at h
  let p := hstrict.toOpenPartialHomeomorph F
  have hp : p.symm (F v₀) = v₀ := hstrict.localInverse_apply_image
  have hpd : HasFDerivAt p (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (p.symm (F v₀)) := by
    change HasFDerivAt F (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (p.symm (F v₀))
    rw [hp]
    exact hF
  have hpc : ContDiffAt ℂ ω p (p.symm (F v₀)) := by
    change ContDiffAt ℂ ω F (p.symm (F v₀))
    rw [hp]
    exact hFan.contDiffAt
  have hpinv : ContDiffAt ℂ ω p.symm (F v₀) :=
    p.contDiffAt_symm hstrict.image_mem_toOpenPartialHomeomorph_target hpd hpc
  have hGi : ContMDiffAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω p.symm (G P₀) := by
    rw [← hFP]
    exact hpinv.contMDiffAt
  have hG : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω G P₀ := by
    apply contMDiffAt_pi_module_iff.mpr
    intro i
    exact (hholo U (s i) P₀ hUP).contMDiffAt ((hopen U).mem_nhds hUP)
  have hexpr : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
      (fun P => proj Λ (p.symm (G P))) P₀ :=
    ((BPAnalytic.contMDiff_proj Λ) (p.symm (G P₀))).comp P₀ (hGi.comp P₀ hG)
  let c := BPAnalytic.chartOf Λ v₀
  have hqsrc : q₀ ∈ c.source := by
    rw [← hq₀]
    exact BPAnalytic.proj_mem_chartOf_source Λ v₀
  have hcv : c q₀ = v₀ := by
    rw [← hq₀]
    simpa only [c, BPAnalytic.chartOf_symm_apply] using
      c.right_inv (BPAnalytic.self_mem_chartOf_target Λ v₀)
  let W : APts A → (Fin g → ℂ) := fun P => c (phiInv φ P)
  have hcW : ContinuousAt W P₀ := (c.continuousAt hqsrc).comp hc.continuousAt
  have hW₀ : W P₀ = v₀ := hcv
  have hW : Tendsto W (𝓝 P₀) (𝓝 v₀) := by
    have h := hcW.tendsto
    rwa [hW₀] at h
  have hsrc : ∀ᶠ P in 𝓝 P₀, phiInv φ P ∈ c.source :=
    (hc.tendsto P₀).eventually (c.open_source.mem_nhds hqsrc)
  have hleft : ∀ᶠ P in 𝓝 P₀, p.symm (F (W P)) = W P :=
    hW.eventually hstrict.eventually_left_inverse
  have heq : phiInv φ =ᶠ[𝓝 P₀] (fun P => proj Λ (p.symm (G P))) := by
    filter_upwards [hsrc, hleft] with P hP hLP
    have hproj : proj Λ (W P) = phiInv φ P := BPAnalytic.proj_chartOf Λ hP
    have hFG : F (W P) = G P := by
      change G (phiPts φ (proj Λ (W P))) = G P
      rw [hproj, phiPts_phiInv]
    rw [hFG] at hLP
    calc
      phiInv φ P = proj Λ (W P) := hproj.symm
      _ = proj Λ (p.symm (G P)) := congrArg (proj Λ) hLP.symm
  exact hexpr.congr_of_eventuallyEq heq

include hNH hcoords

/-- A genuine biholomorphism to the regular model, preserving the original arbitrary φ. -/
def strongUnifDiffeomorph (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) :
    Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ), 𝓘(ℂ, Fin n → ℂ)⟯ APts A where
  toEquiv := (strongUnifHomeomorph A hopen (fun U s => (hholo U s).continuousOn) hNH φ hφ).toEquiv
  contMDiff_toFun := contMDiff_phiPts A n hNH hcoords φ hφ
  contMDiff_invFun := contMDiff_phiInv A n hopen hholo φ hφ

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] in
/-- The desired arbitrary-source analytic identification, with both function identities explicit.
No full-lattice, g=n, B-uniformization, H103 or GAGA premise is added. -/
theorem strongUnif_diffeomorph (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ) :
    ∃ e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ), 𝓘(ℂ, Fin n → ℂ)⟯ APts A,
      (∀ q, e q = phiPts φ q) ∧ (∀ P, e.symm P = phiInv φ P) :=
  ⟨strongUnifDiffeomorph A n hopen hholo hNH hcoords φ hφ, fun _ => rfl, fun _ => rfl⟩

end StrongAnalytic

section PointHom

variable {A B : AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
variable {ψ : (Fin g → ℂ) → APts B}

/-- The quotient descent transported through the original given group presentation of A. -/
def pointDescentHom (φ : Torus Λ ≃+ Additive (APts A))
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) : APts A →* APts B where
  toFun P := Additive.toMul (descendHom hψ hΛ (phiInv φ P))
  map_one' := by
    change descendHom hψ hΛ (φ.symm 0) = 0
    rw [map_zero, map_zero]
  map_mul' P Q := by
    change descendHom hψ hΛ (φ.symm (Additive.ofMul P + Additive.ofMul Q)) =
      descendHom hψ hΛ (φ.symm (Additive.ofMul P)) +
        descendHom hψ hΛ (φ.symm (Additive.ofMul Q))
    rw [map_add, map_add]

@[simp]
theorem pointDescentHom_spec (φ : Torus Λ ≃+ Additive (APts A))
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) (z : Fin g → ℂ) :
    pointDescentHom φ hψ hΛ (phiPts φ (proj Λ z)) = ψ z := by
  change Additive.toMul (descendHom hψ hΛ (phiInv φ (phiPts φ (proj Λ z)))) = ψ z
  rw [phiInv_phiPts, descendHom_proj]
  rfl

/-- The given φ is onto, so the point-level descent is unique without any algebraic input. -/
theorem pointDescentHom_unique (φ : Torus Λ ≃+ Additive (APts A))
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1)
    (F : APts A →* APts B) (hF : ∀ z, F (phiPts φ (proj Λ z)) = ψ z) :
    F = pointDescentHom φ hψ hΛ := by
  apply MonoidHom.ext
  intro P
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (phiInv φ P)
  change proj Λ z = phiInv φ P at hz
  have hp : phiPts φ (proj Λ z) = P := by
    rw [hz]
    exact phiPts_phiInv φ P
  calc
    F P = F (phiPts φ (proj Λ z)) := congrArg F hp.symm
    _ = ψ z := hF z
    _ = pointDescentHom φ hψ hΛ P := by
      rw [← hp]
      exact (pointDescentHom_spec φ hψ hΛ z).symm

end PointHom

section PointDescent

variable (A B : AbVar ℂ) (n m : ℕ) [TopologicalSpace (APts A)] [TopologicalSpace (APts B)]
variable [ChartedSpace (Fin n → ℂ) (APts A)] [ChartedSpace (Fin m → ℂ) (APts B)]
variable [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω (APts B)]
variable {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
variable {ψ : (Fin g → ℂ) → APts B}
variable (hopenA : ∀ U : A.X.left.Opens, IsOpen (pointDom A U))
variable (hholoA : ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)),
  ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω
    (fun P : APts A => cEvalAt P U s) (pointDom A U))
variable (hNHA : ∀ (P₀ : APts A) (N : Set (APts A)), N ∈ 𝓝 P₀ →
  ∃ (U : A.X.left.Opens) (k : ℕ) (s : Fin k → Γ(A.X.left, U)) (ε : ℝ),
    0 < ε ∧ P₀ ∈ pointDom A U ∧ ∀ P : APts A, P ∈ pointDom A U →
      (∀ i, ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε) → P ∈ N)
variable (hcoordsA : ∀ P : APts A, ∃ (U : A.X.left.Opens) (s : Fin n → Γ(A.X.left, U)),
  P ∈ pointDom A U ∧ IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
    (fun Q i => cEvalAt Q U (s i)) P)
variable (hNHB : ∀ (P₀ : APts B) (N : Set (APts B)), N ∈ 𝓝 P₀ →
  ∃ (U : B.X.left.Opens) (k : ℕ) (s : Fin k → Γ(B.X.left, U)) (ε : ℝ),
    0 < ε ∧ P₀ ∈ pointDom B U ∧ ∀ P : APts B, P ∈ pointDom B U →
      (∀ i, ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε) → P ∈ N)
variable (hcoordsB : ∀ P : APts B, ∃ (U : B.X.left.Opens) (s : Fin m → Γ(B.X.left, U)),
  P ∈ pointDom B U ∧ IsLocalDiffeomorphAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
    (fun Q i => cEvalAt Q U (s i)) P)

include hopenA hholoA hNHA hcoordsA hNHB hcoordsB

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω (APts B)] in
/-- The original ψ descends to a holomorphic group map on the actual regular point models.
A strong target uniformization and a multivariable Cω upgrade of ψ are not used. -/
theorem mdifferentiable_pointDescentHom (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ)
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) (pointDescentHom φ hψ hΛ) := by
  let e := strongUnifDiffeomorph A n hopenA hholoA hNHA hcoordsA φ hφ
  have hinv : MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) e.symm :=
    fun P => (e.contMDiff_invFun P).mdifferentiableAt (by simp)
  have h := (mdifferentiable_quotientDescent B m hcoordsB hNHB hψ hΛ).comp hinv
  exact h

omit [IsManifold 𝓘(ℂ, Fin n → ℂ) ω (APts A)] [IsManifold 𝓘(ℂ, Fin m → ℂ) ω (APts B)] in
/-- Unique holomorphic point-level descent for the original arbitrary g, Λ and φA.
All regular-model premises are unbundled genuine Γ-evaluation facts. This is not GAGA. -/
theorem existsUnique_holomorphic_descent (φ : Torus Λ ≃+ Additive (APts A))
    (hφ : IsStrongUnif A (RingHom.id ℂ) Λ φ)
    (hψ : IsAnalyticHom (RingHom.id ℂ) ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ∃! F : APts A →* APts B,
      MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) F ∧
        ∀ z, F (phiPts φ (proj Λ z)) = ψ z := by
  refine ⟨pointDescentHom φ hψ hΛ, ⟨?_, pointDescentHom_spec φ hψ hΛ⟩, ?_⟩
  · exact mdifferentiable_pointDescentHom A B n m hopenA hholoA hNHA hcoordsA hNHB hcoordsB
      φ hφ hψ hΛ
  · intro F hF
    exact pointDescentHom_unique φ hψ hΛ F hF.2

end PointDescent

/-! ## Facts from the actual committed canonical point/manifold model

These use CloudB3W17Hodge's native point topology and its chosen algebraic étale charts.
They introduce neither a second topology nor a printed-model hypothesis structure.
-/

/-- A finite Γ-evaluation neighbourhood in the existing canonical analytic topology. -/
theorem canonicalPoint_neighbourhood
    (X : Over (Spec (CommRingCat.of ℂ))) (P₀ : ComplexPoint X)
    (N : Set (ComplexPoint X)) (hN : N ∈ 𝓝 P₀) :
    ∃ (U : X.left.Opens) (k : ℕ) (s : Fin k → Γ(X.left, U)) (ε : ℝ),
      0 < ε ∧ P₀ ∈ Point.overOpen U ∧
      ∀ P : ComplexPoint X, P ∈ Point.overOpen U →
        (∀ i, ‖Point.evaluate U (s i) P - Point.evaluate U (s i) P₀‖ < ε) → P ∈ N := by
  obtain ⟨O, hON, hO, hP₀O⟩ := mem_nhds_iff.mp hN
  obtain ⟨U, hU, hP₀U, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := P₀.underlying) (U := ⊤) trivial
  have hOU : @IsOpen (Point.OverOpen (X := X) U) (Point.chartTopology U)
      (Subtype.val ⁻¹' O) := by
    have h := (isOpen_iSup_iff.mp hO) (⟨U, hU⟩ : X.left.affineOpens)
    exact h
  obtain ⟨H, hH, hHO⟩ := isOpen_induced_iff.mp hOU
  obtain ⟨H', hH', rfl⟩ :=
    (CommRingCat.HomTopology.isEmbedding_hom (CommRingCat.of ℂ) Γ(X.left, U)).isInducing.isOpen_iff.mp hH
  have hP₀H : ⇑(Point.evaluationHom U ⟨P₀, hP₀U⟩).hom ∈ H' := by
    have hm : (⟨P₀, hP₀U⟩ : Point.OverOpen (X := X) U) ∈ Subtype.val ⁻¹' O := hP₀O
    rwa [← hHO] at hm
  obtain ⟨I, u, hu, hIH⟩ := isOpen_pi_iff.mp hH' _ hP₀H
  let V : Set (I → ℂ) := ⋂ t : I, {v | v t ∈ u t.1}
  let v₀ : I → ℂ := fun t => Point.evaluate U t.1 P₀
  have hV : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro t
    exact (hu t.1 t.2).1.preimage (continuous_apply t)
  have hv₀ : v₀ ∈ V := by
    apply Set.mem_iInter.mpr
    intro t
    change Point.evaluate U t.1 P₀ ∈ u t.1
    have ht := (hu t.1 t.2).2
    change Point.evaluationHom U ⟨P₀, hP₀U⟩ t.1 ∈ u t.1 at ht
    rwa [Point.evaluationHom_apply] at ht
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hv₀)
  let k := Fintype.card I
  let e : I ≃ Fin k := Fintype.equivFin I
  let s : Fin k → Γ(X.left, U) := fun i => (e.symm i).1
  refine ⟨U, k, s, ε, hε, hP₀U, ?_⟩
  intro P hPU hPs
  have hPB : (fun t : I => Point.evaluate U t.1 P) ∈ Metric.ball v₀ ε := by
    apply (dist_pi_lt_iff hε).mpr
    intro t
    simpa only [s, Equiv.symm_apply_apply, v₀, dist_eq_norm] using hPs (e t)
  have hPH : ⇑(Point.evaluationHom U ⟨P, hPU⟩).hom ∈ H' := by
    apply hIH
    intro t ht
    have hm := Set.mem_iInter.mp (hball hPB) (⟨t, ht⟩ : I)
    change Point.evaluate U t P ∈ u t at hm
    change Point.evaluationHom U ⟨P, hPU⟩ t ∈ u t
    rw [Point.evaluationHom_apply]
    exact hm
  have hm : (⟨P, hPU⟩ : Point.OverOpen (X := X) U) ∈ Subtype.val ⁻¹' O := by
    rw [← hHO]
    exact hPH
  exact hON hm

/-- The committed canonical smooth model makes every genuine Γ-evaluation Cω on its open. -/
theorem canonicalPoint_holo (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (U : X.left.Opens) (s : Γ(X.left, U)) :
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (Point.evaluate U s)
      (Point.overOpen U : Set (ComplexPoint X)) := by
  intro P hP
  let c := ComplexPoint.localChart X n P
  have hsrc : P ∈ c.source := ComplexPoint.mem_localChart_source X n P
  have hc : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω c P :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hsrc)
  have hPU : c.symm (c P) ∈ (Point.overOpen U : Set (ComplexPoint X)) := by
    rw [c.left_inv hsrc]
    exact hP
  have hfun : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω
      (fun v => Point.evaluate U s (c.symm v)) (c P) :=
    (ComplexPoint.analyticAt_localChart_symm_evaluate X n P
      (c.map_source hsrc) U s hPU).contDiffAt.contMDiffAt
  have heq : Point.evaluate U s =ᶠ[𝓝 P]
      (fun Q => Point.evaluate U s (c.symm (c Q))) := by
    filter_upwards [c.open_source.mem_nhds hsrc] with Q hQ
    exact congrArg (Point.evaluate U s) (c.left_inv hQ).symm
  exact ((hfun.comp P hc).congr_of_eventuallyEq heq).contMDiffWithinAt

/-- Canonical algebraic étale coordinates are genuine Γ-evaluation local biholomorphisms. -/
theorem canonicalPoint_coords (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (P : ComplexPoint X) :
    ∃ (U : X.left.Opens) (s : Fin n → Γ(X.left, U)),
      P ∈ Point.overOpen U ∧ IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
        (fun Q i => Point.evaluate U (s i) Q) P := by
  let D := ComplexPoint.localEtaleCoordinates X n P
  let c := ComplexPoint.localChart X n P
  let d : PartialDiffeomorph 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ)
      (ComplexPoint X) (Fin n → ℂ) ω :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hP : P ∈ Point.overOpen D.ambientCoordinateOpen := by
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using ComplexPoint.mem_localEtaleCoordinates X n P
  refine ⟨D.ambientCoordinateOpen, D.ambientCoordinateSection, hP, ?_⟩
  unfold IsLocalDiffeomorphAt
  refine ⟨d, ComplexPoint.mem_localChart_source X n P, ?_⟩
  intro Q hQ
  funext i
  exact (ComplexPoint.localChart_apply_component_eq_evaluate X n P Q hQ i).symm

end ZInQ.Contrib.CloudB3W17GAGA
