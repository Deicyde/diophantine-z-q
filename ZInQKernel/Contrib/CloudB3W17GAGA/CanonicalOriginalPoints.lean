import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalModels
import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalPointComparison

/-!
# Original complex points in the actual canonical models

Specialize the verified generic/native-canonical analytic suppliers to the
ORIGINAL `CPts A (RingHom.id ℂ)`, using the committed Hodge carrier/member/
evaluation/topology/atlas dictionary and the separately banked Cω comparison.
The canonical data are unchanged. No field, algebraic map, GAGA hypothesis,
full-lattice premise, source-dimension equality, or target uniformization is added.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cEvalAt)

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17GAGA

local instance cptsIntegral (A : AbVar ℂ) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

local instance cptsTopology (A : AbVar ℂ) : TopologicalSpace (APts A) :=
  CloudB3W17Hodge.classicalTopology A.X

local instance cptsChartedSpace (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom] :
    ChartedSpace (Fin n → ℂ) (APts A) :=
  CloudB3W17Hodge.chartedSpace A.X n

/-- Original identity-embedding CPts is the committed canonical Point carrier. -/
abbrev cptModelEquiv (A : AbVar ℂ) : APts A ≃ ComplexPoint A.X :=
  CloudB3W17Hodge.cptEquiv A.X

/-- The committed homeomorphism, on the original CPts rather than a test carrier. -/
abbrev cptModelHomeomorph (A : AbVar ℂ) : APts A ≃ₜ ComplexPoint A.X :=
  CloudB3W17Hodge.cptHomeomorph A.X

/-- The original-carrier instance of the independently usable comparison supplier. -/
abbrev cptModelDiffeomorph (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom] :
    APts A ≃ₘ^ω⟮𝓘(ℂ, Fin n → ℂ), 𝓘(ℂ, Fin n → ℂ)⟯ ComplexPoint A.X :=
  cptDiffeomorph A.X n

/-- Original cEvalAt is precisely the native canonical Γ-evaluation, even off U. -/
theorem cEvalAt_eq_canonicalEvaluate (A : AbVar ℂ) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) (P : APts A) :
    cEvalAt P U s = Point.evaluate U s (cptModelEquiv A P) := by
  rw [ZInQ.LeafPush2.cEvalAt_eq_evalAt A P U s]
  exact CloudB3W17Hodge.xevalAt_eq_evaluate A.X U s P

/-- The original CPts point-domain and native canonical open agree. -/
theorem pointDom_eq_canonicalPreimage (A : AbVar ℂ) (U : A.X.left.Opens) :
    pointDom A U = cptModelEquiv A ⁻¹' Point.overOpen U := by
  ext P
  exact CloudB3W17Hodge.ptIn_iff A.X P U

/-- Genuine Zariski point-domains are open in the committed original-CPts topology. -/
theorem canonical_isOpen_pointDom (A : AbVar ℂ) (U : A.X.left.Opens) :
    IsOpen (pointDom A U) := by
  rw [pointDom_eq_canonicalPreimage]
  exact (Point.isOpen_overOpen U).preimage (cptModelHomeomorph A).continuous

section TransportBasis

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {U : Type*} {S : U → Type*}

/-- Transport a finite regular-evaluation neighbourhood basis through a homeomorphism.
This is a helper on genuine functions, not a model/algebraicity hypothesis bundle. -/
theorem regular_neighbourhood_of_homeomorph (e : X ≃ₜ Y)
    (domX : U → Set X) (domY : U → Set Y)
    (evalX : ∀ u, S u → X → ℂ) (evalY : ∀ u, S u → Y → ℂ)
    (hdom : ∀ x u, x ∈ domX u ↔ e x ∈ domY u)
    (heval : ∀ x u s, evalX u s x = evalY u s (e x))
    (hn : ∀ (y : Y) (N : Set Y), N ∈ 𝓝 y →
      ∃ (u : U) (k : ℕ) (s : Fin k → S u) (ε : ℝ), 0 < ε ∧ y ∈ domY u ∧
        ∀ y' ∈ domY u, (∀ i, ‖evalY u (s i) y' - evalY u (s i) y‖ < ε) → y' ∈ N)
    (x : X) (N : Set X) (hN : N ∈ 𝓝 x) :
    ∃ (u : U) (k : ℕ) (s : Fin k → S u) (ε : ℝ), 0 < ε ∧ x ∈ domX u ∧
      ∀ x' ∈ domX u, (∀ i, ‖evalX u (s i) x' - evalX u (s i) x‖ < ε) → x' ∈ N := by
  have hN' : e.symm ⁻¹' N ∈ 𝓝 (e x) := by
    apply e.symm.continuous.continuousAt.preimage_mem_nhds
    rwa [e.symm_apply_apply]
  obtain ⟨u, k, s, ε, hε, hU, hsep⟩ := hn (e x) (e.symm ⁻¹' N) hN'
  refine ⟨u, k, s, ε, hε, (hdom x u).mpr hU, ?_⟩
  intro x' hx' hxi
  have hv : ∀ i, ‖evalY u (s i) (e x') - evalY u (s i) (e x)‖ < ε := by
    intro i
    rw [← heval x' u (s i), ← heval x u (s i)]
    exact hxi i
  have hm := hsep (e x') ((hdom x' u).mp hx') hv
  change e.symm (e x') ∈ N at hm
  rwa [e.symm_apply_apply] at hm

end TransportBasis

/-- Finite Γ-evaluations detect neighbourhoods on ORIGINAL CPts in the canonical topology. -/
theorem canonical_cpts_neighbourhood (A : AbVar ℂ) (P₀ : APts A)
    (N : Set (APts A)) (hN : N ∈ 𝓝 P₀) :
    ∃ (U : A.X.left.Opens) (k : ℕ) (s : Fin k → Γ(A.X.left, U)) (ε : ℝ),
      0 < ε ∧ P₀ ∈ pointDom A U ∧ ∀ P : APts A, P ∈ pointDom A U →
        (∀ i, ‖cEvalAt P U (s i) - cEvalAt P₀ U (s i)‖ < ε) → P ∈ N := by
  exact regular_neighbourhood_of_homeomorph (cptModelHomeomorph A)
    (pointDom A) (fun U => Point.overOpen U)
    (fun U s P => cEvalAt P U s) (fun U s P => Point.evaluate U s P)
    (fun P U => CloudB3W17Hodge.ptIn_iff A.X P U)
    (fun P U s => cEvalAt_eq_canonicalEvaluate A U s P)
    (canonicalPoint_neighbourhood A.X) P₀ N hN

section FunctionTransfer

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [ChartedSpace E X] [ChartedSpace F Y]

/-- Transfer scalar regularity through an actual diffeomorphism, without unfolding its atlas. -/
theorem contMDiffOn_pullback (e : X ≃ₘ^ω⟮𝓘(𝕜, E), 𝓘(𝕜, F)⟯ Y)
    (s : Set X) (t : Set Y) (fX : X → 𝕜) (fY : Y → 𝕜)
    (heq : ∀ x, fX x = fY (e x)) (hmap : MapsTo e s t)
    (hY : ContMDiffOn 𝓘(𝕜, F) 𝓘(𝕜, 𝕜) ω fY t) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) ω fX s := by
  apply (hY.comp e.contMDiff.contMDiffOn hmap).congr
  intro x hx
  exact heq x

end FunctionTransfer

/-- Genuine Γ-evaluations are Cω in the actual canonical atlas on ORIGINAL CPts. -/
theorem canonical_cpts_holo (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom]
    (U : A.X.left.Opens) (s : Γ(A.X.left, U)) :
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω
      (fun P : APts A => cEvalAt P U s) (pointDom A U) := by
  exact contMDiffOn_pullback (cptModelDiffeomorph A n)
    (pointDom A U) (Point.overOpen U)
    (fun P => cEvalAt P U s) (fun P => Point.evaluate U s P)
    (cEvalAt_eq_canonicalEvaluate A U s)
    (fun P hP => (CloudB3W17Hodge.ptIn_iff A.X P U).mp hP)
    (canonicalPoint_holo A.X n U s)

/-- The actual canonical Γ-coordinates are local biholomorphisms on ORIGINAL CPts. -/
theorem canonical_cpts_coords (A : AbVar ℂ) (n : ℕ) [SmoothOfRelativeDimension n A.X.hom]
    (P : APts A) :
    ∃ (U : A.X.left.Opens) (s : Fin n → Γ(A.X.left, U)),
      P ∈ pointDom A U ∧ IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
        (fun Q i => cEvalAt Q U (s i)) P := by
  let e := cptModelDiffeomorph A n
  obtain ⟨U, s, hU, hl⟩ := canonicalPoint_coords A.X n (e P)
  refine ⟨U, s, (CloudB3W17Hodge.ptIn_iff A.X P U).mpr hU, ?_⟩
  have hcmp := (e.isLocalDiffeomorph P).comp 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ) hl
  have hfun : (fun Q : APts A => fun i => cEvalAt Q U (s i)) =
      (fun Q : APts A => fun i => Point.evaluate U (s i) (e Q)) := by
    funext Q i
    exact cEvalAt_eq_canonicalEvaluate A U (s i) Q
  rw [hfun]
  exact hcmp

/-- Canonical-model specialization requiring only the original strong-uniformization premise.
The given g, Λ and φ remain arbitrary; there is no g=dim premise, full-lattice premise or GAGA. -/
theorem strongUnif_canonical_diffeomorph (A : AbVar ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (APts A))
    (hφ : ZInQ.HomLattice.IsStrongUnif A (RingHom.id ℂ) Λ φ) :
    ∃ e : BPAnalytic.Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin g → ℂ),
        𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)⟯ APts A,
      (∀ q, e q = phiPts φ q) ∧ (∀ P, e.symm P = phiInv φ P) :=
  strongUnif_diffeomorph A (TopologicalSpace.dim A.X.left)
    (canonical_isOpen_pointDom A) (canonical_cpts_holo A _)
    (canonical_cpts_neighbourhood A) (canonical_cpts_coords A _) φ hφ

/-- Unique holomorphic group descent in the actual canonical models of ORIGINAL CPts A and B.
Only the original Γ-DifferentiableOn ψ input is used. No B uniformization/H103/GAGA is assumed. -/
theorem existsUnique_holomorphic_descent_canonical (A B : AbVar ℂ) {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (APts A))
    (hφ : ZInQ.HomLattice.IsStrongUnif A (RingHom.id ℂ) Λ φ)
    {ψ : (Fin g → ℂ) → APts B} (hψ : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ∃! F : APts A →* APts B,
      MDifferentiable 𝓘(ℂ, Fin (TopologicalSpace.dim A.X.left) → ℂ)
        𝓘(ℂ, Fin (TopologicalSpace.dim B.X.left) → ℂ) F ∧
        ∀ z, F (phiPts φ (BPAnalytic.proj Λ z)) = ψ z :=
  existsUnique_holomorphic_descent A B (TopologicalSpace.dim A.X.left) (TopologicalSpace.dim B.X.left)
    (canonical_isOpen_pointDom A) (canonical_cpts_holo A _)
    (canonical_cpts_neighbourhood A) (canonical_cpts_coords A _)
    (canonical_cpts_neighbourhood B) (canonical_cpts_coords B _) φ hφ hψ hΛ

end ZInQ.Contrib.CloudB3W17GAGA
