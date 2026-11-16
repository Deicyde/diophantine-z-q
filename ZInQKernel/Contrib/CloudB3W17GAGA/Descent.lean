import ZInQKernel.OneProof.H.TailQ

/-!
# Analytic regular-function descent through a discrete quotient

W17 H105 preparatory supplier. An `IsAnalyticHom` killing a discrete subgroup
has a unique additive descent. Every regular-function domain of that descent
is open, and its regular evaluations are manifold-differentiable on that domain.

This is **not** algebraization and does not discharge `GAGAMorphism`.
The quotient lift is Mathlib's `QuotientAddGroup.lift`; the analytic part uses
BPAnalytic's existing covering charts. No linear lift or global `ContMDiff`
projection-descent theorem is re-proved. In particular, the input's
`DifferentiableOn ℂ` is not silently upgraded to multivariable analyticity.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cDom cEvalAt)
open ZInQ.HomLattice (IsAnalyticHom)
open BPAnalytic (Torus proj)

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17GAGA

variable {K : Type} [Field K] {B : AbVar K} {σ : K →+* ℂ} {g : ℕ}
variable {Λ : Submodule ℤ (Fin g → ℂ)}
variable {ψ : (Fin g → ℂ) → CPts B σ}

/-- The additive form of the homomorphism clause of `IsAnalyticHom`. -/
def analyticAddHom (hψ : IsAnalyticHom σ ψ) :
    (Fin g → ℂ) →+ Additive (CPts B σ) where
  toFun z := Additive.ofMul (ψ z)
  map_zero' := by
    change ψ 0 = 1
    exact ZInQ.HomLattice.map_zero_of_hom hψ.1
  map_add' z w := by
    change ψ (z + w) = ψ z * ψ w
    exact hψ.1 z w

/-- The quotient homomorphism associated to an analytic homomorphism killing Λ. -/
def descendHom (hψ : IsAnalyticHom σ ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    Torus Λ →+ Additive (CPts B σ) :=
  QuotientAddGroup.lift Λ.toAddSubgroup (analyticAddHom hψ) (by
    intro z hz
    change ψ z = 1
    exact hΛ z hz)

@[simp]
theorem descendHom_proj (hψ : IsAnalyticHom σ ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1)
    (z : Fin g → ℂ) :
    descendHom hψ hΛ (proj Λ z) = Additive.ofMul (ψ z) := rfl

/-- The universal property fixes the descent; no surjectivity of ψ is needed. -/
theorem descendHom_unique (hψ : IsAnalyticHom σ ψ) (hΛ : ∀ z ∈ Λ, ψ z = 1)
    (F : Torus Λ →+ Additive (CPts B σ))
    (hF : ∀ z, F (proj Λ z) = Additive.ofMul (ψ z)) : F = descendHom hψ hΛ := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact (hF z).trans (descendHom_proj hψ hΛ z).symm

/-- The points of the source quotient mapping into a Zariski open of B. -/
def torusDom (F : Torus Λ → Additive (CPts B σ)) (U : B.X.left.Opens) :
    Set (Torus Λ) :=
  {q | ⊤ ≤ (Additive.toMul (F q)).left ⁻¹ᵁ U}

/-- Evaluation of a regular function after a quotient map, used only on `torusDom`. -/
def torusEval (F : Torus Λ → Additive (CPts B σ)) (U : B.X.left.Opens)
    (s : Γ(B.X.left, U)) (q : Torus Λ) : ℂ :=
  cEvalAt (Additive.toMul (F q)) U s

@[simp]
theorem preimage_torusDom_descendHom (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) (U : B.X.left.Opens) :
    proj Λ ⁻¹' torusDom (descendHom hψ hΛ) U = cDom ψ U := by
  ext z
  simp only [mem_preimage, torusDom, mem_ofPred_eq, descendHom_proj]
  rfl

@[simp]
theorem torusEval_descendHom_proj (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) (U : B.X.left.Opens) (s : Γ(B.X.left, U))
    (z : Fin g → ℂ) :
    torusEval (descendHom hψ hΛ) U s (proj Λ z) = cEvalAt (ψ z) U s := rfl

/-- The descended regular-function domains are open in the quotient topology. -/
theorem isOpen_torusDom_descendHom (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) (U : B.X.left.Opens) :
    IsOpen (torusDom (descendHom hψ hΛ) U) := by
  apply (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).isOpen_preimage.mp
  rw [preimage_torusDom_descendHom hψ hΛ U]
  exact hψ.2.1 U

variable [DiscreteTopology Λ]

/-- Regular evaluations descend holomorphically, in the manifold-differentiable sense.
The proof stays on the given open regular-function domain and uses one covering chart. -/
theorem mdifferentiableOn_torusEval_descendHom (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) (U : B.X.left.Opens) (s : Γ(B.X.left, U)) :
    MDifferentiableOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ)
      (torusEval (descendHom hψ hΛ) U s) (torusDom (descendHom hψ hΛ) U) := by
  intro q hq
  let c := chartAt (Fin g → ℂ) q
  have hqc : q ∈ c.source := mem_chart_source (Fin g → ℂ) q
  have hpc : proj Λ (c q) = q := BPAnalytic.proj_chartOf Λ hqc
  have hz : c q ∈ cDom ψ U := by
    rw [← preimage_torusDom_descendHom hψ hΛ U]
    change proj Λ (c q) ∈ torusDom (descendHom hψ hΛ) U
    rw [hpc]
    exact hq
  have hd : DifferentiableAt ℂ (fun z => cEvalAt (ψ z) U s) (c q) :=
    (hψ.2.2 U s).differentiableAt ((hψ.2.1 U).mem_nhds hz)
  have hc' : ContMDiffAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω c q :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hqc)
  have hc : MDifferentiableAt 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) c q :=
    hc'.mdifferentiableAt (by simp)
  have heq : torusEval (descendHom hψ hΛ) U s =ᶠ[𝓝 q]
      (fun z => cEvalAt (ψ z) U s) ∘ c := by
    filter_upwards [c.open_source.mem_nhds hqc] with q' hq'
    have hp : proj Λ (c q') = q' := BPAnalytic.proj_chartOf Λ hq'
    calc
      torusEval (descendHom hψ hΛ) U s q' =
          torusEval (descendHom hψ hΛ) U s (proj Λ (c q')) :=
        congrArg (torusEval (descendHom hψ hΛ) U s) hp.symm
      _ = cEvalAt (ψ (c q')) U s := torusEval_descendHom_proj hψ hΛ U s (c q')
  exact ((hd.mdifferentiableAt.comp q hc).congr_of_eventuallyEq heq).mdifferentiableWithinAt

/-- Unique analytic regular-function descent. This preparatory theorem has no algebraicity
premise and assumes neither a full lattice nor the dimension of an abelian variety. -/
theorem existsUnique_regular_analytic_descent (hψ : IsAnalyticHom σ ψ)
    (hΛ : ∀ z ∈ Λ, ψ z = 1) :
    ∃! F : Torus Λ →+ Additive (CPts B σ),
      (∀ z, F (proj Λ z) = Additive.ofMul (ψ z)) ∧
      (∀ U : B.X.left.Opens, IsOpen (torusDom F U)) ∧
      (∀ (U : B.X.left.Opens) (s : Γ(B.X.left, U)),
        MDifferentiableOn 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, ℂ) (torusEval F U s) (torusDom F U)) := by
  refine ⟨descendHom hψ hΛ, ⟨descendHom_proj hψ hΛ,
    isOpen_torusDom_descendHom hψ hΛ, mdifferentiableOn_torusEval_descendHom hψ hΛ⟩, ?_⟩
  intro F hF
  exact descendHom_unique hψ hΛ F hF.1

end ZInQ.Contrib.CloudB3W17GAGA
