import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedDeterminantTransport

/-! # Transport the marked Hodge metric through the actual open subgroup

The model on the open subgroup uses the inverse of the actual generic Hodge pullback.
The resulting period lattice and the coefficient of the marked section are exactly the
original ones, separately at every embedding.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Obj

noncomputable section

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Metrize the actual open subgroup using the same analytically uniformized generic fiber.
The sole lattice witness is the pullback of the marked original section. -/
def markedOpenMetrized {g : ℕ} (G : GroupModel A L) (M : MetrizedModel A L g)
    (j : G.G ⟶ M.model.G) [IsMonHom j] [IsOpenImmersion j.left]
    [IsIso ((Over.pullback (jL L)).map j)] (eta : M.model.hodgeSpace g)
    (heta : eta ∈ M.model.detLattice g) (hz : eta ≠ 0)
    (hi : secIndex (M.model.detLattice g) eta ≠ 0) : MetrizedModel A L g := by
  let E := LinearEquiv.ofBijective (hodgeMap G M.model j g)
    (hodgeMapBijective K A L G M.model j inferInstance g)
  let D := pullHodge M.hodge E.symm.toLinearMap E.symm.injective (G.detLattice g)
    (E.finrank_eq.symm.trans M.hodge.finrank_eq_one)
    ⟨E eta, hodgeMap_detLattice G M.model j g eta heta,
      fun hz' => hz (E.injective (hz'.trans E.map_zero.symm)),
      fun hi' => hi ((secIndex_hodgeMap_openIso G M.model j g eta).trans hi')⟩
  haveI := isIso_genMap G M.model j
  refine { model := G, hodge := D, lattice_eq := rfl, arch := ?_ }
  intro τ
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  let q := Equiv.ofBijective _ (pts_comp_bijective G M.model j τ)
  let Ψ : (Fin g → ℂ) → G.Pts τ := fun z => q.symm (Φ z)
  have hΦΨ : (fun z => Ψ z ≫ j) = Φ := funext fun z => q.apply_symm_apply (Φ z)
  have hU := isAnalyticUniformization_of_comp G M.model j τ _ Ψ (hΦΨ ▸ hΦ)
  refine ⟨Ψ, hU, fun t => ?_⟩
  let t₀ : Fin g → IsLocalRing.maximalIdeal M.model.genStalk := fun i =>
    ⟨(inv (genMap G M.model j)) (t i), by
      rw [← genMap_mem_maximalIdeal_iff G M.model j, ← CommRingCat.comp_apply,
        IsIso.inv_hom_id, CommRingCat.id_apply]
      exact (t i).2⟩
  have ht : ∀ i, (t i : G.genStalk) = genMap G M.model j (t₀ i) := fun i => by
    show _ = genMap G M.model j ((inv (genMap G M.model j)) (t i))
    rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  have hw : G.wedge t = hodgeMap G M.model j g (M.model.wedge t₀) := by
    rw [hodgeMap_wedgeGerm]
    congr 1
    funext i
    exact Subtype.ext (ht i)
  change M.hodge.coeff τ (E.symm (G.wedge t)) = _
  have hH : E.symm (G.wedge t) = M.model.wedge t₀ := by
    rw [hw]
    exact E.symm_apply_apply _
  rw [hH, hc, ← jacDet_comp_genMap G M.model j _ Ψ hU t₀ t ht, hΦΨ]

/-- The original section and its actual pullback have the same period lattice and coefficient,
so the metric is unchanged at each specified embedding. -/
theorem markedOpen_periods_coeff {g : ℕ} (G : GroupModel A L) (M : MetrizedModel A L g)
    (j : G.G ⟶ M.model.G) [IsMonHom j] [IsOpenImmersion j.left]
    [IsIso ((Over.pullback (jL L)).map j)] (eta : M.model.hodgeSpace g)
    (heta : eta ∈ M.model.detLattice g) (hz : eta ≠ 0)
    (hi : secIndex (M.model.detLattice g) eta ≠ 0) (τ : L →+* ℂ) :
    let W := markedOpenMetrized G M j eta heta hz hi
    W.hodge.periods τ = M.hodge.periods τ ∧
      W.hodge.coeff τ (hodgeMap G M.model j g eta) = M.hodge.coeff τ eta := by
  let E := LinearEquiv.ofBijective (hodgeMap G M.model j g)
    (hodgeMapBijective K A L G M.model j inferInstance g)
  refine ⟨rfl, ?_⟩
  change M.hodge.coeff τ (E.symm (E eta)) = M.hodge.coeff τ eta
  rw [E.symm_apply_apply]

/-- In original Faltings normalization the squared norm of the marked section is unchanged
at every embedding under this open-subgroup pullback. -/
theorem markedOpen_torusMetricSq {g : ℕ} (G : GroupModel A L) (M : MetrizedModel A L g)
    (j : G.G ⟶ M.model.G) [IsMonHom j] [IsOpenImmersion j.left]
    [IsIso ((Over.pullback (jL L)).map j)] (eta : M.model.hodgeSpace g)
    (heta : eta ∈ M.model.detLattice g) (hz : eta ≠ 0)
    (hi : secIndex (M.model.detLattice g) eta ≠ 0) (τ : L →+* ℂ) :
    let W := markedOpenMetrized G M j eta heta hz hi
    torusMetricSq (W.hodge.periods τ) (W.hodge.coeff τ (hodgeMap G M.model j g eta)) =
      torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta) := by
  dsimp only
  obtain ⟨hp, hc⟩ := markedOpen_periods_coeff G M j eta heta hz hi τ
  rw [hp, hc]

#print axioms markedOpenMetrized
#print axioms markedOpen_periods_coeff
#print axioms markedOpen_torusMetricSq

end ZInQ.Contrib.IsogenyDegree
