import ZInQKernel.Contrib.CloudB3W17LocalExp.UnconditionalTorus

/-!
# A positive-dimensional in-tree instance of the unconditional torus theorem

`CloudB3W17LocalExp.exists_torus_diffeo` quantifies over compact connected commutative complex Lie
groups. This file shows the class is inhabited **inside Lean**, by a positive-dimensional group, so the
theorem is not vacuous: the complex torus `ℂ / (ℤ + ℤ i)` of the Siegel point `Ω = i`, written
multiplicatively.

Two steps:

* transport of the analytic structure along the type synonym `Multiplicative`
  (`ChartedSpace`, `IsManifold`, `LieGroup`, `CompactSpace`, `ConnectedSpace` for
  `Multiplicative (BPAnalytic.Torus Λ)`), all by `inferInstanceAs` on the same carrier and the
  existing additive proofs — no analytic structure is re-proved;
* the instance itself: `Lat = periodLattice` of `Ω = i`, `Ex = Multiplicative (Torus Lat)`,
  which is nontrivial (`1/2 ∉ Lat`), and `example_torus_diffeo` applies the unconditional theorem to it.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Matrix

noncomputable section

namespace CloudB3W17LocalExp

open BPAnalytic

/-! ## 1. Transport along `Multiplicative` -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Λ : Submodule ℤ E)
  [DiscreteTopology Λ]

/-- The multiplicative copy of a complex torus is charted by the same atlas. -/
instance instChartedSpaceMultiplicativeTorus :
    ChartedSpace E (Multiplicative (Torus Λ)) :=
  inferInstanceAs (ChartedSpace E (Torus Λ))

instance instIsManifoldMultiplicativeTorus :
    IsManifold 𝓘(ℂ, E) ω (Multiplicative (Torus Λ)) :=
  inferInstanceAs (IsManifold 𝓘(ℂ, E) ω (Torus Λ))

/-- Multiplication and inversion of `Multiplicative (Torus Λ)` are the addition and negation of
`Torus Λ`, which are analytic (`BPAnalytic.lieAddGroup_torus`). -/
instance instLieGroupMultiplicativeTorus :
    LieGroup 𝓘(ℂ, E) ω (Multiplicative (Torus Λ)) where
  contMDiff_mul := ContMDiffAdd.contMDiff_add (I := 𝓘(ℂ, E)) (n := ω) (G := Torus Λ)
  contMDiff_inv := LieAddGroup.contMDiff_neg (I := 𝓘(ℂ, E)) (n := ω) (G := Torus Λ)

instance instConnectedSpaceMultiplicativeTorus :
    ConnectedSpace (Multiplicative (Torus Λ)) :=
  inferInstanceAs (ConnectedSpace (Torus Λ))

instance instCompactSpaceMultiplicativeTorus [FiniteDimensional ℂ E] [IsZLattice ℝ Λ] :
    CompactSpace (Multiplicative (Torus Λ)) :=
  inferInstanceAs (CompactSpace (Torus Λ))

end Transport

/-! ## 2. The torus of `Ω = i`, multiplicatively -/

/-- The `1 × 1` period matrix `Ω = i`. -/
def ΩI : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => Complex.I

theorem det_im_ΩI : (ΩI.map Complex.im).det ≠ 0 := by
  simp [ΩI]

/-- The lattice `ℤ i + ℤ ⊂ ℂ`. -/
abbrev Lat : Submodule ℤ (Fin 1 → ℂ) := periodLattice ΩI det_im_ΩI

/-- The elliptic curve `ℂ / (ℤ + ℤ i)`, written multiplicatively: a compact connected commutative
complex Lie group of dimension one. -/
abbrev Ex : Type := Multiplicative (Torus Lat)

theorem half_notMem_Lat : (fun _ => (1 / 2 : ℂ)) ∉ Lat := by
  intro hmem
  obtain ⟨m, n, hv⟩ := (mem_periodLattice_iff ΩI det_im_ΩI _).mp hmem
  have h0 : (1 / 2 : ℂ) = Complex.I * (m 0 : ℂ) + (n 0 : ℂ) := by
    have := congrFun hv 0
    simpa [ΩI, Matrix.mulVec, dotProduct] using this
  have hre : (1 / 2 : ℝ) = (n 0 : ℝ) := by
    have := congrArg Complex.re h0
    simpa using this
  have h2 : ((2 * n 0 : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
  have : (2 * n 0 : ℤ) = 1 := by exact_mod_cast h2
  omega

theorem nontrivial_Ex : Nontrivial Ex := by
  refine ⟨⟨Multiplicative.ofAdd (proj Lat (fun _ => (1 / 2 : ℂ))), 1, ?_⟩⟩
  intro h
  have h' : proj Lat (fun _ => (1 / 2 : ℂ)) = proj Lat 0 := by
    simpa using congrArg Multiplicative.toAdd h
  exact half_notMem_Lat (by simpa using (proj_eq_iff Lat).mp h')

/-! ## 3. The unconditional theorem, applied -/

/-- **Non-vacuity.** The unconditional torus theorem applies to the one-dimensional group
`Ex = ℂ / (ℤ + ℤ i)`: it is a compact connected commutative complex Lie group charted on `ℂ^1`. -/
theorem example_torus_diffeo :
    ∃ (Λ : Submodule ℤ (Fin 1 → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ Ex), ∀ a b, e (a + b) = e a * e b :=
  exists_torus_diffeo (E := Fin 1 → ℂ) (G := Ex)

/-- The full form on the same example: an exponential, surjective, with discrete full-lattice kernel
and an analytic group isomorphism from the quotient. -/
theorem example_exp_torus_diffeo :
    ∃ (exp : (Fin 1 → ℂ) → Ex) (Λ : Submodule ℤ (Fin 1 → ℂ)) (_ : DiscreteTopology Λ)
      (_ : IsZLattice ℝ Λ) (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ Ex),
      Function.Surjective exp ∧ (∀ v, v ∈ Λ ↔ exp v = 1) ∧
        (∀ a b, e (a + b) = e a * e b) ∧ ∀ v, e (proj Λ v) = exp v :=
  exists_exp_torus_diffeo (E := Fin 1 → ℂ) (G := Ex)

/-- The commutative Mumford statement, applied to the same positive-dimensional example. -/
theorem example_mumfordComplexTorus_comm :
    ∃ (Λ : Submodule ℤ (Fin 1 → ℂ)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, Fin 1 → ℂ), 𝓘(ℂ, Fin 1 → ℂ)⟯ Ex), ∀ a b, e (a + b) = e a * e b :=
  mumfordComplexTorus_comm 1 Ex inferInstance inferInstance inferInstance inferInstance

end CloudB3W17LocalExp
