import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.HDecomp.Analytic.Uniformization

/-! Glue of `docs/research/h-decomposition.md`, new in task hdec-adopt4 (no draft).
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-!
# bp-analytic's uniformization gives leaf-push2's at `σ = id`

The project has two forms of the analytic uniformization (node AN3):

* bp-analytic's `BPAnalytic.Uniformization.IsUniformization A Λ φ`: for `A` over `ℂ`, a group
  isomorphism `φ : ℂ^g ⧸ Λ ≃ A(ℂ)` with clauses (i) holomorphic regular functions, (ii) local
  coordinates, (iii) continuity of `φ⁻¹`; leaf `UniformizationLeafAll`;
* leaf-push2's `ZInQ.LeafPush2.IsUniformization σ Λ Φ`: a surjective homomorphism
  `Φ : ℂ^g → A(ℂ)_σ` with kernel `Λ`, open chart preimages and holomorphic regular functions;
  leaf `UniformizationExists` (all `K`, all `σ`, with `g = dim A`).

`isUniformization_of_bp`: for `A` over `ℂ` and `σ = id`, `Φ = φ ∘ proj` satisfies leaf-push2's
predicate (`CPts A id` is `A.Pt ℂ`, and leaf-push2's `cEvalAt` is bp-analytic's `evalAt`).
`exists_isUniformization_of_leaf`: bp-analytic's leaf gives, for every complex abelian variety,
some `g`, a full lattice `Λ ⊆ ℂ^g` and a uniformization in leaf-push2's sense at `σ = id`. What it
does not give: `g = dim A` (dimension theory of `A`) and other fields `K` and embeddings `σ`
(base change along `σ`); those remain between the two leaves.
-/

namespace ZInQ.LeafPush2

open CategoryTheory AlgebraicGeometry Limits MonObj
open PkgI3 (AbVar)

/-- leaf-push2's complex points at `σ = id` are bp-analytic's `ℂ`-points. -/
theorem cPts_id_eq (A : AbVar ℂ) : CPts A (RingHom.id ℂ) = A.Pt ℂ := rfl

/-- leaf-push2's evaluation `cEvalAt` is bp-analytic's `evalAt`. -/
theorem cEvalAt_eq_evalAt (A : AbVar ℂ) (P : A.Pt ℂ) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) :
    cEvalAt (A := A) (σ := RingHom.id ℂ) P U s = BPAnalytic.Uniformization.evalAt A U s P := by
  unfold cEvalAt BPAnalytic.Uniformization.evalAt BPAnalytic.Uniformization.PtIn
  split <;> split <;> rename_i h1 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

/-- **bp-analytic's uniformization is one in leaf-push2's sense** (`σ = id`, `Φ = φ ∘ proj`). -/
theorem isUniformization_of_bp (A : AbVar ℂ) {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    [DiscreteTopology Λ] {φ : BPAnalytic.Torus Λ ≃+ Additive (A.Pt ℂ)}
    (hφ : BPAnalytic.Uniformization.IsUniformization A Λ φ) :
    IsUniformization (A := A) (RingHom.id ℂ) Λ
      (fun z => Additive.toMul (φ (BPAnalytic.proj Λ z))) := by
  refine ⟨fun z w => ?_, fun z => ?_, fun P => ?_, fun U => ?_, fun U s => ?_⟩
  · change Additive.toMul (φ (BPAnalytic.proj Λ (z + w))) =
      Additive.toMul (φ (BPAnalytic.proj Λ z)) * Additive.toMul (φ (BPAnalytic.proj Λ w))
    rw [← toMul_add, ← map_add]
    rfl
  · change Additive.toMul (φ (BPAnalytic.proj Λ z)) = 1 ↔ z ∈ Λ
    constructor
    · intro h
      have h0 : φ (BPAnalytic.proj Λ z) = φ 0 := by
        rw [map_zero]
        exact h
      have := (BPAnalytic.proj_eq_iff Λ (x := z) (y := 0)).mp (by
        rw [φ.injective h0]; rfl)
      simpa using this
    · intro hz
      have : BPAnalytic.proj Λ z = BPAnalytic.proj Λ 0 :=
        (BPAnalytic.proj_eq_iff Λ).mpr (by simpa using hz)
      rw [this]
      change Additive.toMul (φ 0) = 1
      rw [map_zero]
      rfl
  · obtain ⟨q, hq⟩ := φ.surjective (Additive.ofMul P)
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨z, by simp only [hq]; rfl⟩
  · exact (hφ.holo U 0).1
  · have h := (hφ.holo U s).2
    have hd := h.differentiableOn
    refine hd.congr fun z _ => ?_
    exact cEvalAt_eq_evalAt A _ U s

/-- **bp-analytic's leaf gives leaf-push2's uniformizations at `σ = id`**, for some `g` (not yet
identified with `dim A`). -/
theorem exists_isUniformization_of_leaf (h : BPAnalytic.Uniformization.UniformizationLeafAll)
    (A : AbVar ℂ) :
    ∃ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization (RingHom.id ℂ) Λ Φ := by
  obtain ⟨g, Λ, hd, hz, φ, hφ⟩ := h A
  have := hd
  exact ⟨g, Λ, _, hd, hz, isUniformization_of_bp A hφ⟩

end ZInQ.LeafPush2
