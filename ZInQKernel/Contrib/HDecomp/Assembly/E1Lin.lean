import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-assembly/E1Lin.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# E1 glue: invariants commute with extension of the coefficient field

N5 L862-864: "Invariants in their finite-dimensional Hom space commute with extension of the
coefficient field." The direction used: if `(E ⊗_F W)^G ≠ 0` then `W^G ≠ 0`, for a
representation `W` of a group `G` over a field `F` and a field extension `E/F` (for E1:
`W = Hom_{ℚ₅}(V₅A, V₅J)`, `G = G_{L'}`, `E` a finite extension of `ℚ₅`). Proved for any
`F`-module `W` (no finiteness needed) by expanding in an `F`-basis of `E`.
-/

namespace GlueAssembly

open TensorProduct

variable {F E W G : Type*} [Field F] [Field E] [Algebra F E] [AddCommGroup W] [Module F W]
  [Group G]

/-- Coordinates of `E ⊗_F W` in an `F`-basis `b` of `E` are natural in `W`. -/
theorem coord_lTensor {ι : Type*} [DecidableEq ι] (b : Module.Basis ι F E) (f : W →ₗ[F] W) (x : E
    ⊗[F] W)
    (i : ι) :
    finsuppScalarLeft F W ι (LinearEquiv.rTensor W b.repr (LinearMap.lTensor E f x)) i =
      f (finsuppScalarLeft F W ι (LinearEquiv.rTensor W b.repr x) i) := by
  induction x using TensorProduct.inductionOn with
  | tmul y w => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- **Invariants and extension of scalars.** If `W^G = 0` then every `G`-invariant vector of
`E ⊗_F W` vanishes. -/
theorem baseChange_invariant_eq_zero (ρ : Representation F G W) (h : ρ.invariants = ⊥)
    (x : E ⊗[F] W) (hx : ∀ g : G, LinearMap.lTensor E (ρ g) x = x) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis F E
  let e : E ⊗[F] W ≃ₗ[F] _ := LinearEquiv.rTensor W b.repr ≪≫ₗ finsuppScalarLeft F W _
  have hcoord : ∀ i, e x i = 0 := by
    intro i
    have hi : e x i ∈ ρ.invariants := by
      rw [Representation.mem_invariants]
      intro g
      have := coord_lTensor b (ρ g) x i
      rw [hx g] at this
      exact this.symm
    rw [h] at hi
    exact hi
  have : e x = 0 := Finsupp.ext hcoord
  exact e.injective (this.trans e.map_zero.symm)

/-- Contrapositive form used in E1: a nonzero invariant after extension of scalars gives a
nonzero invariant before. -/
theorem invariants_ne_bot_of_baseChange (ρ : Representation F G W) (x : E ⊗[F] W) (hx0 : x ≠ 0)
    (hx : ∀ g : G, LinearMap.lTensor E (ρ g) x = x) : ρ.invariants ≠ ⊥ :=
  fun h => hx0 (baseChange_invariant_eq_zero ρ h x hx)

end GlueAssembly
