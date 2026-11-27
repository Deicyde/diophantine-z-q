import ZInQKernel.Contrib.G9.I4Layer

/-!
# Colmez's period pairing on `T_p` versus `V_p`

Colmez, Math. Ann. 292 (1992), Théorème 5.2 (ii), p. 639, states the period pairing on
`H¹_dR(X) × T_p(X)` ("Soit u=(…,u_n,…) … un élément du module de Tate T_p(X) de X"), non-degenerate
"quand on étend les scalaires à B_dR". The tree's rows state it on `V_p = ℚ_p ⊗ T_p`.

For a `ℤ_p`-module `T` with a `G_F`-action `τ` and `V = ℚ_p ⊗_{ℤ_p} T` with `ρ = τ ⊗ ℚ_p`:

* `ShapeT p F S τ`: `∃ H, P : H → (T →ₗ[ℤ_p] B_dR)`, values in `S`, Galois-equivariant, and
  non-degenerate after `B_dR ⊗_{ℤ_p} T` (`B_dR` is a `ℤ_p`-algebra through `ℤ_p ⊂ ℚ_p`,
  `algZp`, a scoped instance).
* `ShapeV p F S ρ`: the same with `P : H → (V →ₗ[ℚ_p] B_dR)` and `B_dR ⊗_{ℚ_p} V` (the body of the
  tree's `ColmezShape` with `Q = (· ∈ S)`).
* `shapeT_iff_shapeV`: the two are equivalent when `S` is a `ℚ_p`-submodule (as `B_dR^+` is).
-/

namespace ZInQ.Contrib.ColmezTiltIso.Tp

set_option linter.unusedSectionVars false

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-- `B_dR` as a `ℤ_p`-algebra, through `ℤ_p ⊂ ℚ_p ⊂ B_dR`. -/
noncomputable scoped instance algZp : Algebra ℤ_[p] (BdR p) :=
  ((algebraMap ℚ_[p] (BdR p)).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

scoped instance isScalarTower_zp : IsScalarTower ℤ_[p] ℚ_[p] (BdR p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (F : Type*) [Field F] [Algebra ℚ_[p] F]

/-- The pairing on `T` (`ℤ_p`-linear), non-degenerate after `B_dR ⊗_{ℤ_p} T`. -/
def ShapeT (S : Submodule ℚ_[p] (BdR p)) {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    (τ : Field.absoluteGaloisGroup F → T →ₗ[ℤ_[p]] T) : Prop :=
  ∃ (H : Type) (P : H → (T →ₗ[ℤ_[p]] BdR p)),
    (∀ ω u, P ω u ∈ S) ∧
    (∀ ω (σ : Field.absoluteGaloisGroup F) u,
      P ω (τ σ u) = bdrAct p (gfToGqp p F σ) (P ω u)) ∧
    (∀ x : BdR p ⊗[ℤ_[p]] T, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0)

/-- The pairing on `V` (`ℚ_p`-linear), non-degenerate after `B_dR ⊗_{ℚ_p} V`. -/
def ShapeV (S : Submodule ℚ_[p] (BdR p)) {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Field.absoluteGaloisGroup F → V →ₗ[ℚ_[p]] V) : Prop :=
  ∃ (H : Type) (P : H → (V →ₗ[ℚ_[p]] BdR p)),
    (∀ ω u, P ω u ∈ S) ∧
    (∀ ω (σ : Field.absoluteGaloisGroup F) u,
      P ω (ρ σ u) = bdrAct p (gfToGqp p F σ) (P ω u)) ∧
    (∀ x : BdR p ⊗[ℚ_[p]] V, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0)

variable {p F}
variable {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]

theorem liftBaseChange_one_tmul (f : T →ₗ[ℤ_[p]] BdR p) (t : T) :
    f.liftBaseChange ℚ_[p] ((1 : ℚ_[p]) ⊗ₜ t) = f t := by
  rw [LinearMap.liftBaseChange_tmul, one_smul]

theorem liftBaseChange_mem_iff (S : Submodule ℚ_[p] (BdR p)) (f : T →ₗ[ℤ_[p]] BdR p) :
    (∀ u, f u ∈ S) ↔ ∀ v, f.liftBaseChange ℚ_[p] v ∈ S := by
  constructor
  · intro h v
    induction v using TensorProduct.inductionOn with
    | tmul q t => rw [LinearMap.liftBaseChange_tmul]; exact S.smul_mem q (h t)
    | add v w hv hw => rw [map_add]; exact S.add_mem hv hw
  · intro h u
    rw [← liftBaseChange_one_tmul f u]
    exact h _

theorem liftBaseChange_gal_iff (τ : Field.absoluteGaloisGroup F → T →ₗ[ℤ_[p]] T)
    (f : T →ₗ[ℤ_[p]] BdR p) :
    (∀ σ u, f (τ σ u) = bdrAct p (gfToGqp p F σ) (f u)) ↔
      ∀ σ v, f.liftBaseChange ℚ_[p] ((τ σ).baseChange ℚ_[p] v) =
        bdrAct p (gfToGqp p F σ) (f.liftBaseChange ℚ_[p] v) := by
  constructor
  · intro h σ v
    induction v using TensorProduct.inductionOn with
    | tmul q t =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        h, bdrAct_smul]
    | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]
  · intro h σ u
    have := h σ ((1 : ℚ_[p]) ⊗ₜ u)
    rwa [LinearMap.baseChange_tmul, liftBaseChange_one_tmul, liftBaseChange_one_tmul] at this

variable (p T) in
/-- `B_dR ⊗_{ℚ_p} (ℚ_p ⊗_{ℤ_p} T) ≅ B_dR ⊗_{ℤ_p} T`. -/
noncomputable def cancelEquiv : BdR p ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] T) ≃ₗ[BdR p] BdR p ⊗[ℤ_[p]] T :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[p] ℚ_[p] (BdR p) (BdR p) T

theorem liftBaseChange_cancelEquiv (f : T →ₗ[ℤ_[p]] BdR p)
    (x : BdR p ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] T)) :
    (f.liftBaseChange ℚ_[p]).liftBaseChange (BdR p) x =
      f.liftBaseChange (BdR p) (cancelEquiv p T x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    induction v using TensorProduct.inductionOn with
    | tmul q t =>
      rw [cancelEquiv, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        LinearMap.liftBaseChange_tmul, smul_eq_mul, smul_eq_mul, mul_smul_comm, smul_mul_assoc]
    | add v w hv hw => rw [TensorProduct.tmul_add, map_add, map_add, hv, hw, map_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- **The pairing on `T_p` is equivalent to the pairing on `V_p = ℚ_p ⊗ T_p`.** -/
theorem shapeT_iff_shapeV (S : Submodule ℚ_[p] (BdR p))
    (τ : Field.absoluteGaloisGroup F → T →ₗ[ℤ_[p]] T) :
    ShapeT p F S τ ↔ ShapeV p F S (fun σ => (τ σ).baseChange ℚ_[p]) := by
  constructor
  · rintro ⟨H, P, h0, hgal, hnd⟩
    refine ⟨H, fun ω => (P ω).liftBaseChange ℚ_[p],
      fun ω => (liftBaseChange_mem_iff S (P ω)).1 (h0 ω),
      fun ω => (liftBaseChange_gal_iff τ (P ω)).1 (hgal ω), fun x hx => ?_⟩
    have h1 : cancelEquiv p T x = 0 := hnd _ fun ω => by
      rw [← liftBaseChange_cancelEquiv]
      exact hx ω
    simpa using congrArg (cancelEquiv p T).symm h1
  · rintro ⟨H, P, h0, hgal, hnd⟩
    set P' : H → (T →ₗ[ℤ_[p]] BdR p) := fun ω =>
      (LinearMap.liftBaseChangeEquiv ℚ_[p]).symm (P ω)
    have hP : ∀ ω, (P' ω).liftBaseChange ℚ_[p] = P ω := fun ω =>
      (LinearMap.liftBaseChangeEquiv ℚ_[p]).apply_symm_apply (P ω)
    refine ⟨H, P', fun ω => (liftBaseChange_mem_iff S (P' ω)).2 (by rw [hP]; exact h0 ω),
      fun ω => (liftBaseChange_gal_iff τ (P' ω)).2 (by rw [hP]; exact hgal ω), fun x hx => ?_⟩
    have h1 : (cancelEquiv p T).symm x = 0 := hnd _ fun ω => by
      rw [← hP, liftBaseChange_cancelEquiv, LinearEquiv.apply_symm_apply]
      exact hx ω
    simpa using congrArg (cancelEquiv p T) h1

end ZInQ.Contrib.ColmezTiltIso.Tp
