import ZInQKernel.HDecomp.Objects

/-!
# The original finite torsion Galois action

The finite level is the actual subgroup of geometric points killed by an
integer. Its automorphisms are induced by the original scheme action,
and Tate evaluation is equivariant and compatible with multiplication.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualFiniteLevel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma galAct_one (A : PkgI3.AbVar K) (x : A.Pt Ω) : A.galAct 1 x = x := by
  change PkgI3.AbVar.galHom 1 ≫ x = x
  rw [PkgI3.AbVar.galHom_one, Category.id_comp]

lemma galAct_mul (A : PkgI3.AbVar K) (σ τ : Ω ≃ₐ[K] Ω) (x : A.Pt Ω) :
    A.galAct (σ * τ) x = A.galAct σ (A.galAct τ x) := by
  change PkgI3.AbVar.galHom (σ * τ) ≫ x =
    PkgI3.AbVar.galHom σ ≫ (PkgI3.AbVar.galHom τ ≫ x)
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

def torsionSubgroup (A : PkgI3.AbVar K) (Ω : Type) [Field Ω] [Algebra K Ω] (m : ℕ) :
    Subgroup (A.Pt Ω) where
  carrier := {x | x ^ m = 1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change (x * y) ^ m = 1
    change x ^ m = 1 at hx
    change y ^ m = 1 at hy
    rw [mul_pow, hx, hy, _root_.one_mul]
  inv_mem' := by
    intro x hx
    change x⁻¹ ^ m = 1
    change x ^ m = 1 at hx
    rw [inv_pow, hx, inv_one]

@[simp] lemma mem_torsionSubgroup (A : PkgI3.AbVar K) (m : ℕ) (x : A.Pt Ω) :
    x ∈ torsionSubgroup A Ω m ↔ x ^ m = 1 := Iff.rfl

def action (A : PkgI3.AbVar K) (m : ℕ) :
    (Ω ≃ₐ[K] Ω) →* MulAut (torsionSubgroup A Ω m) where
  toFun σ :=
    { toFun := fun x => ⟨A.galAct σ x.1, by
        change A.galAct σ x.1 ^ m = 1
        rw [← map_pow]
        exact (congrArg (A.galAct σ) x.2).trans (map_one _)⟩
      invFun := fun x => ⟨A.galAct σ⁻¹ x.1, by
        change A.galAct σ⁻¹ x.1 ^ m = 1
        rw [← map_pow]
        exact (congrArg (A.galAct σ⁻¹) x.2).trans (map_one _)⟩
      left_inv := fun x => Subtype.ext (by
        change A.galAct σ⁻¹ (A.galAct σ x.1) = x.1
        rw [← galAct_mul, inv_mul_cancel, galAct_one])
      right_inv := fun x => Subtype.ext (by
        change A.galAct σ (A.galAct σ⁻¹ x.1) = x.1
        rw [← galAct_mul, mul_inv_cancel, galAct_one])
      map_mul' := fun x y => Subtype.ext (map_mul (A.galAct σ) x.1 y.1) }
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact galAct_one A x.1
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact galAct_mul A σ τ x.1

@[simp] lemma action_apply_coe (A : PkgI3.AbVar K) (m : ℕ) (σ : Ω ≃ₐ[K] Ω)
    (x : torsionSubgroup A Ω m) :
    ((action A m σ x : torsionSubgroup A Ω m) : A.Pt Ω) = A.galAct σ x.1 := rfl

lemma mem_action_ker (A : PkgI3.AbVar K) (m : ℕ) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ (action (Ω := Ω) A m).ker ↔ ∀ x : A.Pt Ω, x ^ m = 1 → A.galAct σ x = x := by
  change action A m σ = 1 ↔ _
  constructor
  · intro h x hx
    exact congrArg (fun e : MulAut (torsionSubgroup A Ω m) => (e ⟨x, hx⟩).1) h
  · intro h
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact h x.1 x.2

variable (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

def tateEvaluation (n : ℕ) :
    PkgI3.Tate.T ℓ (Additive (A.Pt Ω)) →+ Additive (torsionSubgroup A Ω (ℓ ^ n)) where
  toFun t := Additive.ofMul ⟨Additive.toMul (t.1 n), PkgI3.Tate.pow_smul_eq_zero t.2 n⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma tateEvaluation_coe (n : ℕ) (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω))) :
    (Additive.toMul (tateEvaluation (Ω := Ω) A ℓ n t)).1 = Additive.toMul (t.1 n) := rfl

lemma tateEvaluation_galois (n : ℕ) (σ : Ω ≃ₐ[K] Ω)
    (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω))) :
    tateEvaluation A ℓ n (PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ)) t) =
      Additive.ofMul (action A (ℓ ^ n) σ (Additive.toMul (tateEvaluation A ℓ n t))) := rfl

def transition (n : ℕ) : torsionSubgroup A Ω (ℓ ^ (n + 1)) →* torsionSubgroup A Ω (ℓ ^ n) where
  toFun x := ⟨x.1 ^ ℓ, by
    change (x.1 ^ ℓ) ^ (ℓ ^ n) = 1
    rw [← pow_mul, ← pow_succ']
    exact x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := Subtype.ext (mul_pow x.1 y.1 ℓ)

lemma transition_galois (n : ℕ) (σ : Ω ≃ₐ[K] Ω) (x : torsionSubgroup A Ω (ℓ ^ (n + 1))) :
    transition A ℓ n (action A (ℓ ^ (n + 1)) σ x) = action A (ℓ ^ n) σ (transition A ℓ n x) := by
  apply Subtype.ext
  exact (map_pow (A.galAct σ) x.1 ℓ).symm

lemma transition_tateEvaluation (n : ℕ) (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω))) :
    transition A ℓ n (Additive.toMul (tateEvaluation A ℓ (n + 1) t)) =
      Additive.toMul (tateEvaluation A ℓ n t) := Subtype.ext (t.2.2 n)

lemma level_zero_subsingleton : Subsingleton (torsionSubgroup A Ω (ℓ ^ 0)) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx : x.1 = 1 := by simpa using x.2
  have hy : y.1 = 1 := by simpa using y.2
  exact hx.trans hy.symm

end ActualFiniteLevel
