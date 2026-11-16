import ZInQKernel.Contrib.CloudB3W17Realify.ComplexOneParameter
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Global analytic exponential in a finite-dimensional commutative complex Lie group

Constructed as a finite product of fixed analytic one-parameter subgroups along
a complex basis. This bypasses any joint regularity theorem for the velocity
parameter in the real ODE solution. No compactness or connectedness is assumed.
-/

open Function Set
open scoped Manifold Topology ContDiff

namespace CloudB3W17Realify

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup 𝓘(ℂ, E) ω G]

/-- At the identity, the derivative of multiplication is addition of the two derivatives. -/
theorem hasMFDerivAt_mul_at_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f g : V → G} {x : V} {D D' : V →L[ℂ] E}
    (hf : HasMFDerivAt 𝓘(ℂ, V) 𝓘(ℂ, E) f x D)
    (hg : HasMFDerivAt 𝓘(ℂ, V) 𝓘(ℂ, E) g x D')
    (hf1 : f x = 1) (hg1 : g x = 1) :
    HasMFDerivAt 𝓘(ℂ, V) 𝓘(ℂ, E) (fun y => f y * g y) x (D + D') := by
  have hm := ((contMDiff_mul 𝓘(ℂ, E) ω (G := G)).contMDiffAt
    (x := (f x, g x)) |>.mdifferentiableAt (by simp)).hasMFDerivAt
  have h := hm.comp x (hf.prodMk hg)
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro v
  change V at v
  change mfderiv (𝓘(ℂ, E).prod 𝓘(ℂ, E)) 𝓘(ℂ, E)
    (fun p : G × G => p.1 * p.2) (f x, g x) (D v, D' v) = D v + D' v
  rw [mfderiv_prod_eq_add_apply
    ((contMDiff_mul 𝓘(ℂ, E) ω).mdifferentiableAt (by simp))]
  have hfmap : (fun a : G => a * g x) = id := by funext a; simp [hg1]
  have hgmap : (fun a : G => f x * a) = id := by funext a; simp [hf1]
  erw [hfmap, hgmap, mfderiv_id, mfderiv_id]
  rfl

/-- The derivative of a finite product whose factors equal one is the sum of factor derivatives. -/
theorem hasMFDerivAt_prod_at_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type*} (s : Finset ι) (f : ι → V → G) (D : ι → V →L[ℂ] E) (x : V)
    (hf : ∀ i ∈ s, HasMFDerivAt 𝓘(ℂ, V) 𝓘(ℂ, E) (f i) x (D i))
    (hf1 : ∀ i ∈ s, f i x = 1) :
    HasMFDerivAt 𝓘(ℂ, V) 𝓘(ℂ, E) (fun y => ∏ i ∈ s, f i y) x (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using
      (hasMFDerivAt_const (I := 𝓘(ℂ, V)) (I' := 𝓘(ℂ, E)) (1 : G) x)
  | @insert i s hi ih =>
      have hp : (fun y => ∏ j ∈ insert i s, f j y) =
          (fun y => f i y * ∏ j ∈ s, f j y) := by
        funext y
        exact Finset.prod_insert hi
      rw [hp, Finset.sum_insert hi]
      exact hasMFDerivAt_mul_at_one
        (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf1 j (Finset.mem_insert_of_mem hj)))
        (hf1 i (Finset.mem_insert_self _ _))
        (by exact Finset.prod_eq_one (fun j hj => hf1 j (Finset.mem_insert_of_mem hj)))

/-- Assemble a global analytic homomorphism with identity derivative from fixed basis flows. -/
theorem exists_complexExp_of_basis [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ E)
    (hf : ∀ i, ∃ f : ℂ → G, f 0 = 1 ∧ (∀ z w, f (z + w) = f z * f w) ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω f ∧
      HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) f 0 ((ContinuousLinearMap.id ℂ ℂ).smulRight (b i))) :
    ∃ exp : E → G, exp 0 = 1 ∧ (∀ x y, exp (x + y) = exp x * exp y) ∧
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω exp ∧
      HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) exp 0 (ContinuousLinearMap.id ℂ E) := by
  classical
  choose f hf0 hfadd hfa hfd using hf
  let c : ι → E →L[ℂ] ℂ := fun i => (b.coord i).toContinuousLinearMap
  let exp : E → G := fun x => ∏ i, f i (c i x)
  have h0 : exp 0 = 1 := by simp only [exp, map_zero, hf0, Finset.prod_const_one]
  have ha : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω exp :=
    ContMDiff.prod (fun i _ => (hfa i).comp (c i).contDiff.contMDiff)
  have hd : HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) exp 0
      (∑ i, ((ContinuousLinearMap.id ℂ ℂ).smulRight (b i)).comp (c i)) := by
    apply hasMFDerivAt_prod_at_one
    · intro i _
      have hi : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) (f i) (c i 0)
          ((ContinuousLinearMap.id ℂ ℂ).smulRight (b i)) := by
        erw [map_zero]
        exact hfd i
      exact hi.comp 0 ((c i).hasFDerivAt (x := (0 : E))).hasMFDerivAt
    · intro i _
      simp only [map_zero, hf0]
  have hsum : (∑ i, ((ContinuousLinearMap.id ℂ ℂ).smulRight (b i)).comp (c i)) =
      ContinuousLinearMap.id ℂ E := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, c]
    exact b.sum_repr x
  refine ⟨exp, h0, ?_, ha, hsum ▸ hd⟩
  intro x y
  simp only [exp, map_add, hfadd]
  exact Finset.prod_mul_distrib

/-- A finite-dimensional commutative complex analytic Lie group admits a global analytic
exponential homomorphism with identity derivative at zero. -/
theorem exists_complexExp [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] :
    ∃ exp : E → G, exp 0 = 1 ∧ (∀ x y, exp (x + y) = exp x * exp y) ∧
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω exp ∧
      HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) exp 0 (ContinuousLinearMap.id ℂ E) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ, E) ω
  have : T1Space G := ChartedSpace.t1Space E G
  have : T2Space G := inferInstance
  exact exists_complexExp_of_basis (Module.finBasis ℂ E) (fun i => exists_complexOneParameter _)

/-- Bundled additive-to-multiplicative form of the actual global analytic exponential. -/
theorem exists_complexExpHom [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] :
    ∃ exp : E →+ Additive G,
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x => Additive.toMul (exp x)) ∧
      HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x => Additive.toMul (exp x)) 0
        (ContinuousLinearMap.id ℂ E) := by
  obtain ⟨exp, h0, hadd, ha, hd⟩ := exists_complexExp (E := E) (G := G)
  exact ⟨{ toFun := fun x => Additive.ofMul (exp x), map_zero' := h0, map_add' := hadd }, ha, hd⟩

end CloudB3W17Realify
