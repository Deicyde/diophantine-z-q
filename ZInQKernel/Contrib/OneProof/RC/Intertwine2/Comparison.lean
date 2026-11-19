import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Operators
import ZInQKernel.Contrib.OneProof.RC.Intertwine2.Index

/-! Application to a pair of realized rectangular class-function spaces.
Only local tensor evaluations on the elementary cylinders are read from
the specified common lifts. The linear extension is on-the-spot (c)
for tex 8726–8807, 8996–9007. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine2

open Intertwine OldStageLaw RelativeAction
open scoped BigOperators MatrixGroups

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

def classDelta (r : Grid a) : Grid a → ℂ := by
  classical
  exact Pi.single r 1

theorem classDelta_eval (r : Grid a) :
    J rationalFiniteModel (classDelta r) = cosetIndicator r := by
  classical
  funext x
  have he : residue (a := a) rationalFiniteModel x = some r ↔ x ∈ coset (I₀ := integralAdeles) r :=
    residue_eq_some rationalFiniteModel
  change (residue (a := a) rationalFiniteModel x).elim 0 (classDelta r) = cosetIndicator r x
  cases hx : residue (a := a) rationalFiniteModel x with
  | none =>
    have hn : x ∉ coset (I₀ := integralAdeles) r := fun h => by
      have := he.mpr h
      rw [hx] at this
      contradiction
    simp [cosetIndicator, hn]
  | some t =>
    by_cases ht : t = r
    · subst t
      simp [classDelta, cosetIndicator, he.mp hx]
    · have hn : x ∉ coset (I₀ := integralAdeles) r := fun h => by
        have := he.mpr h
        rw [hx, Option.some.injEq] at this
        exact ht this
      simp [classDelta, cosetIndicator, hn, ht]

private theorem sum_classDelta (w : Grid a → ℂ) : (∑ r, w r • classDelta r) = w := by
  classical
  unfold classDelta
  simp_rw [← Pi.single_smul', smul_eq_mul, mul_one]
  exact Finset.univ_sum_single w

private def upperLinear (n : ℤ) : (Grid a → ℂ) →ₗ[ℂ] (Grid a → ℂ) where
  toFun := twist n
  map_add' v w := by funext r; simp [twist, mul_add]
  map_smul' c v := by funext r; simp [twist, mul_left_comm]

private def fourierLinear : (Grid a → ℂ) →ₗ[ℂ] (Grid a → ℂ) where
  toFun := finiteFourier
  map_add' v w := by funext s; simp [finiteFourier, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    funext s
    simp [finiteFourier, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_left_comm]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- Missing local model input on the elementary restricted tensors only.
This specifies the action by products of local operators, with neither
an adèlic integral nor a discriminant-grid action on its right-hand sides. -/
def GeneratorTensorAction
    (E : (Grid a → ℂ) →ₗ[ℂ] V) (eval : V →ₗ[ℂ] (FiniteVectors → ℂ))
    (R : G →* Module.End ℂ V) (lift : Step → G) (γ : Place → ℂˣ) : Prop :=
  (∀ n r x, eval (R (lift (.trans n)) (E (classDelta r))) x =
    ∏ᶠ p, localUpper a p n (localCoset p (atPlace p (center r))) (atPlace p x)) ∧
  (∀ r y, eval (R (lift .inv) (E (classDelta r))) y =
    ∏ᶠ p, (γ p : ℂ) *
      localFourier a p (localCoset p (atPlace p (center r))) (atPlace p y))

private theorem linear_eq_of_classDelta
    (f g : (Grid a → ℂ) →ₗ[ℂ] (FiniteVectors → ℂ))
    (h : ∀ r, f (classDelta r) = g (classDelta r)) : f = g := by
  apply LinearMap.ext
  intro w
  calc
    f w = f (∑ r, w r • classDelta r) := congrArg f (sum_classDelta w).symm
    _ = g (∑ r, w r • classDelta r) := by simp only [map_sum, map_smul, h]
    _ = g w := congrArg g (sum_classDelta w)

theorem generator_descriptions
    (E : (Grid a → ℂ) →ₗ[ℂ] V) (eval : V →ₗ[ℂ] (FiniteVectors → ℂ))
    (hE : ∀ w, eval (E w) = J rationalFiniteModel w) (hsurj : Function.Surjective E)
    (R : G →* Module.End ℂ V) (lift : Step → G) (γ : Place → ℂˣ)
    (hγ : γ.HasFiniteMulSupport) (h : GeneratorTensorAction E eval R lift γ) :
    (∀ n v x, eval (R (lift (.trans n)) v) x =
      finitePhase rationalFiniteModel (-(n : RationalFiniteAdeles) * quad a x) * eval v x) ∧
    (∀ v, eval (R (lift .inv) v) =
      ((∏ᶠ p, γ p : ℂˣ) : ℂ) •
        haarFourier (a := a) rationalFiniteModel (normalizedHaar a) (eval v)) := by
  constructor
  · intro n v x
    obtain ⟨w, rfl⟩ := hsurj v
    have H : eval.comp ((R (lift (.trans n))).comp E) =
        (J rationalFiniteModel).comp (upperLinear n) := by
      apply linear_eq_of_classDelta
      intro r
      funext y
      change eval (R (lift (.trans n)) (E (classDelta r))) y =
        J rationalFiniteModel (twist n (classDelta r)) y
      rw [h.1, ← upper_tensor, upper_description, J_twist, classDelta_eval]
    have hh := congrFun (LinearMap.congr_fun H w) x
    change eval (R (lift (.trans n)) (E w)) x = J rationalFiniteModel (twist n w) x at hh
    rwa [J_twist, ← hE] at hh
  · intro v
    obtain ⟨w, rfl⟩ := hsurj v
    let g := ((∏ᶠ p, γ p : ℂˣ) : ℂ)
    have H : eval.comp ((R (lift .inv)).comp E) =
        g • (J rationalFiniteModel).comp fourierLinear := by
      apply linear_eq_of_classDelta
      intro r
      funext y
      change eval (R (lift .inv) (E (classDelta r))) y =
        g * J rationalFiniteModel (finiteFourier (classDelta r)) y
      rw [h.2, ← weyl_tensor γ hγ, weyl_description, ← classDelta_eval, ← adelic_fourier]
      rfl
    have hh := LinearMap.congr_fun H w
    change eval (R (lift .inv) (E w)) = g • J rationalFiniteModel (finiteFourier w) at hh
    rwa [adelic_fourier, ← hE] at hh

/-- Both comparisons with one inverse lift and one scalar. No stage
vectors, depths, level, or stage identifications enter this result. -/
theorem pair_of_tensor_generators
    {V₀ : Type*} [AddCommGroup V₀] [Module ℂ V₀]
    (E : (Grid a → ℂ) →ₗ[ℂ] V) (E₀ : (Grid referenceForm → ℂ) →ₗ[ℂ] V₀)
    (eval : V →ₗ[ℂ] (FiniteVectors → ℂ)) (eval₀ : V₀ →ₗ[ℂ] (FiniteVectors → ℂ))
    (heval : Function.Injective eval) (heval₀ : Function.Injective eval₀)
    (hE : ∀ w, eval (E w) = J rationalFiniteModel w)
    (hE₀ : ∀ w, eval₀ (E₀ w) = J rationalFiniteModel w)
    (hsurj : Function.Surjective E) (hsurj₀ : Function.Surjective E₀)
    (R : G →* Module.End ℂ V) (R₀ : G →* Module.End ℂ V₀)
    (π : G →* SL(2, ℤ)) (lift : Step → G) (hlift : ∀ s, π (lift s) = s.matrix⁻¹)
    (γ : FiniteIndexFamily) (hγ : WeilIndexProductFormula γ)
    (h : GeneratorTensorAction E eval R lift (indexAt γ (rationalDiagonal a)))
    (h₀ : GeneratorTensorAction E₀ eval₀ R₀ lift (indexAt γ (rationalDiagonal referenceForm))) :
    (∀ s, π (lift s) = s.matrix⁻¹) ∧
    (Function.Injective E ∧ IntertwinesGenerators E R lift (generatorScalar (realIndex (rationalDiagonal a)))) ∧
    (Function.Injective E₀ ∧ IntertwinesGenerators E₀ R₀ lift (generatorScalar (realIndex (rationalDiagonal a)))) := by
  obtain ⟨hT, hW⟩ := generator_descriptions E eval hE hsurj R lift _ (hγ _).1 h
  obtain ⟨hT₀, hW₀⟩ := generator_descriptions E₀ eval₀ hE₀ hsurj₀ R₀ lift _ (hγ _).1 h₀
  obtain ⟨hi, hi₀⟩ := index_products γ hγ a
  exact ⟨hlift, adelic_pair_comparison E E₀ eval eval₀ heval heval₀ hE hE₀ R R₀ lift
    _ _ _ hi hi₀ hT hT₀ hW hW₀⟩

#print axioms classDelta_eval
#print axioms sum_classDelta
#print axioms linear_eq_of_classDelta
#print axioms generator_descriptions
#print axioms pair_of_tensor_generators

end ZInQ.Manuscript.RC.Intertwine2
