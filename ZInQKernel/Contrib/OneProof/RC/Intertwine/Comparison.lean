import ZInQKernel.Contrib.OneProof.RC.Intertwine.Fourier

/-! Common scalars and lifts, and injective transport back to the two tables
(tex 8726–8807 and 8996–9015). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine

open OldStageLaw RelativeAction CongruenceSubgroup
open scoped BigOperators

variable {A : Type*} [CommRing A] [Algebra ℚ A] {I₀ : Subring A}
variable (M : IntegralModel I₀)
variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
variable [MeasurableSpace (Fin 3 → A)] [MeasurableAdd (Fin 3 → A)]
variable {G V V₀ : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V₀] [Module ℂ V₀]

/-- Same positive real Weil index and global product one force the same
finite scalar for either form. -/
theorem common_weyl_scalar (realIndex finiteIndex finiteIndex₀ : ℂˣ)
    (h : realIndex * finiteIndex = 1) (h₀ : realIndex * finiteIndex₀ = 1) :
    finiteIndex = finiteIndex₀ :=
  mul_left_cancel (h.trans h₀.symm)

def generatorScalar (realIndex : ℂˣ) : Step → ℂˣ
  | .inv => realIndex
  | .trans _ => 1

/-- The model's actions by a phase and a scalar times a Haar integral
imply the two grid identities. The model may live in a subspace of functions. -/
theorem comparison
    (E : (Grid a → ℂ) →ₗ[ℂ] V) (eval : V →ₗ[ℂ] ((Fin 3 → A) → ℂ))
    (heval : Function.Injective eval) (hE : ∀ w, eval (E w) = J M w)
    (ν : MeasureTheory.Measure (Fin 3 → A)) [ν.IsAddLeftInvariant]
    (hL : MeasurableSet (lattice I₀ : Set (Fin 3 → A)))
    (hi : ∀ y, MeasureTheory.Integrable (latticeCharacter (a := a) M y) ν)
    (hvol : (ν.real (lattice I₀) : ℂ) = ∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ))
    (R : G →* Module.End ℂ V) (lift : Step → G) (realIndex : ℂˣ)
    (hT : ∀ n v x, eval (R (lift (.trans n)) v) x =
      finitePhase M (-(n : A) * quad a x) * eval v x)
    (hW : ∀ v, eval (R (lift .inv) v) =
      (↑(realIndex⁻¹) : ℂ) • haarFourier (a := a) M ν (eval v)) :
    Function.Injective E ∧ IntertwinesGenerators E R lift (generatorScalar realIndex) := by
  refine ⟨fun v w h => J_injective M (by rw [← hE v, ← hE w, h]), ?_, ?_⟩
  · intro w
    apply heval
    rw [LinearMap.map_smul, hW, hE, hE, J_fourier M ν hL hi hvol]
    simp [generatorScalar, smul_smul, ← Units.val_mul]
  · intro n w
    apply heval
    rw [LinearMap.map_smul, hE, J_twist]
    funext x
    simp [generatorScalar, hT, hE]

/-- Apply the two common comparisons to one lifted eigenpair. The remaining
ratios here are local arithmetic inputs for one word at a time. -/
theorem weighted_table_of_common_comparison {N : ℕ} (ξ : (ZMod N)ˣ →* ℂˣ)
    (w : Grid a → ℂ)
    (E : (Grid a → ℂ) →ₗ[ℂ] V) (E₀ : (Grid referenceForm → ℂ) →ₗ[ℂ] V₀)
    (R : G →* Module.End ℂ V) (R₀ : G →* Module.End ℂ V₀)
    (lift : Step → G) (realIndex : ℂˣ)
    (h : Function.Injective E ∧ IntertwinesGenerators E R lift (generatorScalar realIndex))
    (h₀ : Function.Injective E₀ ∧ IntertwinesGenerators E₀ R₀ lift (generatorScalar realIndex))
    (l : List Step) (hl : wordMatrix l ∈ Gamma0 N) (lam : ℂ)
    (he₀ : R₀ (inverseLiftWord lift l) (E₀ referenceWeight) = lam • E₀ referenceWeight)
    (he : R (inverseLiftWord lift l) (E w) =
      ((ξ ((Gamma0Map N).toHomUnits ⟨wordMatrix l, hl⟩) : ℂ) * lam) • E w) :
    PairedActionAt ξ w l :=
  paired_of_lifted_eigen ξ w E E₀ h.1 h₀.1 R R₀ lift _ h.2 h₀.2 l hl lam he₀ he

#print axioms common_weyl_scalar
#print axioms comparison
#print axioms weighted_table_of_common_comparison

end ZInQ.Manuscript.RC.Intertwine
