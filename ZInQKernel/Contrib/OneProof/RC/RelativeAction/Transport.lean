import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Unipotents
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.LocalFactor

/-! Generator comparison and its propagation, on-the-spot (c) for the
compatible finite lifts in tex 8989–9015. -/

noncomputable section

namespace ZInQ.Manuscript.RC.RelativeAction

open OldStageLaw CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups BigOperators

variable {a : Fin 3 → ℕ}
variable {G V V₀ : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V₀] [Module ℂ V₀]

/-- Extend a rectangular coset table by zero. The residue map assigns none
off the dual rectangular lattice. -/
def extendCosets {X : Type*} (res : X → Option (Grid a)) :
    (Grid a → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun w x := (res x).elim 0 w
  map_add' v w := by
    funext x
    cases hx : res x <;> simp [hx]
  map_smul' c v := by
    funext x
    cases hx : res x <;> simp [hx]

theorem extendCosets_injective {X : Type*} (res : X → Option (Grid a))
    (h : ∀ r, ∃ x, res x = some r) : Function.Injective (extendCosets res) := by
  intro v w he
  funext r
  obtain ⟨x, hx⟩ := h r
  simpa [extendCosets, hx] using congrFun he x

/-- The upper generator comparison on a coset extension reduces to the
value of the local product phase on occupied cosets; values off the grid
union do not enter. -/
theorem extendCosets_twist {X : Type*} (res : X → Option (Grid a)) (n : ℤ)
    (w : Grid a → ℂ) (phase : X → ℂ)
    (h : ∀ x r, res x = some r → phase x = kernel (n : ℂ) (energy r)) :
    extendCosets res (twist n w) = fun x => phase x * extendCosets res w x := by
  funext x
  cases hx : res x with
  | none => simp [extendCosets, hx]
  | some r => simp [extendCosets, hx, twist, h x r hx]

variable [∀ i, NeZero (2 * a i)]

/-- The missing model comparison can be checked on the displayed Fourier
and phase operators. It makes no assumption about a weight or stabilizer.
Use the same lifted generators and scalar function on the two spaces. -/
def IntertwinesGenerators (J : (Grid a → ℂ) →ₗ[ℂ] V)
    (R : G →* Module.End ℂ V) (lift : Step → G) (μ : Step → ℂˣ) : Prop :=
  (∀ w, J (finiteFourier w) = (μ .inv : ℂ) • R (lift .inv) (J w)) ∧
  (∀ n w, J (twist n w) = (μ (.trans n) : ℂ) • R (lift (.trans n)) (J w))

/-- Word operators act in reverse order, as do the lifts of the inverse
generators. -/
def inverseLiftWord (lift : Step → G) : List Step → G
  | [] => 1
  | s :: l => inverseLiftWord lift l * lift s

theorem inverseLiftWord_projects (π : G →* SL(2, ℤ)) (lift : Step → G)
    (h : ∀ s, π (lift s) = s.matrix⁻¹) (l : List Step) :
    π (inverseLiftWord lift l) = (wordMatrix l)⁻¹ := by
  induction l with
  | nil => simp [inverseLiftWord, wordMatrix]
  | cons s l ih => simp [inverseLiftWord, wordMatrix, ih, h, mul_inv_rev]

theorem intertwines_word (J : (Grid a → ℂ) →ₗ[ℂ] V)
    (R : G →* Module.End ℂ V) (lift : Step → G) (μ : Step → ℂˣ)
    (h : IntertwinesGenerators J R lift μ) (l : List Step) (w : Grid a → ℂ) :
    J (wordAction l w) = (((l.map μ).prod : ℂˣ) : ℂ) • R (inverseLiftWord lift l) (J w) := by
  induction l generalizing w with
  | nil => simp [wordAction, inverseLiftWord]
  | cons s l ih =>
    have hs (v : Grid a → ℂ) :
        J (wordAction [s] v) = (μ s : ℂ) • R (lift s) (J v) := by
      cases s with
      | inv => exact h.1 v
      | trans n => exact h.2 n v
    have hf : wordAction (s :: l) w = wordAction l (wordAction [s] w) := by cases s <;> rfl
    rw [hf, ih, hs]
    simp only [inverseLiftWord, List.map_cons, List.prod_cons, Units.val_mul, map_mul,
      Module.End.mul_apply, LinearMap.map_smul, smul_smul, mul_comm]

/-- Reflect a pair of eigen-equations for one lifted operator to the
literal pair of table identities. Injectivity is required on each grid. -/
theorem paired_of_lifted_eigen {N : ℕ} (ξ : (ZMod N)ˣ →* ℂˣ) (w : Grid a → ℂ)
    (J : (Grid a → ℂ) →ₗ[ℂ] V) (J₀ : (Grid referenceForm → ℂ) →ₗ[ℂ] V₀)
    (hJ : Function.Injective J) (hJ₀ : Function.Injective J₀)
    (R : G →* Module.End ℂ V) (R₀ : G →* Module.End ℂ V₀)
    (lift : Step → G) (μ : Step → ℂˣ)
    (hT : IntertwinesGenerators J R lift μ) (hT₀ : IntertwinesGenerators J₀ R₀ lift μ)
    (l : List Step) (h : wordMatrix l ∈ Gamma0 N) (lam : ℂ)
    (he₀ : R₀ (inverseLiftWord lift l) (J₀ referenceWeight) = lam • J₀ referenceWeight)
    (he : R (inverseLiftWord lift l) (J w) =
      ((ξ ((Gamma0Map N).toHomUnits ⟨wordMatrix l, h⟩) : ℂ) * lam) • J w) :
    PairedActionAt ξ w l := by
  refine ⟨h, (((l.map μ).prod : ℂˣ) : ℂ) * lam, hJ₀ ?_, hJ ?_⟩
  · rw [intertwines_word J₀ R₀ lift μ hT₀, he₀, LinearMap.map_smul, smul_smul]
  · rw [intertwines_word J R lift μ hT, he, LinearMap.map_smul, smul_smul]
    congr 1
    ring

/-- An evaluated product of local functions scales by the product of the
local eigenvalues; there is no Haar factor in this operation. -/
theorem product_eigen {P : Type*} [Fintype P] {X : P → Type*}
    (v t : ∀ p, X p → ℂ) (lam : P → ℂ) (h : ∀ p, t p = lam p • v p) (x : ∀ p, X p) :
    (∏ p, t p (x p)) = (∏ p, lam p) * ∏ p, v p (x p) := by
  simp_rw [h, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

#print axioms extendCosets_injective
#print axioms extendCosets_twist
#print axioms inverseLiftWord_projects
#print axioms intertwines_word
#print axioms paired_of_lifted_eigen
#print axioms product_eigen

end ZInQ.Manuscript.RC.RelativeAction
