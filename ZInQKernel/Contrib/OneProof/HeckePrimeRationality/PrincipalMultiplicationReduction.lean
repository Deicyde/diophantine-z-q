import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ActualPrincipalMultiplication

/-!
# Reduction of higher-weight multiplication to three small pairs and a degree gap

This is a conditional algebraic reduction on genuine principal modular forms,
not a proof of its input surjectivity statements. The geometric producer must
supply the gap statement and the three exceptional products independently.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane
open scoped TensorProduct

namespace ZInQ.Contrib.HeckePrimeRationality.PrincipalMultiplication

/-- A change of natural weight does not change the actual function. -/
def castWeight (N : ℕ) {a b : ℕ} (h : a = b) : Form N a →ₗ[ℂ] Form N b where
  toFun f := f.mcast (congrArg (fun n : ℕ => (n : ℤ)) h)
  map_add' := by intro f g; ext τ; rfl
  map_smul' := by intro c f; ext τ; rfl

@[simp] theorem castWeight_apply (N : ℕ) {a b : ℕ} (h : a = b) (f : Form N a) (τ : ℍ) :
    castWeight N h f τ = f τ := rfl

theorem castWeight_injective (N : ℕ) {a b : ℕ} (h : a = b) :
    Function.Injective (castWeight N h) := by
  intro f g he
  ext τ
  exact congrArg (fun u : Form N b => u τ) he

/-- Onto multiplication is symmetric, by commuting the actual tensor factors. -/
theorem multiplication_surjective_swap (N a b : ℕ)
    (hab : Function.Surjective (multiplication N a b)) :
    Function.Surjective (multiplication N b a) := by
  intro h
  obtain ⟨z,hz⟩ := hab (castWeight N (Nat.add_comm b a) h)
  refine ⟨TensorProduct.comm ℂ (Form N a) (Form N b) z, ?_⟩
  have heq : (castWeight N (Nat.add_comm b a)).comp
      ((multiplication N b a).comp (TensorProduct.comm ℂ (Form N a) (Form N b)).toLinearMap) =
      multiplication N a b := by
    apply TensorProduct.ext'
    intro f g
    ext τ
    exact mul_comm _ _
  apply castWeight_injective N (Nat.add_comm b a)
  exact (LinearMap.congr_fun heq z).trans hz

/-- Reassociation of actual products propagates two independently supplied onto maps. -/
theorem multiplication_surjective_reassociate (N a b c : ℕ)
    (hleft : Function.Surjective (multiplication N a (b + c)))
    (hright : Function.Surjective (multiplication N b c)) :
    Function.Surjective (multiplication N (a + b) c) := by
  let P := LinearMap.range (multiplication N (a + b) c)
  have hterm : ∀ (f : Form N a) (g : Form N (b + c)),
      castWeight N (Nat.add_assoc a b c).symm (product N a (b + c) f g) ∈ P := by
    intro f g
    obtain ⟨z,hz⟩ := hright g
    rw [← hz]
    clear hz g
    induction z using TensorProduct.inductionOn with
    | tmul u w =>
      refine ⟨product N a b f u ⊗ₜ[ℂ] w, ?_⟩
      ext τ
      exact mul_assoc _ _ _
    | add z w hz hw =>
      have he : castWeight N (Nat.add_assoc a b c).symm
          (product N a (b + c) f (multiplication N b c (z + w))) =
          castWeight N (Nat.add_assoc a b c).symm (product N a (b + c) f (multiplication N b c z)) +
          castWeight N (Nat.add_assoc a b c).symm (product N a (b + c) f (multiplication N b c w)) := by
        change castWeight N _ ((productLinear N a (b + c) f) (multiplication N b c (z + w))) = _
        rw [map_add, map_add, map_add]
        rfl
      rw [he]
      exact Submodule.add_mem P hz hw
  have hall : ∀ z : Form N a ⊗[ℂ] Form N (b + c),
      castWeight N (Nat.add_assoc a b c).symm (multiplication N a (b + c) z) ∈ P := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul f g => exact hterm f g
    | add z w hz hw => rw [map_add, map_add]; exact Submodule.add_mem P hz hw
  intro h
  obtain ⟨z,hz⟩ := hleft (castWeight N (Nat.add_assoc a b c) h)
  have hp := hall z
  rw [hz] at hp
  have he : castWeight N (Nat.add_assoc a b c).symm
      (castWeight N (Nat.add_assoc a b c) h) = h := by ext τ; rfl
  rw [he] at hp
  exact hp

/-- The only exceptional pairs needed after a gap producer are (2,2), (2,3), and (3,3).
All hypotheses below are actual, still-independent multiplication obligations. -/
theorem multiplication_all_of_gap_and_three_pairs (N : ℕ)
    (hgap : ∀ a b : ℕ, 2 ≤ a → a + 2 ≤ b →
      Function.Surjective (multiplication N a b))
    (h22 : Function.Surjective (multiplication N 2 2))
    (h23 : Function.Surjective (multiplication N 2 3))
    (h33 : Function.Surjective (multiplication N 3 3)) :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → Function.Surjective (multiplication N a b) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b ha hb
    by_cases ha2 : a = 2
    · subst a
      by_cases hb2 : b = 2
      · subst b; exact h22
      by_cases hb3 : b = 3
      · subst b; exact h23
      exact hgap 2 b (by omega) (by omega)
    by_cases ha3 : a = 3
    · subst a
      by_cases hb2 : b = 2
      · subst b; exact multiplication_surjective_swap N 2 3 h23
      by_cases hb3 : b = 3
      · subst b; exact h33
      by_cases hb4 : b = 4
      · subst b
        exact multiplication_surjective_swap N 4 3
          (multiplication_surjective_reassociate N 2 2 3 (hgap 2 5 (by omega) (by omega)) h23)
      exact hgap 3 b (by omega) (by omega)
    have ha4 : 4 ≤ a := by omega
    have hsmall : Function.Surjective (multiplication N (a - 2) b) :=
      ih (a - 2) (by omega) b (by omega) hb
    have hout := multiplication_surjective_reassociate N 2 (a - 2) b
      (hgap 2 (a - 2 + b) (by omega) (by omega)) hsmall
    have he : 2 + (a - 2) = a := by omega
    rw [he] at hout
    exact hout

end ZInQ.Contrib.HeckePrimeRationality.PrincipalMultiplication
