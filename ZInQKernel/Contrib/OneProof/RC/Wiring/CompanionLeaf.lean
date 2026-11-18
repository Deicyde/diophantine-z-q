import ZInQKernel.Contrib.OneProof.RC.Wiring.Data

/-!
# Theorem 5.3, Lane RC0: the final companion, as a leaf

`CompanionLeaf W` (tex 2595–2603, with 2349–2352) and `companionTarget_of` (PROVED), kept in their
own module so that the leaves' providers (lane RC24's address leaf, batch 3's companion) can use them
without importing `RC/Wiring/Leaves.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **The final companion, as a leaf** (tex 2595–2603): in Branch 2, `k < 0` squarefree,
`k ≠ −1, −3`, its primes in the fixed support, `k ≡ 1 (mod 4)`, a unit square at every prime of `2N`,
prime to `h_*`, and `L_*(k) ≠ 0`. -/
def CompanionLeaf {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ¬ W.OddEmptyUnit → W.kfin < 0 ∧ Squarefree W.kfin ∧ W.kfin ≠ -1 ∧ W.kfin ≠ -3 ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.kfin → p ∈ W.S) ∧ W.kfin % 4 = 1 ∧
    (∀ p : ℕ, p.Prime → p ∣ 2 * CST.newformLevel (Ecurve ℓ) → UnitSquareAt p W.kfin) ∧
    IsCoprime W.kfin W.hstar ∧ W.Lstar W.kfin ≠ 0

/-- **`RCSteps.companion`** from the leaf and the normalization of `L_*` (PROVED). -/
theorem companionTarget_of {ℓ : ℕ} {W : WData ℓ} (hL : LstarTarget W.toRCData)
    (h : CompanionLeaf W) : CompanionTarget W.toRCData := fun hU => by
  obtain ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, hLk⟩ := h hU
  exact ⟨hneg, hsf, h1, h3, hS, h4, h2N, hcop, (hL _ hneg.ne).mp hLk⟩

end ZInQ.Manuscript.RC.Wiring
