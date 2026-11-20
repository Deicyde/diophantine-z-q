import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ActualInventory
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.BlockDescent

/-! The finite Fourier identities give exactly the spans used in the
scoped coordinate descent when the labelled columns are placed in a model. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open BlocksPerU
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- For one actual expansion it suffices to represent its own columns
in the inventory, with the level and character witnessed for each column.
This provides the complex span needed by the odd side's descent. -/
theorem block_span_of_inventory_labels
    {I J K L : Type} [Fintype I] [Field K] [AddCommGroup L]
    {ε : L →+ ZMod 2} {T : TypeData L ε} {m N : ℕ} {a : ℕ → ℂ}
    (A : CuspBlockExpansion m a) (Y : Inventory I J K T N) (κ : K →+* ℂ)
    (χ : (ZMod N)ˣ →* Kˣ) (place : ↥A.columns → I)
    (hlevel : ∀ c, Y.level (place c) ∣ m)
    (hchar : ∀ c, Y.χ (Y.origin (place c)) = χ)
    (hcoeff : ∀ (c : ↥A.columns) n, κ (Y.expansion (place c) n) = A.colCoeff c n) :
    a ∈ Submodule.span ℂ (blockColumns Y κ m χ) := by
  classical
  let v (c : ↥A.columns) : ℕ → ℂ := fun n => κ (Y.expansion (place c) n)
  have hv (c : ↥A.columns) : v c ∈ blockColumns Y κ m χ :=
    ⟨place c, hlevel c, hchar c, rfl⟩
  have ha : a = ∑ c : ↥A.columns, A.weight c.val • v c := by
    funext n
    rw [A.eq_coeff n]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, hcoeff]
    exact (Finset.sum_coe_sort _ _).symm
  rw [ha]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span (hv c))

end ZInQ.Manuscript.RC.EvenJoin
