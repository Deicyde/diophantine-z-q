import ZInQKernel.Contrib.CloudB3E1RingClass.ClassGroupMap
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST

/-!
# The order `ℤ + f𝒪_K` of this development is the tree's `conductorOrder`

`ringClassOrder f` (`Order.lean`) and the shared blueprint's `CST.conductorOrder K f` (the order
`ℤ + f𝒪_K` of the Cai–Shu–Tian print, `CloudB3RC53/Prints/CST.lean`) are the same
`NumberFieldOrder`. So the ring class fields, Artin classes and Frobenius statements here apply
verbatim to the tree's objects. Kind: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type} [Field K] [NumberField K]

/-- **`ringClassOrder f = CST.conductorOrder K f`.** Kind: PROVED. -/
theorem ringClassOrder_eq_conductorOrder (f : ℕ) [NeZero f] :
    ringClassOrder (K := K) f (NeZero.ne f) = ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K f := by
  refine NumberFieldOrder.ext (Subalgebra.ext fun x => ?_)
  change x ∈ (ringClassSubalgebra (K := K) f).map (IsScalarTower.toAlgHom ℤ (𝓞 K) K) ↔
    ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * (y : K)
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, ha⟩ := (mem_ringClassSubalgebra_iff f w).mp hw
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨a, y, ?_⟩
    have h : w = (a : 𝓞 K) + (f : 𝓞 K) * y := by rw [mul_comm, hy]; ring
    change ((w : 𝓞 K) : K) = _
    rw [h]
    push_cast
    rfl
  · rintro ⟨a, y, rfl⟩
    refine ⟨(a : 𝓞 K) + (f : 𝓞 K) * y, (mem_ringClassSubalgebra_iff f _).mpr
      ⟨a, ?_⟩, ?_⟩
    · rw [add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · change (((a : 𝓞 K) + (f : 𝓞 K) * y : 𝓞 K) : K) = _
      push_cast
      rfl

end ZInQ.Contrib.CloudB3E1RingClass
