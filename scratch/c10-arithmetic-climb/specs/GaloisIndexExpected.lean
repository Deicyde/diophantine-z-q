import ZInQKernel.HDecomp.C10.C10

/-!
Independent target definitions for the Galois-index bridge.
These are specifications, not proofs of finite index or of a constructed global C10 bundle.
-/

namespace ClimbIndexExpected

noncomputable section

/-- The literal subgroup fixing the image of this particular number-field embedding. -/
def fixingEmbedding {L : Type} [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] GlueC10.Qbar) : Subgroup GlueC10.GQ where
  carrier := {σ | ∀ x : L, σ (ι x) = ι x}
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    change σ (τ (ι x)) = ι x
    rw [hτ x, hσ x]
  inv_mem' := by
    intro σ hσ x
    have h := congrArg σ.symm (hσ x)
    simpa using h.symm

/-- Exact index, with a fixed embedding and the actual absolute Galois carrier. -/
def IndexEquality : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] GlueC10.Qbar),
    (fixingEmbedding ι).index = Module.finrank ℚ L

/-- The scalar-index condition consumed by the S1/S2 finite-index step. -/
def IndexCastNonzero : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] GlueC10.Qbar)
    (k : Type) [Field k] [CharZero k],
    ((fixingEmbedding ι).index : k) ≠ 0

/-- A range identification is explicit here; an arbitrary group map does not supply it. -/
def RangeIndexCastNonzero : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] GlueC10.Qbar)
    (k : Type) [Field k] [CharZero k]
    (jj : Field.absoluteGaloisGroup L →* GlueC10.GQ),
    MonoidHom.range jj = fixingEmbedding ι →
      (((MonoidHom.range jj).index : ℕ) : k) ≠ 0

end
end ClimbIndexExpected
