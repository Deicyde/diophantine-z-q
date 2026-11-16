import ZInQKernel.Contrib.CloudB3SC5NewformReduction.Basic
import ZInQKernel.Contrib.G9.I4Layer

/-!
# The newform-character reduction in the G9 context

The G9 modular definitions are copies of the original `PkgI4` definitions on
identical Mathlib cusp-form objects. This typed theorem transports the closed
character-preserving helper to those exact definitions without a new hypothesis.
-/

noncomputable section

namespace CloudB3SC5NewformReduction

/-- The closed newform/character helper for the exact G9 normalized-eigenform
predicate used in the DS965Weak statement. -/
theorem exists_newform_preserving_nebentypus_G9
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (g : ZInQ.Contrib.G9.PkgI4.CF N k) (hN : 0 < N)
    (hg : ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ) :
    ∃ (M : ℕ) (_ : NeZero M) (hMN : M ∣ N) (f : HeckeRing.GL2.Newform M k),
      0 < M ∧ ZInQ.Contrib.G9.PkgI4.IsNewform f.toCuspForm (MulChar.ofUnitHom f.χ) ∧
      f.χ.comp (ZMod.unitsMap hMN) = χ.toUnitHom ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ZInQ.Contrib.G9.PkgI4.coeff f.toCuspForm p = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ M) (p : ZMod M) = χ (p : ZMod N) := by
  exact exists_newform_preserving_nebentypus N k χ g hN hg

end CloudB3SC5NewformReduction
