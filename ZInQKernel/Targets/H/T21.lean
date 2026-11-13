import ZInQKernel.HDecomp.Conductor.Breaks

/-!
# First H batch: T21, the global different exponent bound

Proposed closed target, reserved provider `ZInQ.Contrib.H.T21_holds`.
This registration draft is not mathematical or protected Astra acceptance.

The statement body preserves PR #41's `ZInQ.Targets.H.T21` at
`2757349fbd8ca613340b679bbd149f78c2baba6b`, from
`GlueConductor.SerreDifferentBound` in the frozen reference `Leaves.lean` at
`48b5f075e5509678c84685f0d1ec53febd10b1e5`.
Reference file SHA-256: `99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`.

Reference: Serre, Local Fields, III section 6, remark after Proposition 13
(numbering subject to source review): v_L(D_L/K) ≤ e - 1 + v_L(e).
For K = Q_p the integer e has valuation e*v_p(e). The exact global statement was
read in MIT 18.785 Fall 2021 Lecture 12, Theorem 12.27, and Conrad, The Different
Ideal, section 4, by a preliminary independent reviewer. Separable residue fields
and finite separability are automatic for number fields over Q; no Galois premise
is needed. The Serre locator itself remains unverified.
The target is over the
original number field and its global different ideal: a local-field inequality
needs explicit localization/completion, ideal-factorization and ramification-index
transport. No local comparison is treated as a proof of the global statement.
All baseline declarations and the existing equivalent leaf remain unchanged.
-/

open NumberField

namespace ZInQ.Targets.H

/-- Exact global prime-power nondivisibility form of the different bound. -/
def T21 : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)

/-- The original baseline predicate is preserved definitionally, not replaced. -/
theorem T21_iff_baseline : T21 ↔ GlueConductor.SerreDifferentBound := Iff.rfl

end ZInQ.Targets.H
