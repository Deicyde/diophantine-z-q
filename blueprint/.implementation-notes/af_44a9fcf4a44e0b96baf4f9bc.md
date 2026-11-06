# Implementation note: The assembly lemma

- Lean names: `ZInQ.Assembly.Pstar_spec`, `ZInQ.Assembly.assembly`.
- Draft:
  ```lean
  theorem Pstar_spec (hH : SixContactEstimate) (hPC : PoleCompleteness) (hMW : MordellWeilE)
      (h22 : FixedPrimePattern) (hCAT : CatalogueBound) :
      Syntax.Pstar.totalDegree < hyperoperation 4 2 7 ∧
      (∀ m : Fin 292890231905 →₀ ℕ, (Syntax.Pstar.coeff m).natAbs < hyperoperation 4 2 8) ∧
      ∀ q : ℚ, (∃ w : Fin 292890231904 → ℚ,
          MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cons q w) Syntax.Pstar = 0) ↔
        ∃ z : ℤ, (z : ℚ) = q
  theorem assembly (hH hPC hMW h22 hCAT) : FrozenTarget := ⟨Syntax.Pstar, Pstar_spec hH hPC hMW h22 hCAT⟩
  ```
  Then `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` (ZInQKernel/Main.lean) is
  `assembly hH hPC hMW h22 hCAT`.
- The bounds come from the size chapter's syntax-bounds theorem (hypothesis `hCAT`); the zero
  set from `ZInQ.Syntax.Pstar_zero_projection` and `exists_value_rel_iff`.
- Mathlib: `Nat.hyperoperation` (Mathlib/Data/Nat/Hyperoperation.lean), already imported by
  ZInQKernel/Target.lean.
- FINITE COMPUTATION: no. Difficulty: easy (~40 lines given the dependencies).

Shared conventions (assembly notes): namespace `ZInQ.Assembly`, files under
`ZInQKernel/Assembly/`. `RelT τ a` abbreviates `ZInQ.Syntax.Rel τ.poly τ.parameterCount
τ.witnessCount a` (syntax note for template semantics); codes are `ZInQ.iota : ℤ → Fin 5 → ℚ`
and `ZInQ.pointCode` (point-codes note); `genP0 : genCurve.toAffine.Point`. The hypothesis
quadruple `(hH : SixContactEstimate) (hPC : PoleCompleteness) (hMW : MordellWeilE)
(h22 : FixedPrimePattern)` is written `hyps`. The constants `A0`, `Bnk n κ`, `heightD` and
every power `4 ^ Bnk n κ` must stay symbolic: mark them `@[irreducible]`/`noncomputable` and
never use `decide`, `norm_num` evaluation or `#eval` on them.
