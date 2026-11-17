import ZInQKernel.Contrib.OneProof.JavanpeykarDict.Basic
import ZInQKernel.Contrib.OneProof.JavanpeykarDict.BelyiAlgebra
import ZInQKernel.Contrib.OneProof.JavanpeykarDict.FunctionField

/-! # javanpeykar-dict: `JavanpeykarBound` from two printed theorems

Task javanpeykar-dict (2026-11-16), report `docs/research/javanpeykar-dict.md`, scratch
`scratch/javanpeykar-dict/`.

**Target.** The bundle field `javanpeykarBound : ZInQ.HeightSplit.JavanpeykarBound`
(`ZInQKernel/OneProof/H/TailY.lean`), rated by the 11-16 dictionary pass a consequence of Javanpeykar 2014
Thm 1.1.1 through three dictionary steps: (1) the kernel's Jacobian (`IsJacobian`) against `Jac(X)`;
(2) `dim J` against the genus; (3) the kernel's `K`-rational `IsBelyiFunction` against a Belyi map of
`X` over `ℚ̄`.

**Result.** `javanpeykarBound_of_printed_stichtenoth : JavanpeykarPrinted →
ConstantFieldExtensionUnramified → JavanpeykarBound`, where
* `JavanpeykarPrinted` (`JavanpeykarDict/Basic.lean`) is Javanpeykar's Thm 1.1.1 for `X = X₀ ×_K ℚ̄`,
  with `Jac(X)` the degree-zero Picard scheme, `g` the genus of `X_ℚ̄` and a Belyi function of `X_ℚ̄`;
* `ConstantFieldExtensionUnramified` (`JavanpeykarDict/BelyiAlgebra.lean`) is Stichtenoth's Thm 3.6.3(a)
  (a constant field extension of a function field is unramified).
Steps (1) and (2) are proved in `Basic.lean`; step (3), `BelyiBaseChange`, is proved from Stichtenoth's
theorem in `FunctionField.lean` (function field of `X_ℚ̄` = `K(X) ⊗_K ℚ̄`) and `BelyiAlgebra.lean`
(degree and ramification under the constant field extension).

No `sorry`, no `axiom`. -/

namespace JavanpeykarDict

/-- **`javanpeykarBound` from the printed Javanpeykar leaf and Stichtenoth's theorem.** -/
theorem javanpeykarBound_of_printed_stichtenoth (hJ : JavanpeykarPrinted)
    (hS : ConstantFieldExtensionUnramified) : ZInQ.HeightSplit.JavanpeykarBound :=
  javanpeykarBound_of_printed hJ (belyiBaseChange_of_unramified hS)

end JavanpeykarDict
