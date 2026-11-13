import ZInQKernel.Hypotheses.GreenTao
import Submission

/-!
# Green–Tao for the primes, from the vendored proof

`Submission.green_tao` (ThirdParty/GreenTao, vendored from Vilin97/Autoformalization, green-tao/,
Apache-2.0; see ThirdParty/GreenTao/NOTICE.md) proves the lean-eval statement
`LeanEval.NumberTheory.ContainsArbitraryAPs {p : ℕ | Nat.Prime p}`. The project predicate
`ZInQ.ContainsArbitraryAPs` has the same definition, so the two statements agree by unfolding.
-/

namespace ZInQ

/-- **Green–Tao** (Green–Tao 2008, Theorem 1.1): the primes contain arbitrarily long arithmetic
progressions. -/
theorem greenTao_primes : ContainsArbitraryAPs {p : ℕ | p.Prime} :=
  Submission.green_tao

end ZInQ
