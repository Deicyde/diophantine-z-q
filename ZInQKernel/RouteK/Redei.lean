import ZInQKernel.RouteK.Redei.Field
import ZInQKernel.RouteK.Redei.Primes
import ZInQKernel.RouteK.Redei.Entry
import ZInQKernel.RouteK.Redei.Bridge

/-!
# Rédei's formula (`docs/research/redei-plan.md` §3.2), root module

* `Redei/Field.lean`: the field `ℚ(√−n)`, its automorphism, norms, `O ∩ ℚ = ℤ`;
* `Redei/Primes.lean`: the splitting trichotomy, the ramified primes `𝔭_p`, `(√−n) = Π 𝔭_p`,
  `𝔞 σ(𝔞) = (N𝔞)`;
* `Redei/Entry.lean`: the entries `R_{qp}` of the Rédei matrix (`redeiEntry`);
* `Redei/Bridge.lean` (step 8, imports `Redei/Kernel.lean`, step 7): `RedeiFormula` from the 4-rank
  statement `OddGClStatement` (`redeiFormula_of_oddGClStatement`), and
  `certifiedRankTYZRk_of_oddGClStatement`.
-/
