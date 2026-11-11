import ZInQKernel.RouteK.Redei.Field
import ZInQKernel.RouteK.Redei.Primes
import ZInQKernel.RouteK.Redei.Entry
import ZInQKernel.RouteK.Redei.Ambiguous
import ZInQKernel.RouteK.Redei.Genus
import ZInQKernel.RouteK.Redei.Dirichlet
import ZInQKernel.RouteK.Redei.Bridge
import ZInQKernel.RouteK.Redei.FourRank

/-!
# Rédei's formula (`docs/research/redei-plan.md` §3.2), root module

* `Redei/Field.lean`: the field `ℚ(√−n)`, its automorphism, norms, `O ∩ ℚ = ℤ`;
* `Redei/Primes.lean`: the splitting trichotomy, the ramified primes `𝔭_p`, `(√−n) = Π 𝔭_p`,
  `𝔞 σ(𝔞) = (N𝔞)`;
* `Redei/Entry.lean`: the entries `R_{qp}` of the Rédei matrix (`redeiEntry`);
* `Redei/Ambiguous.lean`: Hilbert 90 for ideals, `psi`, `range_psi : im ψ = Cl[2]`,
  `card_ker_sq_le : #Cl[2] ≤ 2^{t−1}`;
* `Redei/Genus.lean`: the genus characters `chi n q` (`χ_q([𝔞]) = [N𝔞/q]`), `chi_ramIdeal`;
* `Redei/Dirichlet.lean`: split primes and the surjectivity of the genus characters
  (`exists_chi_eq`);
* `Redei/Bridge.lean` (step 8, imports `Redei/Kernel.lean`, step 7): `RedeiFormula` from the 4-rank
  statement `OddGClStatement` (`redeiFormula_of_oddGClStatement`), and
  `certifiedRankTYZRk_of_oddGClStatement`;
* `Redei/FourRank.lean` (step 6 and the assembly): `chi_psi`, genus theory by counting
  (`range_sq_eq_ker_chi : Cl² = ⋂ ker χ_q`, `card_ker_sq_eq : #Cl[2] = 2^{t−1}`), the 4-rank
  statement `odd_gCl_iff`, and the theorems `oddGClStatement` and
  `redeiFormula : RouteK.Rank5b.RedeiFormula`.
-/
