# Theorem 5.3 forward rank: scoped stop

The proposed auxiliary-field replacement for `Prints.kolyvagin` exceeds
the GLUE budget. Theorem 5.3 can reuse its existing newform route, but
still needs a CM trace dictionary for curves outside the pole family
and a comparison and descent of full Sha for the chosen quadratic
field. That changes one open GLUE field into at least two open GLUE
obligations in the lane. The actual count is unchanged.

The audit found 16 direct calls in ten theorems and two explicit
even-upper adapters. Genus comparisons can use rank bounds alone;
signed calibration passes both exact ranks and Sha finiteness. The
general rank-zero adapter has no restriction to the pole family.
The PR #163 variants are absent from the pinned base.

The route uses at most four print slots, including the existing BFH
statement. BFH(ii) supplies a nonzero twist value for analytic rank
one; BFH(i) would supply a simple twist zero for analytic rank zero.
The candidate height and conjugation readings supply trace non-torsion
and its sign under conjugation; the candidate Kolyvagin arithmetic
result supplies rank one and full Sha finiteness over the field.
Locators are UNVERIFIED. Check the 1988 paper's subclass and whether
the proposed 1990/1991 reading gives all primes, including two.
The manuscript cites an unrefereed preprint with a weak-Weil premise;
the Lean field uses a weaker modularity predicate. The retained
Shimura route also records a conjugate-eigenform typo in the print.
No new manuscript error was established.

No Lean declarations were added or checked on this stop. The
[report](../docs/research/kolyvagin-prints.md) records the proposed
source checks and unresolved comparisons; the
[consumer audit](../scratch/kolyvagin-prints/consumers.md) records each
application. Neither the pole hypothesis nor the Theorem 5.3 field
was changed.
