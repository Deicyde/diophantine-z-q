---
article_id: af_09f60d6f1e4ca8be36ec3b6a
declaration: structure
origin: cited
statement: formalized
lean: ZInQ.Contrib.CloudB3RC53.Prints
---

# The cited results

The proof of Theorem 5.3 in Lean takes four cited results as one structure:
- Breuil, Conrad, Diamond and Taylor, Theorem A: every elliptic curve over $\mathbb Q$ is modular;
- a consequence of Kolyvagin's Theorem 1 for analytic rank at most one: Kolyvagin assumes a weak Weil
  parametrization, the Lean statement assumes only modularity, and the passage between the two goes
  through Shimura's construction and Faltings' isogeny theorem;
- Dokchitser and Dokchitser, Theorem 1.8, for curves with a rational point of order two: the parity of the
  $2^\infty$-Selmer corank determines the root number. The Lean statement composes it with the
  identification of the root number with the sign of the functional equation, which is not part of the
  print;
- Cai, Shu and Tian, Theorem 1.1, in its split case: the explicit Gross–Zagier formula.

Each is stated over genuine definitions, with its locator in the print. Further cited results that the
proof uses enter as fields of [the remaining hypotheses](remaining-hypotheses.md).

## Depends on

None.

## Sources

- [Section 7](../../sources/manuscript.md#section-7)
