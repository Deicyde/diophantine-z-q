---
article_id: af_e6eb235dc67654fd2297b3aa
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Redei.redeiEntry
---

# The Rédei matrix

Let $n$ be a natural number and $T_n$ its set of ramified primes: the primes of $n$, together with
$2$ unless $n\equiv3\pmod4$. The *Rédei matrix* $R$ of $n$ is the matrix over $\mathbb F_2$ with
rows indexed by the primes $q\mid n$ and columns by $T_n$, with entries
$$R_{q2}=[2/q],\qquad R_{qq}=\Bigl[\frac{n/q}{q}\Bigr]\quad(q\ne2),\qquad R_{qp}=[p/q]\quad(p\ne q,\ p\ne2),$$
where $[a/q]\in\mathbb F_2$ is the residue bit. A vector $e\in\mathbb F_2^{T_n}$ is *killed* by $R$
when $\sum_{p\in T_n}R_{qp}e_p=0$ for every prime $q\mid n$.

For odd squarefree $n$, $R$ is the matrix of the genus characters on the ambiguous classes:
$\chi_q(\psi(e))=\sum_{p\in T_n}R_{qp}e_p$
([the genus characters on the ambiguous classes](genus/characters-on-ambiguous-classes.md)).

## Depends on

- [The ramified primes and the ideals $\mathfrak p_p$](field/ramified-primes.md)
- [Residue bits](../route-k/residue-bits.md)

## Sources

- [Step 4: genus characters](../../sources/redei-locators.md#step-4-genus-characters)
