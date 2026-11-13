---
article_id: af_e5ac6a3555ce4c3d96d3663b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.oddGClStatement, ZInQ.RouteK.Redei.odd_gCl_iff, ZInQ.RouteK.Redei.fourRankVec, ZInQ.RouteK.Redei.fourRankVec_ne_zero
---

# Rédei's theorem on the 4-rank

The 4-rank statement holds: for every odd squarefree $n>1$, the genus class number
$g(n)=|\mathrm{Cl}(\mathbb Q(\sqrt{-n}))^2|$ is odd if and only if every vector
$e\in\mathbb F_2^{T_n}$ killed by the Rédei matrix of $n$ is $0$ or $e_n$. Here $e_n$ is $1$ at the
primes of $n$ and $0$ at $2$, and it is nonzero for $n>1$.

**Proof sketch.** By the principal genus theorem and the values of the genus characters on the
ambiguous classes, $\psi(e)\in\mathrm{Cl}^2$ if and only if $\sum_pR_{qp}e_p=0$ for every prime
$q\mid n$. Also $\psi(e_n)=1$, the image of $\psi$ is $\mathrm{Cl}[2]$, and $g(n)=|\mathrm{Cl}^2|$
is odd if and only if $\mathrm{Cl}[2]\cap\mathrm{Cl}^2=1$.

- If $g(n)$ is odd and $e$ is killed by $R$, then $\psi(e)\in\mathrm{Cl}[2]\cap\mathrm{Cl}^2=1$. So
  $e\in\ker\psi$, which has two elements and contains $0$ and $e_n\ne0$; hence $e\in\{0,e_n\}$.
- Conversely, an element of $\mathrm{Cl}[2]\cap\mathrm{Cl}^2$ is $\psi(m)$ with $m$ killed by $R$.
  So $m\in\{0,e_n\}$, and $\psi(m)=1$.

## Depends on

- [The 4-rank statement](four-rank-statement.md)

## Proof depends on

- [The principal genus theorem](principal-genus.md)
- [The genus characters on the ambiguous classes](../genus/characters-on-ambiguous-classes.md)
- [When the subgroup of squares has odd order](odd-square-subgroup.md)
- [The 2-rank of the class group](two-rank.md)
- [The classes of the ramified primes](../genus/ramified-classes.md)
- [The ambiguous classes fill $\mathrm{Cl}[2]$](../genus/two-torsion.md)

## Sources

- [Step 6: the 4-rank](../../../sources/redei-locators.md#step-6-the-4-rank)
- [Rédei 1934](../../../sources/redei-locators.md#redei-1934)
- [Tian-Yuan-Zhang](../../../sources/redei-locators.md#tian-yuan-zhang)
