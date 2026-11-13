---
article_id: af_a7ef048d21dda4cff0b7a2de
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.redeiFormula
---

# Rédei's formula

Rédei's formula holds. Let $d$ be odd and squarefree, and let $B$ be a nonempty set of primes of
$d$ with $d_B=\prod_{p\in B}p\equiv7$, $3$ or $1\pmod8$. Then
$$g(d_B)\equiv g_d(B)\pmod 2:$$
the parity of the order of the subgroup of squares of the class group of $\mathbb Q(\sqrt{-d_B})$
is Rédei's $g$ of $B$, computed from the residue bits of the primes of $d$.

**Proof sketch.** Rédei's theorem on the 4-rank proves the 4-rank statement: for odd squarefree
$n>1$, $g(n)$ is odd if and only if the kernel of the Rédei matrix of $n$ is $\{0,e_n\}$. From the
4-rank statement, $g(d_B)\equiv g_d(B)\pmod2$ follows for every odd $d$ and every nonempty set $B$
of primes of $d$. The number $d_B$ is odd, squarefree and greater than $1$, and its primes are the
elements of $B$. The Rédei matrix of $d_B$ is the Laplacian $L_B$ of the bits of $d$, bordered by
the column $z_B$ exactly when $y(B)=0$. Its kernel is $\{0,e_{d_B}\}$ if and only if the kernel of
$(L_B\mid z_B)$ is trivial, and that holds if and only if $g_d(B)=1$. The argument uses neither the
squarefreeness of $d$ nor the congruence of $d_B$ modulo $8$.

## Depends on

- [The statement of Rédei's formula](redei-formula-statement.md)

## Proof depends on

- [Rédei's theorem on the 4-rank](four-rank/redei-theorem.md)
- [Rédei's formula from the 4-rank statement](bits/formula-from-four-rank.md)

## Sources

- [The chosen route](../../sources/redei-locators.md#the-chosen-route)
- [Rédei's formulas](../../sources/redei-locators.md#redeis-formulas)
- [Rédei 1934](../../sources/redei-locators.md#redei-1934)
- [Step 6: the 4-rank](../../sources/redei-locators.md#step-6-the-4-rank)
- [Step 8: the bridge](../../sources/redei-locators.md#step-8-the-bridge)
