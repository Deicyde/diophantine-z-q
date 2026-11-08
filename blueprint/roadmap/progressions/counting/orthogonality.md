---
article_id: af_3ce179df4db6974f13ae2b42
declaration: theorem
origin: background
---

# Detecting a residue class by characters

Let $q\ge1$ and let $a$ be an integer coprime to $q$. For every function $f$ on the positive
integers and every finite set $S$ of positive integers,
$$\sum_{\substack{n\in S\\ n\equiv a\ (\mathrm{mod}\ q)}}f(n)
=\frac1{\varphi(q)}\sum_{\chi\bmod q}\overline{\chi(a)}\sum_{n\in S}\chi(n)f(n),$$
the outer sum running over the $\varphi(q)$ Dirichlet characters modulo $q$.

**Proof sketch.** Exchange the sums and apply the orthogonality relation
$\sum_\chi\overline{\chi(a)}\chi(n)=\varphi(q)$ if $n\equiv a\pmod q$ and $0$ otherwise,
valid because $a$ is a unit modulo $q$ (and $\overline{\chi(a)}=\chi(a)^{-1}$).

## Depends on

None.

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
