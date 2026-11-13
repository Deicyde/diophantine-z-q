---
article_id: af_3ce179df4db6974f13ae2b42
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.classSum, ZInQ.Progressions.twistedSum, ZInQ.Progressions.classSum_eq_sum_twistedSum, ZInQ.Progressions.classSum_sub_eq, ZInQ.Progressions.dirichletCharacter_apply_inv_of_isUnit
---

# Detecting a residue class by characters

Let $q\ge1$ and let $a$ be a unit modulo $q$, with inverse $a^{-1}$ modulo $q$. For real $x$
put
$$S_a(x)=\sum_{\substack{n\le x\\ n\equiv a\ (\mathrm{mod}\ q)}}\frac{\Lambda(n)}{n},\qquad
S_\chi(x)=\sum_{n\le x}\frac{\chi(n)\Lambda(n)}{n}$$
for each Dirichlet character $\chi$ modulo $q$. Then
$$S_a(x)=\frac1{\varphi(q)}\sum_{\chi\bmod q}\chi(a^{-1})\,S_\chi(x),$$
the sum running over the $\varphi(q)$ Dirichlet characters modulo $q$, where
$\chi(a^{-1})=\chi(a)^{-1}=\overline{\chi(a)}$. Consequently, for all real $x,y$,
$$S_a(x)-S_a(y)=\frac1{\varphi(q)}\,\mathrm{Re}\sum_{\chi\bmod q}\chi(a^{-1})
\bigl(S_\chi(x)-S_\chi(y)\bigr).$$

**Proof sketch.** Exchange the sums and apply the orthogonality relation
$\sum_\chi\chi(a^{-1})\chi(n)=\varphi(q)$ if $n\equiv a\pmod q$ and $0$ otherwise. Subtract
the identities at $x$ and $y$; the left side is real, so it equals the real part of the right
side.

## Depends on

None.

## Sources

- [Apostol, Chapter 6](../../../sources/progressions-locators.md#apostol-chapter-6)
