---
article_id: af_283e55ff69526472af5e3d36
declaration: def
origin: bridged
statement: formalized
lean: HDec.HSyn.OpenGlue8.nvLocalInertia
---

# Local inertia of tame covers of the line

The *local inertia statement* is the following assertion. Let $p$ be a prime and $E$ a finite Galois
extension of $\mathbb Q(X)$ of degree less than $p$ whose finite branch points lie in a set $S$ of
rational numbers that are $p$-integral and distinct modulo $p$. Let $b\in S$ be a branch point such
that the residue fields of $E$ above $X-b$ are unramified at $p$. Then every element of an inertia
group at a prime of $E$ above $p\mathbb Z[X]$ is conjugate to an element of an inertia group above
$X-b$.

No published statement has this form; it is a step of the project's own argument. It is the third
step of the project's Lemma NV, through which the proof obtains an unramified vertical prime above
each prime $p>324$ in the Hecke cover. A sketch derives it from Abhyankar's lemma along a divisor
with normal crossings (SGA 1 XIII 5.3), which is proved here only over a discrete valuation ring,
and from Zariski–Nagata purity, which is proved here in dimension $2$; the derivation is not yet
part of the proof. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Local inertia of tame covers](../../sources/height-decomposition-locators.md#local-inertia-of-tame-covers)
