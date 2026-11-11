---
article_id: af_34cb527730a4387a2a10e58d
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.card_fpfi, ZInQ.RouteK.Rank5b.Sec3.fpfi, ZInQ.RouteK.Rank5b.Sec3.mem_fpfi, ZInQ.RouteK.Rank5b.Sec3.fpfi_invol, ZInQ.RouteK.Rank5b.Sec3.card_fpfi_pair
---

# Pairings are odd in number exactly on sets of even size

A *pairing* of a finite set $X$ is a fixed-point-free involution of $X$: a map $s:X\to X$ with
$s(x)\ne x$ and $s(s(x))=x$ for all $x\in X$, that is, a partition of $X$ into pairs. The number
of pairings of $X$ is odd if $|X|$ is even and even if $|X|$ is odd. For distinct $x,y\in X$, the
pairings $s$ of $X$ with $s(x)=y$ correspond bijectively to the pairings of $X\setminus\{x,y\}$.

**Proof sketch.** The bijection removes the pair $\{x,y\}$ from a pairing with $s(x)=y$, and puts
it back in a pairing of $X\setminus\{x,y\}$. The parity statement is by strong induction on $|X|$.
The empty set has one pairing and a point has none. For $|X|\ge2$ choose distinct $x,y\in X$ and
conjugate pairings by the transposition $\tau$ of $x$ and $y$, $s\mapsto\tau s\tau$. This is an
involution of the pairings of $X$, and its fixed points are exactly the pairings with $s(x)=y$. The
other pairings cancel in pairs, so the number of pairings of $X$ has the parity of the number of
pairings of $X\setminus\{x,y\}$, a set of size $|X|-2$, and induction applies.

## Depends on

None.

## Sources

- [Proposition 3.5](../../../sources/rank-5b-locators.md#proposition-35)
- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
