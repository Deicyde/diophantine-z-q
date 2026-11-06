---
article_id: af_7ed9789bc99c3c2b91251ccd
declaration: theorem
origin: cited
---

# Correctness of the wrapper

Let $\Pi$ be a primitive register program in final-halt form with registers below $N\ge5$.
For every $x\in\mathbb N$,
$$W(\Pi)\text{ halts on }x\iff\Pi\text{ halts on }\operatorname{decode}_5(x).$$
In particular $W(\Pi)$ halts on $\operatorname{encode}_5(\mathbf c)$ iff $\Pi$ halts on $\mathbf c$, for every
$\mathbf c\in\mathbb N^5$.

**Proof sketch.** By the unpairing-loop invariant, the run of $W(\Pi)$ from $(0,R)$ with $R_0=x$
reaches $(\ell,R')$ after finitely many steps, where $R'_i$ is the $i$-th component of
$\operatorname{decode}_5(x)$ for $i<5$ and $R'_i=0$ otherwise: old work registers stay zero and the
scratch registers, lying above the registers of $\Pi$, are cleared. From there, the map
$(p,R)\mapsto(p+\ell,R)$ sends the run of $\Pi$ on $\operatorname{decode}_5(x)$ step for step onto the run of
$W(\Pi)$, halting configurations to halting configurations (states $\ge m$ of $\Pi$ go to states
$\ge\ell+m$, beyond $W(\Pi)$). So the two runs halt together.

## Depends on

- [The wrapper and the program literal](wrapper.md)
- [Cantor pairing and unpairing](cantor-unpairing.md)

## Sources

- [Section 10.3 unpairing wrapper](../../../../sources/compiler-translation-locators.md#section-103-unpairing-wrapper)
