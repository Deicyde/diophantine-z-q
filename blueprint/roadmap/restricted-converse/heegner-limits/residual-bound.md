---
declaration: theorem
origin: cited
---

# The reduced generic residual rank bound (5.1)

Fix $E$, an integer $A\ge0$ and a number $j$ of derivative labels. For the ring instances with
$\omega(k)\le A$, reduction to characteristic two followed by the support comparison and inversion of $t$
gives a generic residual model of total rank
$$N(E,A,j)\le56\,\omega(2N)+8A+56j+70.\tag{5.1}$$
The bound is independent of the number and sizes of the active primes and of $v_2(r_i-1)$. It bounds the
reduced generic model, not the whole retained support-comparison tuple before $t$ is inverted.

**Proof sketch.** Put $v=\omega(2N)$ and $m=v+1+j$, and let $T$ be the set of rational primes below the
places of $K$ over $2N$, the moving prime and the derivative primes, together with the primes ramified in
$K$; then $s=|T|\le v+A+1+j$ (5.1a). The residual module is $E[2]=\mathbb F_2^2$ with trivial action. The
Kummer sequence and the genus bound $\dim\operatorname{Cl}(\mathcal O_{K,S_T})[2]\le r-1$ ($r$ the number of
ramified primes) give $h^1(G_{K,S_T},\mathbb F_2)\le2s$ (5.1b), so the global complex has total rank at most
$8s+2$, by the Euler characteristic or, independently, by Schreier's bound. The local complexes have
$(h^0,h^1,h^2)=(2,4+2d_w,2)$, and a table of the local conditions (old Kummer, unramified, zero, full, and
strict, finite, singular and relaxed at derivative primes) gives per-prime costs $30$ at $2$, $24$ at other
old primes, $32$ at the moving prime and $14$ at an inert derivative prime, each at most $48$, with an
archimedean allowance of $4$. Finite free models give a cone rank at most the sum, and
$(8s+2)+48m+4\le56v+8A+56j+70$. After reduction mod two and inversion of $t$, every active comparison block is
acyclic, since there $A=D=((1+t)^{\pm e}-1)I$ is $t$ times a unit and $C=0$; over the local ring
$\mathbb F_2((t))[G]$ minimal ranks equal the augmented dimensions.

## Depends on

- [Finite free models and the inner limit](inner-limit.md)
- [Local conditions, the derived Kummer condition and duality](local-conditions.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:limits-residual-bound` (L4453–4648)

## Manuscript check

Checked line by line by AI review, with 18 checks by script, each with a negative control. Every count was
re-derived: (5.1a), the Kummer count and (5.1b), the genus bound (confirmed by composition of forms on all
1,217 imaginary quadratic fields with $|D|\le4000$), Hilbert 90, both routes to the global rank, every row of
the local table and the per-prime costs. The chain (5.1) holds with slack $8$ at the largest $s$, and the
transfer to the original support is correct. In the genus paragraph the radicand is called $d$, where the rest
of the section writes $k$. Not yet checked against the prints: Milne I.2.3, I.2.8, I.4.10, I.5.1 and Nekovář's
Proposition 7.8.8(ii).
