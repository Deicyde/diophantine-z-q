---
article_id: af_8d0940f0253e8b9217773a3c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Stages.exists_detector_stages
---

# (3.7): arbitrarily advanced stages

Assume Serre's open image theorem (`SerreThm3`, a printed result that is not one of [the cited
results](../printed-results.md)). Let $\ell>0$, $D_w>0$ and $h_*<0$, let $A=E_\ell^{(D_w)}$, assumed
without complex multiplication, let $Q\in A(\mathbb Q)$ have infinite order, and let $F_0$ be a finite
Galois extension of $\mathbb Q$ containing $\sqrt{D_w}$ and $\sqrt{h_*}$. Then there are $a\ge0$, an
element $\sigma\in G_{\mathbb Q}$ acting on $T_2E_\ell$ as complex conjugation, and a surjective
$\mathbb Z_2$-linear row $b$ on $T_2A$, fixed by $\sigma$, with $b(c_Q(\sigma^2))=2^{a+1}$ for the
Kummer cocycle $c_Q$ of $Q$. Moreover, for every finite set $B$ of primes there is a sequence of
distinct primes $\ell_0\notin B$, of good reduction for $E_\ell$ and $A$, at the precisions
$M=a+2,a+3,\dots$, each with a Frobenius element $g$ at $\ell_0$ such that $g=\sigma$ on the field of
$2^M$-division points of $Q$, $E_\ell$ and $A$ over $F_0$, and
$$\rho(g)\equiv\rho(\sigma)\pmod{2^M}\ \text{on }T_2E_\ell\text{ and }T_2A,\quad
\ell_0\equiv-1\pmod{2^M},\quad\Bigl(\frac{D_w}{\ell_0}\Bigr)=1,\quad\Bigl(\frac{h_*}{\ell_0}\Bigr)=-1.\tag{3.7}$$

The detector value $2^{a+1}$ is $2^{c_w}$ with $c_w=a+1<M$. The last clause of the manuscript's (3.7),
$v_2\lambda_{M}(\bar Q)=c_w$ for the finite-field Kummer map at $\ell_0$, is Appendix F's (O.2) and is
not part of this theorem; the Lean proof of Theorem 5.3 derives it from the detector outputs, which are
fields of `PreLeaves.odd_staged` in [the remaining hypotheses](../remaining-hypotheses.md). The
manuscript applies the theorem to $Q=LP^{\rm gen}_{D_w}$.

**Proof sketch.** Serre's theorem and the absence of complex multiplication make the Kummer translation
image of $Q$ a full lattice. This gives an element $h$, trivial on $F_0$ and on $T_2A$, whose translation
is $2^at_0$ for a vector $t_0$ with $b(t_0)=1$ for a row $b$ fixed by complex conjugation $C$; put
$\sigma=hC$, so that $b(c_Q(\sigma^2))=2^{a+1}$. Since $D_w>0>h_*$, $\sigma$ fixes $\sqrt{D_w}$ and
moves $\sqrt{h_*}$. Finite Chebotarev gives infinitely many primes whose Frobenius agrees with $\sigma$
on each finite level, and a recursion with a growing exclusion set gives one sequence.

## Depends on

None.

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
