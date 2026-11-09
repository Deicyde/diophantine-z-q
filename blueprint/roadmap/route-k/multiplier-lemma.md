---
article_id: af_7b166a18caa5975513104fe5
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.exists_multiplier_pos, ZInQ.RouteK.exists_multiplier
---

# The multiplier lemma

Let $B$ be a nonzero rational. Then there is a positive divisor $m$ of $2730$ such that
$\beta=\mathrm{sqf}(mB)$ is odd and $|\beta|\equiv7\pmod8$. In particular every admissible $B$
has a signed divisor $m$ of $2730$ with $\beta$ odd and $|\beta|\equiv7\pmod8$.

**Proof sketch.** Write $B=\mathrm{sqf}(B)\,t^2$ and $\mathrm{sqf}(B)=2^fb'$ with $f\in\{0,1\}$ and
$b'$ odd. Multiplication by an odd class permutes the odd classes modulo $8$, so some
$m_0\in\{1,3,5,7\}$ has $m_0|b'|\equiv7\pmod8$; put $m=2^fm_0$. Then
$mB=m_0b'\,(2^ft)^2$, so $\beta=\mathrm{sqf}(m_0b')$ is odd. Since $m_0$ is $1$ or a prime,
$\beta$ differs from $m_0b'$ at most by an odd square factor, and odd squares are $\equiv1\pmod8$,
so $|\beta|\equiv m_0|b'|\equiv7\pmod8$. Admissibility is not needed beyond $B\ne0$.

## Depends on

- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](squarefree-part.md)

## Sources

- [Slots](../../sources/route-k-locators.md#slots)
