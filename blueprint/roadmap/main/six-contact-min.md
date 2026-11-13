---
article_id: af_c1959968703bfe1fee90f347
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.SixContactMin
---

# The minimal height hypothesis

Let $\mathcal C$, $h$, $M_S$, $D$, $E_0$ and $C_{\rm cm}$ be as in the six-contact height
estimate, and put
$$H_6(D)=2\cdot10^{13}\max\bigl(1,C_{\rm cm},Q_D^{17}\bigr),\qquad Q_D=D^{DE_0}.$$
Let $S_{\rm mul}=S_{\rm ht}\cup\mathcal H\cup\{p\text{ prime}:p\mid c_*\}$ be the prime set of the
multiplication certificate: $S_{\rm ht}$ is the set of primes at most $324$, $\mathcal H$ is the
prime catalogue (the first twenty-two primes greater than $324$ in each unit class modulo
$W=4P_s$), and $c_*=4M_0$, where $M_0$ is the least formal multiple of $N_s$.

The minimal height hypothesis is the assertion that for every $u\in\mathbb Q\setminus\mathcal C$,
$$h(u)\le H_6(D)\,M_{S_{\rm mul}}(u)^{24}.$$

This is the instance $S=S_{\rm mul}$, $R=D$ of the six-contact estimate, and it is the only
form of that estimate the proof of the main theorem uses: the precision bound of the value
relation needs it at $S_{\rm ht}\subseteq S_{\rm mul}$, where $M_{S_{\rm mul}}(u)$ divides
$M_{S_{\rm ht}}(u)$, and the finite box of multiplication soundness needs it at $S_{\rm mul}$.
The constant $H_6(D)$ is the precision constant $A^{(0)}_{\rm ht}$. Here it is a hypothesis of
the main theorem.

## Depends on

- [The six-contact height estimate](six-contact-estimate.md)
- [Prime sets and clearing exponents of the multiplication certificate](../multiplication/certificate/constants.md)

## Sources

- [Theorem 4.1](../../sources/manuscript.md#theorem-41)
