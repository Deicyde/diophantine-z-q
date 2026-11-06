---
article_id: af_e11d54d67b0cabb84bc83eca
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.A0_eq_heightH6, ZInQ.Compiler.Precision.max_heightD_heightPrimes, ZInQ.Compiler.Precision.bound_eq_heightH6
---

# The precision constant is the six-contact constant

Let $S_{\rm ht}$ be the set of primes at most $324$. Then
$\max(D,\max S_{\rm ht},10^{12})=D$, and the six-contact constant at this argument is the
precision constant:
$$H_6(S_{\rm ht})=H_6(S_{\rm ht};D)=2\cdot10^{13}\max(1,C_{\rm cm},Q_D^{17})=A^{(0)}_{\rm ht},$$
where $Q_D=D^{DE_0}$ is computed as a real power. Consequently, for all
$(n,\kappa)\in\mathbb Z^2$, $\mathcal B(n,\kappa)=H_6(S_{\rm ht})\,|\kappa F(n)|^{24}$ is the bound
$B(n,\kappa)$ of the ordinary-value relation, and $R=D$ is an admissible argument of the
six-contact estimate for $S_{\rm ht}$.

**Proof sketch.** $\max S_{\rm ht}=317$, and $D\ge F_0=324!>10^{12}$, so the maximum is $D$
(no evaluation of $D$ is needed: $324!\ge10^{12}$ is a small finite check, for instance
$324!\ge20!>10^{12}$). The real power $D^{D E_0}$ with natural base and natural exponent
equals the natural power, so $Q_D=Q_0$, and the remaining expressions agree term by term.

## Depends on

- [The precision height constant](precision-height-constant.md)
- [The six-contact height estimate](../../../main/six-contact-estimate.md)

## Sources

- [Section 4 height constants](../../../../sources/compiler-natural-locators.md#section-4-height-constants)
- [Section 4 height prime set](../../../../sources/compiler-natural-locators.md#section-4-height-prime-set)
- [Section 10 decision predicate](../../../../sources/compiler-natural-locators.md#section-10-decision-predicate)
