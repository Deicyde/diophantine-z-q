---
article_id: af_8b13d10a8bdd4e11fad94566
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Precision.Q0, ZInQ.Compiler.Precision.A0, ZInQ.Compiler.Precision.sixF, ZInQ.Compiler.Precision.bound, ZInQ.Compiler.Precision.contacts
---

# The precision height constant

The following natural numbers are defined by their displayed expressions and are never
evaluated:
$$\begin{aligned}
F_0&=324!, & D&=F_0\,3^{256F_0^4}, & G_0&=116064000000, & E_0&=10(DG_0)^2,\\
Q_0&=D^{DE_0}, & B_{\rm cm}&=D^2\,3^{21000D^2}+1, & C_{\rm cm}&=2B_{\rm cm}+4096(1028+5D+84000D^2),
\end{aligned}$$
$$A^{(0)}_{\rm ht}=2\cdot10^{13}\cdot\max\bigl(1,\ C_{\rm cm},\ Q_0^{17}\bigr).$$
With $F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)$ and $\mathcal C=\{0,-15,-20,-24,-30,-60\}$, the
*precision bound* of $(n,\kappa)\in\mathbb Z^2$ is the natural number
$$\mathcal B(n,\kappa)=A^{(0)}_{\rm ht}\,|\kappa F(n)|^{24}.$$

This is a definition. $A^{(0)}_{\rm ht}$ is the six-contact constant $H_6(S_{\rm ht})$ for
$S_{\rm ht}=\{p\le324\}$; the identification is a separate statement. Its symbol $F_0$ is
distinct from the polynomial $F$.

## Depends on

None.

## Sources

- [Section 4 height constants](../../../../sources/compiler-natural-locators.md#section-4-height-constants)
- [Section 10 decision predicate](../../../../sources/compiler-natural-locators.md#section-10-decision-predicate)
