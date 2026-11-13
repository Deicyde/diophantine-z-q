---
article_id: af_4920ef18243f471dccec8ce1
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.tests_to_congruence
---

# From the local tests to the congruence

Let $p>324$ be a prime, $\mathfrak p$ a prime of
$\mathbb Z[s]$ above $p$, and $c\in\mathbb Z$ with $p\nmid c$. Let $n_1,n_2,n_3\in\mathbb Z$ and
$h,z_1,z_2,z_3\in\mathbb Z$ with $h\ne0$, $h\ne c$, and let
$\tau=\tau(h,z;\,c,cn_1,cn_2,cn_3)$ be the twelve test values. If
$$v_{\mathfrak p}(\tau_j)\ge1\quad(1\le j\le8)\qquad\text{and}\qquad v_{\mathfrak p}(\tau_j)\ge25\quad(9\le j\le12),$$
then $p^{25}\mid n_1n_2-n_3$.

In the certificate $c=c_*$, and $p\nmid c_*$ holds for every $p\notin S_{\rm mul}$.

**Proof sketch.** Let $\mathfrak q=\sigma\mathfrak p$ (possibly $\mathfrak q=\mathfrak p$ if $p$ is
inert), $v=v_{\mathfrak p}$, and let $\lambda_{\mathfrak p},\lambda_{\mathfrak q}$ be the formal
logarithms over the two completions. With $H=[h]P_0$, $U_i=[z_i]P_0$, $V_0=[h-c]P_0$,
$V_i=[z_i-cn_i]P_0$:

1. *The points lie in the formal groups.* $v_{\mathfrak p}(\rho(Q))\ge1$ means $Q=O$ or
   $v_{\mathfrak p}(x(Q))<0$. Tests $1$-$4$ put $H,U_i$ in $E_1(K_{\mathfrak p})$; since
   $v_{\mathfrak p}(\sigma y)=v_{\mathfrak q}(y)$, tests $5$-$8$ put $V_0,V_i$ in
   $E_1(K_{\mathfrak q})$.
2. *Full-log ratios.* By the full-logarithm ratio lemma,
   $\lambda_{\mathfrak p}(U_i)=\alpha_i\lambda_{\mathfrak p}(H)$ and
   $\lambda_{\mathfrak q}(V_i)=\beta_i\lambda_{\mathfrak q}(V_0)$ with the rational numbers
   $\alpha_i=z_i/h$ and $\beta_i=(z_i-cn_i)/(h-c)$.
3. *Truncated ratios.* By the truncation error at $p>324$, $A_i=\alpha_i\,u_i$ in
   $K_{\mathfrak p}$ and $B_i=\beta_i\,u_i'$ in $K_{\mathfrak q}$ with units $u_i,u_i'$ congruent to
   $1$ modulo valuation $28$ (when $U_i=O$ or $V_i=O$ the ratio is $0$ and the claims below
   are trivial).
4. *Integrality.* Since $p\nmid c$, one of $h,h-c$ is a $p$-adic unit. If $p\nmid h$, then
   $\alpha_i$ is $p$-integral, so $A_i$ is $\mathfrak p$-integral with
   $v_{\mathfrak p}(A_i-\alpha_i)\ge28$; tests $9$-$11$ give $v_{\mathfrak p}(\sigma B_i)\ge0$, that is
   $v_{\mathfrak q}(B_i)\ge0$, so $\beta_i=B_iu_i'^{-1}$ is $p$-integral and
   $v_{\mathfrak q}(B_i-\beta_i)\ge28$. If $p\mid h$, argue symmetrically from $\beta_i$.
   Only now do the relative errors give absolute congruences: in both cases $\alpha_i,\beta_i$
   are $p$-integral, $A_i\equiv\alpha_i$ modulo valuation $28$ at $\mathfrak p$, and
   $\sigma B_i\equiv\beta_i$ modulo valuation $28$ at $\mathfrak p$ (as $\beta_i$ is rational).
5. *The congruence.* With test $8+i$: $v_{\mathfrak p}(A_i-\beta_i)\ge25$. Hence
   $z_i-hA_i=h(\alpha_i-A_i)$ and $z_i-cn_i-(h-c)A_i=(h-c)(\beta_i-A_i)$ have valuation at
   least $25$, and so does their difference $c(n_i-A_i)$; as $p\nmid c$,
   $v_{\mathfrak p}(n_i-A_i)\ge25$. Finally
   $n_1n_2-n_3=(n_1-A_1)n_2+A_1(n_2-A_2)+(A_1A_2-A_3)+(A_3-n_3)$ with $A_1$ integral and test
   $12$ gives $v_p(n_1n_2-n_3)\ge25$.

## Depends on

- [The twelve local tests](../certificate/twelve-tests.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../local/primes-above-p.md)

## Proof depends on

- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](../local/formal-group.md)
- [Full-logarithm ratios of multiples of $P_0$](../local/logarithm-ratio.md)
- [The truncation error at a large prime](../local/truncation-error.md)
- [The generator certificate](../../model/generator.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Local congruence](../../../sources/multiplication-locators.md#local-congruence)
