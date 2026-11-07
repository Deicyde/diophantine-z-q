---
article_id: af_fa1b877a814d1f44d00860a6
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.tests_precision_selected
---

# Precision of the tests at a selected prime

Let $p>324$ be a prime with good reduction at a split pair of places: $p$ is odd,
$r\in\mathbb Z$ satisfies $r^2\equiv2\pmod p$, $75\mp53r\not\equiv0\pmod p$, and
$$d_1=\#\widetilde E_r(\mathbb F_p),\qquad d_2=\#\widetilde E_{-r}(\mathbb F_p),\qquad
\widetilde E_{\pm r}:y^2=x^3-(75\mp53r)^2x,$$
counting the point at infinity. Let $\mathfrak p_1=(p,s-r)$ and $\mathfrak p_2=(p,s+r)=\sigma\mathfrak p_1$.
Let $h\in\mathbb Z$ with $h\ne0$, $h\ne c_*$, $d_1\mid h$ and $d_2\mid h-c_*$, let
$n_1,n_2\in\mathbb Z$, $n_3=n_1n_2$, and
$\tau=\tau\bigl(h,(n_1h,n_2h,n_3h);\,c_*,c_*n_1,c_*n_2,c_*n_3\bigr)$. Then
$$v_{\mathfrak p_1}(\tau_j)\ge1\quad(1\le j\le8),\qquad v_{\mathfrak p_1}(\tau_j)\ge28\quad(9\le j\le12).$$

**Proof sketch.** Reduction modulo $\mathfrak p_1$ is a homomorphism
$E(K_0)\to\widetilde E_r(\mathbb F_p)$, a group of order $d_1$, so the reduction of $[h]P_0$ is
$[h/d_1]\bigl([d_1]\overline{P_0}\bigr)=O$; by the definition of reduction, $H=[h]P_0$ lies in
$E_1(K_{\mathfrak p_1})$. Likewise $V_0=[h-c_*]P_0\in E_1(K_{\mathfrak p_2})$. Then
$U_i=[n_i]H\in E_1(K_{\mathfrak p_1})$ and $V_i=[n_i(h-c_*)]P_0=[n_i]V_0\in E_1(K_{\mathfrak p_2})$.
For a point $Q\ne O$ of $E_1$, $v(1/x(Q))=2v(z(Q))\ge2$; with
$v_{\mathfrak p_1}(\sigma y)=v_{\mathfrak p_2}(y)$ this gives the first eight bounds. Since
$\lambda_{\mathfrak p_1}$ is a homomorphism, $\lambda_{\mathfrak p_1}(U_i)=n_i\lambda_{\mathfrak p_1}(H)$
with $\lambda_{\mathfrak p_1}(H)\ne0$, and the truncation error at $p>324$ gives
$A_i=n_i(1+\epsilon_i)/(1+\epsilon_0)$ with $v(\epsilon)\ge28$, so
$v_{\mathfrak p_1}(A_i-n_i)\ge28$. In the same way $v_{\mathfrak p_2}(B_i-n_i)\ge28$, that is
$v_{\mathfrak p_1}(\sigma B_i-n_i)\ge28$. Hence $\tau_{8+i}=A_i-\sigma B_i$ and
$\tau_{12}=A_1A_2-A_3\equiv n_1n_2-n_3=0$ have valuation at least $28$.

## Depends on

- [The twelve local tests](../certificate/twelve-tests.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../local/primes-above-p.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [Reduction is injective on prime-to-$p$ torsion](../../model/descent/reduction-torsion.md)
- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](../local/formal-group.md)
- [The formal logarithm](../local/formal-logarithm.md)
- [The truncation error at a large prime](../local/truncation-error.md)
- [The generator certificate](../../model/generator.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Choice of shifts](../../../sources/multiplication-locators.md#choice-of-shifts)
- [Twelve tests](../../../sources/multiplication-locators.md#twelve-tests)
