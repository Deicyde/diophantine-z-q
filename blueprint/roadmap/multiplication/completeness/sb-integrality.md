---
article_id: af_2bcee6844345efa5d9d63278
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.tests_integral_old
---

# Integrality of the tests at the old primes

Let $n_1,n_2,n_3\in\mathbb Z$ and $h\in\mathbb Z$
with $M_0\mid h$, $h\ne0$ and $h\ne c_*$, and let
$\tau=\tau\bigl(h,(n_1h,n_2h,n_3h);\,c_*,c_*n_1,c_*n_2,c_*n_3\bigr)$. Then
$$v_{\mathfrak p}(\tau_j)\ge0\qquad(1\le j\le12)$$
for every prime $\mathfrak p$ of $\mathbb Z[s]$ above a prime of $S_b$.

This is the manuscript's "the small formal subgroup in the definition of $M_0$ gives
$v_p(D_{gj})\ge0$ at $S_b$", with the step expanded.

**Proof sketch.** Put $Q_0=[M_0]P_0$. By the definition of $M_0$ (which is $\ge1$),
$1/x(Q_0)=(a+bs)/c$ with $N_s^4\mid a,b$ and $\gcd(c,N_s)=1$; the primes dividing
$N_s=P_sH_{\rm cat}$ are exactly those of $S_b$. Hence at every prime $\mathfrak p$ above
$p\in S_b$, $v_{\mathfrak p}(1/x(Q_0))\ge4$ (at odd $p$, $v_{\mathfrak p}(a),v_{\mathfrak p}(b)\ge4$ and
$v_{\mathfrak p}(c)=0$; at $(s)$, $v_s(a),v_s(b)\ge8$), so $Q_0\in E_1(K_{\mathfrak p})$ with
$v_{\mathfrak p}(z(Q_0))\ge2$. Since $c_*=4M_0$, the points $H=[h/M_0]Q_0$, $U_i=[n_i]H$,
$V_0=[(h-c_*)/M_0]Q_0$ and $V_i=[n_i]V_0$ are multiples of $Q_0$ (note
$z_i-c_*n_i=n_i(h-c_*)$). By the formal group, each lies in $E_1(K_{\mathfrak p})$ with
$v(z)\ge2$, hence $v(1/x)=2v(z)\ge4$, at every prime above $p$, including the conjugate one;
this gives $\tau_1,\dots,\tau_8$. For the ratios, $H,V_0\ne O$; by the unit form of the
truncated logarithm, $A_i=\bigl(z(U_i)/z(H)\bigr)\cdot u$ with $u$ a unit (or $A_i=0$ if
$U_i=O$), and $v(z([n_i]H))\ge v(z(H))$, so $A_i$ is integral; likewise $B_i$ at the conjugate
prime, so $\sigma B_i$ is integral at $\mathfrak p$. Hence $\tau_9,\dots,\tau_{12}$ are integral.

## Depends on

- [The twelve local tests](../certificate/twelve-tests.md)
- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)
- [The primes of $\mathbb Z[\sqrt2]$ above an odd prime](../local/primes-above-p.md)

## Proof depends on

- [The least formal multiple](../../syntax/constants/least-formal-multiple.md)
- [Properties of the multiplication constants](../certificate/constants-properties.md)
- [The formal neighbourhood of $y^2=x^3+Ax$ and its filtration](../local/formal-group.md)
- [The truncated logarithm is $16575z$ times a unit](../local/truncation-unit.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)
- [The generator certificate](../../model/generator.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Fixed local clearing](../../../sources/multiplication-locators.md#fixed-local-clearing)
- [Least formal multiple](../../../sources/multiplication-locators.md#least-formal-multiple)
