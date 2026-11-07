---
article_id: af_3cc8c949ef82de16f68343e5
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Assembly.test_complete
---

# One suitable shift

Assume pole completeness. For every $n\in\mathbb Z\setminus\mathcal C$ there is a nonzero
$\kappa\in\mathbb Z$ with
$$\operatorname{Test}(n,\kappa,n).$$

**Proof sketch.** $F(n)\ne0$; choose $\eta=\pm1$ with $R_0=\eta\cdot2730^6F(n)>0$, so $R_0>1$. Let $\Pi$ be
the finite set of prime elements of $\mathbb Z[s]$ dividing $R_0$ (one per associate class) and
$N=1+\max_{\pi\in\Pi}v_\pi(F(n))$. By the deep-multiples statement there is $\kappa\ge1$ with
$[\kappa]P_0\in E_N(\pi)$ for all $\pi\in\Pi$.

Take $h=2\kappa$, $s_0=2\kappa n$, so that
$$H=[2\kappa]P_0,\quad U=[2\kappa n]P_0,\quad V_0=[\kappa]P_0,\quad V_1=[\kappa n]P_0 .$$
Then $\kappa\ne0$, $h\ne0$ and $h-\kappa=\kappa\ne0$, and $t=n\notin\mathcal C$. The six tests
$D_1,\dots,D_6$ and $C_j=D_j/F(n)$ are now fixed elements of $K_0$. By the real-conditions statement
choose $q$ with reduced denominator coprime to $R_0$ (so $v_p(q)\ge0$ for $p\mid R_0$) such that
$a_0,W,\Theta\ne0$ and $0<B_{\rm pole}<1/2$. By the local-conditions statement,
$v_p(B_{\rm pole})\ge4$ for every $p\in\{2,3,5,7,13\}$ and the reduced denominator of $B_{\rm pole}$ is
a square. Pole completeness gives $\Phi(B_{\rm pole})$. All conditions of $\operatorname{Test}(n,\kappa,n)$
hold.

Compared with the manuscript: its "integral trace justifies this also at the ramified place
two" is the case $p=2$ of the trace statement, and the guards hold because nonzero multiples
of $P_0$ are affine with nonzero coordinates.

## Depends on

- [The six local tests](../value-templates/six-local-tests.md)
- [Pole completeness](../../main/pole-completeness.md)

## Proof depends on

- [Deep multiples of the generator](deep-multiples.md)
- [Local conditions on the pole input](pole-input-local.md)
- [Real conditions on the pole input](pole-input-real.md)
- [Nonzero multiples of the generator](../../model/descent/nonzero-multiples.md)

## Sources

- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
- [Theorem 5.2](../../../sources/assembly-locators.md#theorem-52)
