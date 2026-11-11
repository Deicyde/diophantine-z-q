---
article_id: af_ac4c26d5ea93859974e99c96
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.redeiK_kernel_iff_updateCol, ZInQ.RouteK.Redei.redeiK_lapl_rowSum, ZInQ.RouteK.Redei.redeiK_sum_updateCol, ZInQ.RouteK.Redei.redeiK_zmod2_cases
---

# The kernel of $(L_B\mid z_B)$ through a square matrix

Let $V$ be a finite set with bits $a_{ij},y_i,z_i\in\mathbb F_2$ on $V$ satisfying reciprocity, as in
[Rédei's $g$ from the bits](../../rank-5b/genus-sum/redei-g.md). Let $B\subseteq V$, $\rho\in B$,
$y(B)=\sum_{i\in B}y_i$, and let $L_B$ be the Laplacian of $a$ on $B$. Say that *the kernel of $(L_B\mid z_B)$ is trivial* if
the following holds: for every $e:V\to\mathbb F_2$ vanishing off $B$ and every $e_2\in\mathbb F_2$
with $e_2=0$ when $y(B)=1$, if
$$\sum_{p\in B}(L_B)_{qp}e_p+e_2z_q=0\quad\text{for every }q\in B,$$
then $e_2=0$ and $e$ is constant on $B$ (identically $0$ or identically $1$ there). So the column
$z_B$ counts only when $y(B)=0$.

Let $w=y$ if $y(B)=1$ and $w=z$ otherwise, and let $N$ be $L_B$ with its column $\rho$ replaced by
$w$. Then the kernel of $(L_B\mid z_B)$ is trivial if and only if every $F:V\to\mathbb F_2$
vanishing off $B$ with $\sum_{p\in B}N_{qp}F_p=0$ for all $q\in B$ vanishes on $B$.

Along the way, without reciprocity:

- the rows of $L_B$ sum to zero over $B$: $\sum_{p\in B}(L_B)_{qp}=0$ for $q\in B$;
- splitting off the column $\rho$: $\sum_{p\in B}N_{qp}F_p=\sum_{p\in B}(L_B)_{qp}F'_p+w_qF_\rho$,
  where $F'$ is $F$ with $F'_\rho=0$;
- every element of $\mathbb F_2$ is $0$ or $1$.

**Proof sketch.** (⇒) Let $F$ vanish off $B$ with $\sum_pN_{qp}F_p=0$ on $B$. Put $e=F$ with
$e_\rho=0$, and $e_2=F_\rho$, so that $L_Be+F_\rho w=0$ on $B$.

- If $y(B)=1$, sum over $q\in B$. Under reciprocity the column sums of $L_B$ over $B$ are
  $y_v(1+y(B))=0$, while $\sum_{q\in B}w_q=y(B)=1$, so $F_\rho=0$.
- In either case the triviality of the kernel applies (with $w=z$ when $y(B)=0$). It gives
  $e_2=0$ and $e$ constant on $B$, and $e_\rho=0$, so $F=0$ on $B$.

(⇐) Given $(e,e_2)$, replace $e$ by $e-e_\rho$ on $B$; this does not change $L_Be$ on $B$, since
the rows of $L_B$ sum to zero. Set its value at $\rho$ to $e_2$ and call the result $F$. Then
$\sum_pN_{qp}F_p=0$ on $B$ (when $y(B)=1$ because $e_2=0$, when $y(B)=0$ because $w=z$), so $F=0$
on $B$: $e_2=0$, and $e=e_\rho$ is constant on $B$.

## Depends on

- [The Laplacian of a family of bits](../../rank-5b/forests/laplacian.md)
- [Rédei's $g$ from the bits](../../rank-5b/genus-sum/redei-g.md)

## Proof depends on

- [The cofactors of the Laplacian (Lemma 2.2)](../../rank-5b/genus-sum/lemma-2-2.md)

## Sources

- [Step 7: the kernel](../../../sources/redei-locators.md#step-7-the-kernel)
- [Rédei's formulas](../../../sources/redei-locators.md#redeis-formulas)
