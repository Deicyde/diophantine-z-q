---
article_id: af_679fc04247a01012f9eed426
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.redeiG_eq_kappa, ZInQ.RouteK.Rank5b.Sec3.sum_y_kappa, ZInQ.RouteK.Rank5b.Sec3.sum_z_kappa, ZInQ.RouteK.Rank5b.Sec3.sum_z_kappa_of_y_zero
---

# Rédei's $g$ through the cofactors (2.1), (2.2)

Let $a,y,z$ be bits on a finite set $V$ and $B\subseteq V$.

- If $y(B)=1$, then $\sum_{\rho\in B}y_\rho\,\kappa_\rho(B)=g(B)$.
- If the bits satisfy reciprocity and $y(B)=1$, then $g(B)=\kappa_\rho(B)$ for every $\rho\in B$, and
  (2.1) $\sum_{\rho\in B}z_\rho\,\kappa_\rho(B)=z(B)\,g(B)$.
- (2.2) If $y(B)=0$, then $\sum_{\rho\in B}z_\rho\,\kappa_\rho(B)=g(B)$.

**Proof sketch.** The first and the last statements are the definition of $g$. Assume reciprocity
and $y(B)=1$. By Lemma 2.2 all $\kappa_r(B)$, $r\in B$, equal $\kappa_\rho(B)$ for a fixed $\rho\in B$, so
$g(B)=\sum_ry_r\kappa_r(B)=y(B)\,\kappa_\rho(B)=\kappa_\rho(B)$. Then
$\sum_rz_r\kappa_r(B)=z(B)\,\kappa_\rho(B)=z(B)\,g(B)$; here $B$ is not empty because $y(B)=1$.

## Depends on

- [Rédei's $g$ from the bits](redei-g.md)

## Proof depends on

- [The cofactors of the Laplacian (Lemma 2.2)](lemma-2-2.md)

## Sources

- [Proposition 2.3](../../../sources/rank-5b-locators.md#proposition-23)
