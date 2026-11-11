---
article_id: af_69d2055cbab7f3a1198c470d
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.mwFiniteIndex_two_of_kummer, ZInQ.RouteK.Rank.mwKer_kummer_finiteIndex, ZInQ.RouteK.Rank.mwPhiHat, ZInQ.RouteK.Rank.mwPhiHat_phi, ZInQ.RouteK.Rank.mwKer_kummer_eq_range, ZInQ.RouteK.Rank.mwKer_kummer'_le_comap
---

# The index of $2E_b(K)$ from the two Kummer images

Let $K$ be a field of characteristic different from $2$ and $b\in K^\times$, and let
$$\hat\varphi=\lambda_b\circ\varphi_{-4b}:E_{-4b}(K)\to E_{16b}(K)\to E_b(K)$$
be the dual isogeny. If the Kummer images $\alpha_b(E_b(K))$ and $\alpha_{-4b}(E_{-4b}(K))$ are
finite, then $2E_b(K)$ has finite index in $E_b(K)$.

Along the way:

- for $c\in K^\times$, if $\alpha_c(E_c(K))$ is finite, then $\ker\alpha_c$ has finite index in
  $E_c(K)$;
- $\hat\varphi$ is a group homomorphism, and $\hat\varphi(\varphi_b(P))=2P$ for every
  $P\in E_b(K)$;
- $\ker\alpha_b=\hat\varphi\bigl(E_{-4b}(K)\bigr)$;
- $\hat\varphi(Q)\in2E_b(K)$ for every $Q\in\ker\alpha_{-4b}$.

**Proof sketch.** (Silverman–Tate, Section III.5; Silverman, Proposition X.4.9.) Since $\alpha_c$
is a homomorphism, $E_c(K)/\ker\alpha_c\cong\alpha_c(E_c(K))$, which proves the first item.
$\hat\varphi$ is the composite of the homomorphism $\varphi_{-4b}$ and the group isomorphism
$\lambda_b$, and $\hat\varphi\circ\varphi_b=[2]$ is the doubling factorization.

For the kernel, write $P=\lambda_b(P')$ with $P'\in E_{16b}(K)$. The map $\lambda_b$ divides
abscissas by the square $4$ and sends $(0,0)$, of class $16b$, to $(0,0)$, of class $b$; so
$\alpha_b(P)=\alpha_{16b}(P')$. By the kernel theorem for $\varphi_{-4b}:E_{-4b}\to E_{16b}$,
$\alpha_{16b}(P')=1$ if and only if $P'\in\varphi_{-4b}(E_{-4b}(K))$, that is, if and only if
$P\in\hat\varphi(E_{-4b}(K))$. If $\alpha_{-4b}(Q)=1$, the kernel theorem for $\varphi_b$ gives
$Q=\varphi_b(P)$, so $\hat\varphi(Q)=2P$.

Finally, $\alpha_b(2P)=\alpha_b(P)^2=1$, so $2E_b(K)\subseteq\ker\alpha_b$ and
$$[E_b(K):2E_b(K)]=[\ker\alpha_b:2E_b(K)]\,[E_b(K):\ker\alpha_b].$$
The second factor is finite by the first item. For the first, $\ker\alpha_b=\hat\varphi(E_{-4b}(K))$,
so $[\ker\alpha_b:2E_b(K)]=[E_{-4b}(K):\hat\varphi^{-1}(2E_b(K))]$. The group
$\hat\varphi^{-1}(2E_b(K))$ contains $\ker\alpha_{-4b}$, which has finite index by the first item.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)
- [The Kummer map is a homomorphism](../../model/descent/kummer-homomorphism.md)

## Proof depends on

- [The two-isogeny is a homomorphism](isogeny-homomorphism.md)
- [The image of a two-isogeny is the kernel of the Kummer map](../../model/descent/kummer-kernel.md)
- [The composite of the two-isogenies is doubling](../../model/descent/isogeny-doubling.md)

## Sources

- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
- [Silverman: descent and heights](../../../sources/rank-locators.md#silverman-descent-and-heights)
