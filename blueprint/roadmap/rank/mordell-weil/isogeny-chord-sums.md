---
article_id: af_e3e3752d0edd98a526ec6bd1
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.mwPhi_add_generic, ZInQ.RouteK.Rank.mwPhi_double, ZInQ.RouteK.Rank.mwPhi_double'
---

# The two-isogeny on chord sums and doubles

Let $K$ be a field of characteristic different from $2$, $b\in K^\times$, and let
$\varphi_b:E_b(K)\to E_{-4b}(K)$ be the two-isogeny. Write $T=(0,0)$.

- (Chords.) If $P_1=(x_1,y_1)$ and $P_2=(x_2,y_2)$ in $E_b(K)$ have $x_1,x_2\ne0$, $x_1\ne x_2$,
  $x_1x_2\ne b$, and $P_1+P_2$ has nonzero abscissa, then
  $\varphi_b(P_1+P_2)=\varphi_b(P_1)+\varphi_b(P_2)$.
- (Doubling.) If $P=(x,y)$ has $x\ne0$, $y\ne0$ and $2P$ has nonzero abscissa, then
  $\varphi_b(2P)=2\varphi_b(P)$. Equivalently, $\varphi_b(2R)=2\varphi_b(R)$ whenever
  $R\notin\{O,T\}$ and $2R\notin\{O,T\}$.

**Proof sketch.** (Silverman–Tate, Section III.4.) *Chords.* Let $y=\ell x+\nu$ be the chord
through $P_1,P_2$. Then $P_1+P_2=(x_3,-(\ell x_3+\nu))$ with $x_1+x_2+x_3=\ell^2$. The
factorization of $x^3+bx-(\ell x+\nu)^2$ gives $x_1x_2x_3=\nu^2$, so $\nu\ne0$. Subtracting the
curve equations of $P_1$ and $P_2$ and dividing by $x_1-x_2$ gives
$x_1x_2+x_1x_3+x_2x_3=b-2\ell\nu$. By the image-line identity, $\varphi_b(P_1)$, $\varphi_b(P_2)$
and $\varphi_b(-(P_1+P_2))$ lie on $Y=LX+N$, so $\varphi_b(P_1+P_2)=(X_3,-(LX_3+N))$. By the
abscissa-sum identity, $X_1+X_2+X_3=L^2$. Finally $X_1\ne X_2$: by the curve equations,
$X_1=X_2$ would give $x_1x_2(x_1-x_2)(x_1x_2-b)=0$. Addition along a line on $E_{-4b}$ gives the
claim.

*Doubling.* Take the tangent slope $\ell$, with $2y\ell=3x^2+b$, and the same relations with
$x_1=x_2=x$. From $x(2P)\cdot(2y)^2=(x^2-b)^2$ and $x(2P)\ne0$ we get $b\ne x^2$, so the image
ordinate $y(b-x^2)/x^2$ is nonzero. The tangency identity and doubling along a line on
$E_{-4b}$ give the claim. For $R=(x,y)\notin\{O,T\}$ we have $x\ne0$; $2R\ne O$ forces $y\ne0$,
and $2R\ne T$ forces $x(2R)\ne0$.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)

## Proof depends on

- [The Kummer map is a homomorphism](../../model/descent/kummer-homomorphism.md)
- [The two-isogeny maps a chord to a chord](isogeny-chords.md)
- [Addition along a line on $E_c$](addition-along-a-line.md)

## Sources

- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
