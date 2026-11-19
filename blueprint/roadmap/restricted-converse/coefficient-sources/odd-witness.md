---
declaration: theorem
origin: cited
---

# One witness and a compatible detecting sequence (3.7), (O.2)

Under the corank-one hypothesis of Theorem 5.3, use the prepared positive unit filter containing $1$. There
are a negative odd fundamental discriminant $h_*$ with $L(E^{(h_*)},1)\ne0$, a positive fundamental
discriminant $D_w$ in that filter with $L'(E^{(D_w)},1)\ne0$, and a fixed integer $L$ such that $LP_D$ lies in the
rational line of the $D$-twist for every admissible $D$ and $Q=LP_{D_w}$ has infinite order. There is one
sequence of stages, with $M\to\infty$, good primes $\ell_0$ and additive maps
$\lambda_M:E(\mathbb F_{\ell_0^2})\to\mathbb Z/2^M\mathbb Z$, such that
$$\rho(\operatorname{Fr}_{\ell_0})\equiv C\pmod{2^M},\quad(D_w/\ell_0)=1,\quad(h_*/\ell_0)=-1,\quad v_2\lambda_M(\overline Q)=c_w<M,\tag{3.7}$$
with $c_w$ fixed, Frobenius squared trivial on $E[2^M]$ and $\lambda_M$ of Frobenius sign $+1$; here $C$ is
complex conjugation on the Tate module. Finite prime exclusions may be added later without changing $c_w$.

**Proof sketch.** Selmer parity gives root number $-1$. Clause (ii) of Bump–Friedberg–Hoffstein, with every old
prime in the splitting set, gives $h_*$, odd and outside the fields with extra units; clause (i), with the primes
of $h_*$ added, gives $D_w$, in the filter containing $1$ and prime to $h_*$. The genus character of
$\mathbb Q(\sqrt{D_wh_*})$ cuts out $\mathbb Q(\sqrt{D_w},\sqrt{h_*})$, so $P_{D_w}$ has a $D_w$-component and an
$h_*$-component; the latter has rank zero by the forward rank-zero case of Lemma 5.5. Theorem 1.1 of
Cai–Shu–Tian at conductor one, with every prime of $N$ split and no extra units, relates the height of
$P_{D_w}$ to the Rankin derivative $L'(E^{(D_w)},1)L(E^{(h_*)},1)\ne0$, so $P_{D_w}$ has infinite order. A multiple
$L$ of $4BB_{\rm cusp}$, with $B=\prod_{j\le2,f\le4}\#E(\mathbb F_{p_j^f})$ killing torsion over fields of degree at
most four and $B_{\rm cusp}$ killing cuspidal images, makes $LP_D$ a rational point of $E^{(D)}$. The Kummer
cocycle of $Q$ is nonzero on the kernel of $\rho$, because a central scalar $z\ne1$ gives
$(z-1)c(g)=(g-1)c(z)$; so its translation image is a full lattice. A row $b$ with $bC=b$ and an element
$\sigma$ with $\rho(\sigma)=C$ detect it with fixed valuation $c_w$. Chebotarev gives primes $\ell_0$ with
$\operatorname{Fr}_{\ell_0}\equiv C$ and $\ell_0\equiv-1\pmod{2^M}$, and $\lambda_M=b\kappa_M$, where
$\kappa_M(P)=FQ_P-Q_P$ maps $E(\mathbb F_{\ell_0^2})/2^M$ isomorphically onto $E[2^M]$ (O.2).

## Depends on

None.

## Proof depends on

- [The opening reduction](../opening-reduction.md)
- [Nonvanishing in a prescribed unit filter](nonvanishing.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): the witness and stages in Section 7 (L2460–2498),
  `ex:app-detector` (L8224–8406)

## Manuscript check

Mapped by AI review and read for structure. One gap was filled: the step from
$L'(E^{(D_w)},1)L(E^{(h_*)},1)\ne0$ to the height formula uses that the derivative of the product at $s=1$ is that
product, that is $L(E^{(D_w)},1)=0$. This follows from the root number of $E^{(D_w)}$, which is
$w(E)\chi_{D_w}(-1)\chi_{D_w}(N)=(-1)(1)(1)=-1$, since $D_w>0$ and every prime of $N$ splits; the manuscript
leaves it implicit. The height formula is used here only qualitatively. Not yet checked against the prints:
Theorem 1.1 of Cai–Shu–Tian, the clauses of Bump–Friedberg–Hoffstein (pp. 543–544) and Theorem 1.8 of
Dokchitser–Dokchitser.
