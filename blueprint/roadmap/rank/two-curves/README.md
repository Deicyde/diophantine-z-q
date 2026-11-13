---
article_id: af_753ce65272850c48056a59ca
---

# The rank hypothesis on the two curves of a slot choice

Pole completeness uses the rank hypothesis at two curves only. For an admissible input $B$, a
multiplier $m$, a prime $p_0\mid\beta$ and slot data for $\beta,\theta,p_0$, these are $C_{d_1}$
and $C_{d_1|\theta|}=C_{d_2}$, with $d_1=|\beta|\,q_0\prod r_p\prod r_\ell$ as in
[the realization](../../route-k/realization.md). Both carry Selmer certificates for $\beta$, so
through Proposition 0 their 2-Selmer groups have order $8$ and contain a class with first
coordinate $\beta$. This section states the positive-rank hypothesis for exactly these curves,
CR₃^DL,Rk: for every triple $\beta,\theta,p_0$ satisfying the hypotheses of the realization, some
slot choice gives two curves with rational points of infinite order. CR₃^DL,Rk follows from the
positive-rank forms CR₃^Rk and CR₃^TYZ,Rk of [the positive-rank chapter](../README.md), and it
implies pole completeness: on a certified curve, a point of infinite order makes every Selmer
class come from a rational point, and this gives the points with abscissas in
$\beta\mathbb Q^{*2}$ that the pole polynomial needs. The same holds for CR₃^DL,Adm,Rk, which asks
only that for every admissible $B$ some multiplier, prime $p_0$ and slot choice give two curves
with points of infinite order.

Throughout, $C_d$ is the curve $y^2=x^3-d^2x$, as in the rest of the positive-rank chapter.

## Certificates and the 2-Selmer group

Through Proposition 0, a Selmer certificate for $(d,a)$ says that $\mathrm{Sel}_2(C_d)$ has order
$8$ and contains a class with first coordinate $a$.

- [The 2-Selmer group of a certified curve](selmer-group-of-a-certificate.md)

## The hypothesis

The slot data are existential, so the curves of any one slot choice suffice. Both forms depend
on the slot construction: a change to the slot conditions changes what they assert. CR₃^DL,Rk
implies CR₃^DL,Adm,Rk, since the inputs that an admissible number produces satisfy the hypotheses
of CR₃^DL,Rk.

- [The positive-rank hypothesis on the two curves of a slot choice](certified-rank-dl-rk.md)
- [The positive-rank hypothesis at the inputs of admissible numbers](certified-rank-dl-adm-rk.md)
- [CR₃^DL,Adm,Rk from CR₃^DL,Rk](certified-rank-dl-adm-rk-of-dl-rk.md)

## The hypothesis from its forms on all curves

On each of the two curves, the certificate gives the premises of CR₃^Rk through Proposition 0,
and those of CR₃^TYZ,Rk through Proposition 0, Corollary 4.4 and Theorem 3.6.

- [CR₃^DL,Rk from CR₃^Rk](certified-rank-dl-rk-of-rk.md)
- [CR₃^DL,Rk from CR₃^TYZ,Rk](certified-rank-dl-rk-of-tyz-rk.md)

## Pole completeness

With CR₃^DL,Rk or CR₃^DL,Adm,Rk in place of CR₃, the main theorem holds under the minimal height
hypothesis and either of them alone:
[the main theorem from positive rank on the two curves of a slot choice](../../main/main-theorem-two-curves.md).

- [A point of infinite order on a certified curve](point-of-infinite-order.md)
- [Pole completeness from CR₃^DL,Rk](pole-completeness-from-dl-rk.md)
- [Pole completeness from CR₃^DL,Adm,Rk](pole-completeness-from-dl-adm-rk.md)
