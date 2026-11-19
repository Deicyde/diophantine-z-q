---
declaration: theorem
origin: cited
---

# One family for the two coefficient tests (3.9)

Keep $E$, $h_*$, the normalized odd symbol and the final $k$ and $K=\mathbb Q(\sqrt k)$, in the branch where
the intrinsic odd symbol is not a unit at the empty configuration. For every sufficiently large $b$ there
are a finite set $Q$ of distinct good odd primes split in $K$ and outside the fixed support, and nonzero
linear forms $\lambda_q:\mathbb F_2^b\to\mathbb F_2$, such that the family
$$h_x=\prod_{q\in Q}(q^*)^{\lambda_q(x)}\quad(x\in\mathbb F_2^b),\qquad q^*=(-1)^{(q-1)/2}q,$$
has $h_0=1$, keeps all fixed local types, and for every $x\ne0$ satisfies
$$\operatorname{ord}_{s=1}L(E^{(h_x)},s)=1,\quad L_*(h_xk)\ne0,\quad j_{\rm gen}(h_x)\le\omega(h_x)+C_o,\quad v_2L_*(h_xk)\le2\omega(h_x)+C_e.\tag{3.9}$$
The constants are independent of $b$. By (3.4), with $k$ fixed, $2j_{\rm rc}(h_x,k)\le4\omega(h_x)+C_J$.

**Proof sketch.** Take enough copies of every label with total label zero; keeping the seed anchors and
contracting the unused copies into the last anchor gives, for each of the two symbols, a nonzero terminal
polynomial, since a minimum seed does not depend on its internal bits. The two-symbol address construction
then adjoins primary vertices so that both the odd symbol and the even symbol of $E^{(k)}$ are units at every
$x\ne0$. The order of choices is: the fixed data and $D_w$; the genus lower bound and the odd minimum; the
final $K$ and the common alphabet; the determinant precision $M$; then $b$ and its finite operator budget;
then an actual theta stage $M_\theta$, which is not $M$, and only then the primes, by finite realization. At
that stage an odd unit gives $v_2a_{M_\theta}(h_x)=\delta_o+\omega(h_x)<M_\theta$, so (O.8) gives the simple
zero and the bound on $j_{\rm gen}$ (F.7), and the even unit gives the bound on $L_*(h_xk)$ by (3.3a). With
(3.4), $C_J=2C_o+C_e-v_2L_*(h_*)+2$.

## Depends on

- [The branch split and the nonempty seeds](nonempty-seeds.md)

## Proof depends on

- [The address constructions](address-constructions.md)
- [Finite realization, unit seeds and contraction certificates](seeds.md)
- [The odd minimum and the intrinsic odd symbol](odd-minimum.md)
- [Visibility and the native genus index (O.8)](../coefficient-sources/visibility.md)
- [The partitionable even upper estimate (3.3b)](even-upper.md)
- [The genus bound before odd normalization (3.4)–(3.6)](genus-lower-bound.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): the packet realization (L2656–2673), `ex:sec7-final-family`
  (L2674–2712) and `ex:app-final-family` (L10792–10861)

## Manuscript check

Checked by AI review. The bound $2j_{\rm rc}(h_x,k)\le4\omega(h_x)+C_J$ from (3.9) and (3.4) was checked by
script, with the constant above. The realization of the family at one actual stage (L10814–10861) was read
for structure; the order of choices is consistent, with the constants fixed before $b$, and the finite
budget and theta precision chosen after it. The upper use of (3.4) here depends on the form of
Cai–Shu–Tian's Theorem 1.1 discussed under (3.4), which is not yet checked against the print.
