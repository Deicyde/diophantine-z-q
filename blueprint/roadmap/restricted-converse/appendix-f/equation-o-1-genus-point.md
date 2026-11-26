---
article_id: af_cac96e31fa5a2d56f9c65ec2
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Manuscript.RC.Visibility.genusPoint, ZInQ.Contrib.CloudB3RC53.GenusOdd.heegnerSum, ZInQ.Contrib.CloudB3RC53.GenusOdd.HeegnerDatum
---

# (O.1): the conductor-one point $P_D$

Fix the genus partner $h_*<0$. For an admissible $D$ the field $K_D=\mathbb Q(\sqrt{Dh_*})$ is
imaginary quadratic, and the conductor-one point is the unaveraged sum of the Heegner points
$x_D^{[\mathfrak a]}$ under the modular parametrization $\pi$, weighted by the genus character:
$$P_D=\sum_{[\mathfrak a]\in\operatorname{Pic}(\mathcal O_{K_D})}\chi_{h_*}(\mathrm N\mathfrak a)\,
\pi\bigl(x_D^{[\mathfrak a]}\bigr).\tag{O.1}$$
Neither the class number nor the number of units is divided out. This is not the conductor-$|h|$
ring-class point of Section 9.

In Lean a genus datum for $D$ (`HeegnerDatum` at discriminant $Dh_*$, conductor one and
$d_1=h_*$) consists of the field $K_D$, a primitive quadratic character $\chi$ of the class group
that equals $\chi_{h_*}(\mathrm N\mathfrak p)$ at the primes $\mathfrak p$ prime to $h_*$, a Heegner
form of level $N$, and a point $y$ of $E$ over the Hilbert class field $H_1$ whose image under a
complex embedding is the value of the modular parametrization at the Heegner point of that form.
`genusPoint` is the sum `heegnerSum`, $\sum_{\sigma}\chi(\sigma)\,\sigma(y)$ over
$\sigma\in\mathrm{Gal}(H_1/K_D)$, with $\chi(\sigma)$ read through the Artin map; so the sum over ideal
classes is a sum over the Galois group. The point depends on the datum, and the odd side of the
proof fixes one datum for each $D$.

## Depends on

None.

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
