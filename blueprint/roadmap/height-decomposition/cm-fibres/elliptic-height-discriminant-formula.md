---
article_id: af_42ae9e5c84d2ded23483e64e
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves71.cmHeight62
---

# The discriminant formula for the Faltings height of an elliptic curve

The *discriminant formula statement* is the following assertion. Let $K$ be a number field, $L$ a
number field containing $K$, and $E$ an elliptic curve over $K$ with good reduction everywhere over
$L$: some smooth separated group scheme $\mathcal G$ of finite type over $\mathcal O_L$, proper over
$\mathcal O_L$, has generic fibre isomorphic to $E_L$ as a group scheme. For each embedding
$\sigma:L\to\mathbb C$ let $\tau_\sigma$ be a period of $E$ at $\sigma$, that is, at the restriction
of $\sigma$ to $K$, with $\operatorname{Im}\tau_\sigma>0$: some surjective homomorphism $\Phi$ from
$\mathbb C$ to the complex points $E_\sigma(\mathbb C)$ of $E$ through $\sigma$, under which the
preimage of the complex points of each Zariski open subset $U$ of $E$ is open and each regular
function on $U$ is holomorphic along $\Phi$, has kernel $c(\mathbb Z+\tau_\sigma\mathbb Z)$ for some
$c\ne0$. Then
$$h_F(E)\le\frac1{[L:\mathbb Q]}\sum_{\sigma:L\to\mathbb C}-\frac1{12}\log\Bigl(\bigl|\Delta(\tau_\sigma)\bigr|\,(\operatorname{Im}\tau_\sigma)^6\Bigr),\qquad\Delta(\tau)=(2\pi)^{12}\eta(\tau)^{24}.$$
Here $h_F(E)$ is the stable Faltings height of $E$: the infimum in $[-\infty,+\infty]$, over all
number fields $L'\supseteq K$ and all smooth separated group schemes $\mathcal N$ of finite type
over $\mathcal O_{L'}$ whose generic fibre is isomorphic to $E_{L'}$ as a group scheme, of the
height of $\mathcal N$, which is the Arakelov degree of the $\mathcal O_{L'}$-module
$\omega_{\mathcal N}$ of invariant differentials of $\mathcal N$, with the metric
$\|\omega\|_{\sigma'}^2=\frac i2\int_{E_{\sigma'}(\mathbb C)}\omega\wedge\overline\omega$ at each
embedding $\sigma':L'\to\mathbb C$, divided by $[L':\mathbb Q]$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Equation (6.2) of Barquero-Sanchez, Cadwallader,
Cannon, Genao and Masri is the general formula for the Faltings height of an elliptic curve over a
number field through its minimal discriminant and the modular discriminant at its periods, which the
paper attributes to Silverman; the upstream review of the manuscript's CM argument read it in the
published article, in Faltings' original metric and with $\Delta(\tau)=(2\pi)^{12}\eta(\tau)^{24}$.
The statement is its case of good reduction everywhere, where the term of the minimal discriminant
vanishes, and keeps only the inequality $\le$, the half the manuscript uses; it is not restricted to
curves with complex multiplication. The manuscript's remark that the extension to $L$ does not
change the stable height is built into the definition above, an infimum over all extensions.
Reaching the statement from the print takes the comparison of the height in the paper with the
height of $\mathcal G$ in that definition, which is not proved here. The display of (6.2) has not
been re-read for this statement, and a review of the statement is pending. It is a hypothesis, not
proved here.

## Depends on

None.

## Sources

- [Barquero-Sanchez et al. Eq. (6.2)](../../../sources/height-decomposition-locators.md#barquero-sanchez-et-al-eq-62)
