---
article_id: af_bd6481b675c042d993b6365d
---

# The main theorem and its hypotheses

Throughout, $K_0=\mathbb Q(s)$ with $s^2=2$, $d=75-53s$, and $E:y^2=x^3-d^2x$ over $K_0$.
For a reduced fraction $a/b$ with $b>0$, $h(a/b)=\log\max(|a|,b)$. In the rank hypotheses and the
articles that state them, $d$ instead denotes a positive integer and $C_d$ the congruent number
curve $y^2=x^3-d^2x$ over $\mathbb Q$; the row-5b chapter writes $n$ and $C_n$ for these.

The target is the manuscript's Theorem 1.1, in the exact form frozen by the upstream
project.

- [The target statement](frozen-target.md)

The manuscript proves it from six inputs. Three of them depend on deep arithmetic whose
conclusions are nonetheless elementary statements. The six-contact height estimate bounds
the height of a rational number by its odd contact support.

- [The six-contact height estimate](six-contact-estimate.md)

The proof uses the estimate at a single prime set and radius, $S=S_{\rm mul}$ and $R=D$, and
the main theorem assumes only this instance.

- [The minimal height hypothesis](six-contact-min.md)
- [The six-contact estimate implies its minimal form](six-contact-min-of-estimate.md)

The trust statement for H follows the manuscript's proof of the six-contact estimate up to its
last step, with some steps replaced or re-sourced and several checked by no referee. Combining
three of the manuscript's bounds, it gives a bound on the height of the Hauptmodul value
$J(u)=-57600F(u)^2/G(u)^6$, where $F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)$ and
$G(u)=7u^2+300u+3600$ (the manuscript does not display that bound). This bound, at $R=D$, is the
$j$-form of the height hypothesis; it is not proved here and is not a published theorem. The
manuscript's last step returns from $J(u)$ to $u$. That return is replaced here by a proved
inequality, so the $j$-form at $S=S_{\rm mul}$ implies the minimal height hypothesis; the target
holds under the $j$-form together with CR₃^TYZ_Cl,Rk or with the three statements about L-series
below.

- [The height hypothesis in its $j$-form](j-form/README.md)

Pole completeness asserts the rational solubility of one explicit polynomial for all
suitably prepared inputs. The polynomial here is the Route K one, whose curves are congruent
number curves, and pole completeness is no longer assumed: the
[Route K chapter](../route-k/README.md) proves it from a narrower hypothesis, CR₃, which turns an
explicit 2-Selmer certificate of a congruent number curve into a rational point.

- [Pole completeness](pole-completeness.md)
- [The certified rank hypothesis](certified-rank.md)

CR₃ follows from a form stated with the 2-Selmer group itself, CR₃^Sel, because the explicit system
is that Selmer group ([Proposition 0](../selmer/README.md)). CR₃^Sel in turn follows from a
hypothesis in the terms of Smith's row-5b determinant, CR₃^5b, and CR₃^5b from one in Tian, Yuan and
Zhang's terms, CR₃^TYZ ([the row-5b chapter](../rank-5b/README.md)); by Rédei's formula, CR₃^TYZ is
equivalent to its form CR₃^TYZ_Cl with their class numbers ([the Rédei chapter](../redei/README.md)).
Each of CR₃^Sel, CR₃^5b, CR₃^TYZ and CR₃^TYZ_Cl concludes that every Selmer class comes from a
rational point; CR₃ itself concludes only that $C_d$ has a rational point $(x,y)$ with $x\ne0$ and
$x/a$ a square, for the one given $a$. CR₃^Sel, CR₃^TYZ and CR₃^TYZ_Cl also
have forms that conclude only that the curve has positive rank. These imply narrower hypotheses
still, which ask for positive rank only on the two curves of a slot choice
([the positive-rank chapter](../rank/README.md)).

The generator argument uses the Mordell–Weil theorem for $E$ over $K_0$. It was a
hypothesis until the two-isogeny descent of the model chapter proved it.

- [Mordell–Weil for the generator curve](mordell-weil.md)

The multiplication certificate needs twenty-two simultaneous prime values of linear forms
with prescribed reduction behaviour, and the size bounds need every unit class modulo the
catalogue modulus to contain twenty-two primes below the explicit cutoff $2^{W^8}$.

- [The twenty-two-prime pattern](prime-pattern.md)
- [The catalogue bound](catalogue-bound.md)

The multiplication proof uses the prime pattern only to write every integer as a sum of three
slopes with controlled contact primes, the
[slope representation](../multiplication/completeness/slope-representation.md). A second
pattern in primes, with two slopes and twelve linear forms, also gives it, so it can replace
the twenty-two-prime pattern.

- [The two-slope prime pattern](two-slope-pattern.md)

Neither pattern is needed any more. [Route AP](../route-ap/README.md) proves the completeness of
the multiplication template, for the same polynomial, from long arithmetic progressions of good
slope primes; these come from Szemerédi's theorem in the primes, proved from the
Green–Tao theorem ([the Green–Tao chapter](../green-tao/README.md)), and from the positive density
of the good slope primes, [Proposition D](../density/README.md).

The catalogue bound is no longer an assumption of substance: the
[progressions chapter](../progressions/README.md) proves it from an effective Dirichlet
theorem. Under the remaining hypotheses (the minimal form of the height estimate, the certified
rank hypothesis CR₃ and the twenty-two-prime pattern) the target holds; it also holds with pole
completeness in place of CR₃, or with the two-slope pattern in place of the twenty-two-prime
pattern.

- [The main theorem](main-theorem.md)

With route AP the prime pattern drops out, and the target holds under the minimal height
hypothesis and CR₃ alone, or under the minimal height hypothesis and CR₃^Sel or CR₃^5b.

- [The main theorem from two hypotheses](main-theorem-two-hypotheses.md)
- [The main theorem from the Selmer form of the rank hypothesis](main-theorem-selmer.md)

Under the minimal height hypothesis the target also holds with CR₃ replaced by CR₃^TYZ or
CR₃^TYZ_Cl, by any of the positive-rank forms, by positive rank on the two curves of a slot
choice (for every input of the descent, or only for the inputs of admissible numbers), or by
any of the equivalent forms that ask for infinitely many rational points instead of positive rank.

- [The main theorem from the Tian–Yuan–Zhang forms of the rank hypothesis](main-theorem-tyz.md)
- [The main theorem from the positive-rank forms of the rank hypothesis](main-theorem-positive-rank.md)
- [The main theorem from positive rank on the two curves of a slot choice](main-theorem-two-curves.md)
- [The main theorem from the infinitely-many-points forms of the rank hypothesis](main-theorem-infinitely-many-points.md)

The positive-rank form of CR₃^TYZ_Cl, CR₃^TYZ_Cl,Rk, follows from three statements about
L-series: two textbook theorems (the functional equation of $L(C_d,s)$ with root number $-1$,
stated on the strip $0<\operatorname{Re}s<2$, and the positive-rank half of Gross–Zagier) and
Tian–Yuan–Zhang's row 5b, which rests on Proposition N, an unpublished argument written for this
project and not refereed
([the literature section of the positive-rank chapter](../rank/literature/README.md)). The target holds under
the minimal height hypothesis or its $j$-form together with those three statements, and under the
$j$-form and CR₃^TYZ_Cl,Rk.

- [The main theorem from the $j$-form and the L-series statements](main-theorem-literature.md)
