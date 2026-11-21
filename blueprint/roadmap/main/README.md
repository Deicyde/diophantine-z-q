---
article_id: af_bd6481b675c042d993b6365d
---

# The main theorem and its hypotheses

Throughout, $K_0=\mathbb Q(s)$ with $s^2=2$, $d=75-53s$, and $E:y^2=x^3-d^2x$ over $K_0$.
For a reduced fraction $a/b$ with $b>0$, $h(a/b)=\log\max(|a|,b)$.

## The target

The target is the manuscript's Theorem 1.1, in the exact form frozen by the upstream
project.

- [The target statement](frozen-target.md)

## The two headlines

The target has two headline theorems, one for each route to the pole input. They are means to the same
end, and both prove the target statement from the minimal height hypothesis below and a pole input:

- Elliot's route follows the manuscript. Its pole input is pole completeness, the manuscript's Theorem 5.2
  for its own pole polynomial, which the manuscript derives from its restricted converse theorem
  (Theorem 5.3).
- The congruent-number route changes the pole polynomial to one for the congruent number curves, whose
  pole completeness follows from a certified rank hypothesis, derived from Tian–Yuan–Zhang's
  Theorem 3.5(2) in reading A and Gross–Zagier. Its Lean is kept at the tag `route-k-final` and pinned
  upstream in elliotglazer/diophantine-z-q.

- [The main theorem by Elliot's route](main-theorem.md)
- [The main theorem by the congruent-number route](main-theorem-reading-a-gross-zagier.md)

The minimal height hypothesis is not proved here: it is the one instance of the manuscript's
Theorem 4.1 that the proof uses, and it is not a published theorem, since its proof combines refereed
theorems and exact computations with new arguments, the manuscript's and this project's, reviewed only
by AI models. For Elliot's route, the derivation of pole completeness from Theorem 5.3 is formalized here,
from Theorem 5.3 and two cited inputs
([pole completeness from the restricted converse](../pole-completeness-from-5-3/README.md)), and the
proof of Theorem 5.3 has [its own chapter](../restricted-converse/README.md). The manuscript's other
inputs are proved, two of them by routes that differ from the manuscript's: route AP replaces the
twenty-two-prime pattern, and the catalogue bound is proved with a larger cutoff. The rest of this
chapter follows the manuscript's inputs, gives the form of the theorem closest to them, which also
assumes the twenty-two-prime pattern, and ends with the pages of the congruent-number route.

## The manuscript's inputs

The manuscript proves the target from six inputs. Three of them depend on deep arithmetic whose
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
inequality, so the $j$-form at $S=S_{\rm mul}$ implies the minimal height hypothesis.

- [The height hypothesis in its $j$-form](j-form/README.md)

Pole completeness asserts the rational solubility of one explicit polynomial for all
suitably prepared inputs. A rational zero puts two points on curves $y^2=x(x-\ell)(x+3\ell)$. It is the
manuscript's Theorem 5.2 and a hypothesis of the main theorem; the manuscript derives it from its
restricted converse theorem by a simultaneous 2-descent (Section 5.1). That descent is formalized here,
from Theorem 5.3 and two cited inputs ([its chapter](../pole-completeness-from-5-3/README.md)).

- [Pole completeness](pole-completeness.md)

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
theorem. Under the minimal form of the height estimate, pole completeness and the twenty-two-prime
pattern the target holds; this is the form of the theorem closest to the manuscript's inputs.

- [The main theorem from three hypotheses](main-theorem-three-hypotheses.md)

## The congruent-number route's forms of the theorem

The congruent-number route does not assume pole completeness for the manuscript's polynomial. It uses a
different pole polynomial, whose curves are the congruent number curves $y^2=x(x-\ell)(x+\ell)$, with
its pole completeness proved from a certified rank hypothesis CR₃. CR₃ in turn comes from statements
about L-series: Tian–Yuan–Zhang's Theorem 3.5(2) in reading A and the positive-rank half of Gross–Zagier,
with Hecke's continuation and the functional equation, which are proved. The project used this route
until fork issue #77. Its Lean is kept at the tag `route-k-final` and pinned upstream in
elliotglazer/diophantine-z-q, and nasqret/z-in-q-lean builds on it; the project note
`docs/research/rs-pole.md` records why it was adopted. Its pages are:
- [the certified rank hypothesis](certified-rank.md);
- the [chapter on pole completeness from certified rank](../route-k/README.md), and the chapters on
  [Proposition 0](../selmer/README.md), [the row-5b determinant](../rank-5b/README.md),
  [Rédei's formula](../redei/README.md) and [positive rank](../rank/README.md);
- its headline, listed above, and the forms of the main theorem below.

The headline's proof passes through intermediate forms of the main theorem. In proof order:

- [The main theorem from two hypotheses](main-theorem-two-hypotheses.md)
- [The main theorem from the Selmer form of the rank hypothesis](main-theorem-selmer.md), from the
  previous form and the form closest to the manuscript
- [The main theorem from the Tian–Yuan–Zhang forms of the rank hypothesis](main-theorem-tyz.md)
- [The main theorem from the positive-rank forms of the rank hypothesis](main-theorem-positive-rank.md),
  from the Selmer and Tian–Yuan–Zhang forms; the headline is proved from it

Three further forms branch off this chain; the headline does not use them:

- [The main theorem from positive rank on the two curves of a slot choice](main-theorem-two-curves.md)
- [The main theorem from the infinitely-many-points forms of the rank hypothesis](main-theorem-infinitely-many-points.md)
- [The main theorem from the $j$-form and the L-series statements](main-theorem-literature.md)
