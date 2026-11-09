---
article_id: af_bd6481b675c042d993b6365d
---

# The main theorem and its hypotheses

Throughout, $K_0=\mathbb Q(s)$ with $s^2=2$, $d=75-53s$, and $E:y^2=x^3-d^2x$ over $K_0$.
For a reduced fraction $a/b$ with $b>0$, $h(a/b)=\log\max(|a|,b)$.

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

Pole completeness asserts the rational solubility of one explicit polynomial for all
suitably prepared inputs.

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

The catalogue bound is no longer an assumption of substance: the
[progressions chapter](../progressions/README.md) proves it from an effective Dirichlet
theorem. Under the remaining hypotheses (the minimal form of the height estimate, pole completeness
and the twenty-two-prime pattern, or the two-slope pattern in its place) the target holds.

- [The main theorem](main-theorem.md)
