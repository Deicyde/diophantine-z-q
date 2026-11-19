---
article_id: af_78010d6fcd0139911e3a7f29
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HDec.HSyn.sixContactMin_of_open90
---

# The minimal height hypothesis from twenty-seven statements

The [minimal height hypothesis](../main/six-contact-min.md) follows from the twenty-seven statements
of this chapter taken together: theorems from the literature, grouped by the theory they come from
([Shimura curves of discriminant 6](shimura-curves/README.md),
[complex multiplication](cm-fibres/README.md), [abelian varieties](abelian-varieties/README.md),
[Néron models, semistable reduction and monodromy](neron-models/README.md),
[Faltings 1983 and Faltings heights](heights/README.md),
[p-adic Hodge theory](p-adic-hodge/README.md),
[Galois representations of modular forms](modular-galois/README.md)). Of the twenty-seven statements
from the literature, twelve are published statements, some of them specialized or weakened; and
fifteen are consequences of published theorems, which take further theorems to reach from the print.
The project's strict convention, which counts a published statement only once its reading against
the print and its review are complete, counts six of the twenty-seven as published. None of the
twenty-seven is proved here.

The proof follows the manuscript's proof of its Theorem 4.1 at the one instance the main theorem
uses, which the project has split into named steps, each proved from these statements and the steps
before it. Among them are the existence of an unramified vertical prime above each prime $p>324$ in
the Hecke cover, along the steps of the project's Lemma NV; the inequalities between heights, from
the analytic uniformization, the existence of Néron models, the bounds of the section on heights and
the results on semistable reduction and Néron models; the Galois representation of a newform as a
subrepresentation of the Tate module of $J_1(N)$, with its semisimplicity and its conductor; and the
last stretch, from the level bound, the theta point and the height inequalities to the minimal
height hypothesis.

## Depends on

- [The minimal height hypothesis](../main/six-contact-min.md)

## Proof depends on

- [Faltings' semisimplicity theorem](heights/faltings-semisimplicity.md)
- [Faltings' theorem on Tate's conjecture](heights/faltings-tate-conjecture.md)
- [Pazuki's comparison of the theta height with the Faltings height](heights/pazuki-bound.md)
- [Néron models over Dedekind domains](neron-models/neron-models-exist.md)
- [Deligne's Galois representations of eigenforms](modular-galois/deligne-representations.md)
- [The Deligne–Serre theorem](modular-galois/deligne-serre.md)
- [Pan's Fontaine–Mazur theorem](p-adic-hodge/pan-fontaine-mazur.md)
- [Frobenius on the Tate module of Shimura's abelian variety](modular-galois/shimura-af-frobenius.md)
- [Hodge–Tate weights of the representation of a newform](modular-galois/kato-hodge-tate-weights.md)
- [Berger's theorem: de Rham representations are potentially semistable](p-adic-hodge/berger-de-rham-potentially-semistable.md)
- [Shimura's Main Theorem I on Y₃ in Deligne's form](shimura-curves/shimura-main-theorem-y3.md)
- [The lower bound for the Faltings height](heights/bost-lower-bound.md)
- [The isogeny theorem of Gaudron and Rémond](heights/gaudron-remond-isogeny-bound.md)
- [Javanpeykar's bound for curves with a Belyi map](heights/javanpeykar-bound.md)
- [Raynaud's criterion for semistable reduction](neron-models/raynaud-criterion.md)
- [The integral model of Y₃ over ℤ[1/30]](shimura-curves/y3-integral-model.md)
- [Carayol's theorem on the conductor](modular-galois/carayol-conductor.md)
- [Shimura's abelian variety attached to a newform](modular-galois/shimura-abelian-varieties.md)
- [The degree of a field of definition of a CM elliptic curve](cm-fibres/cm-field-degree.md)
- [The discriminant formula for the Faltings height of an elliptic curve](cm-fibres/elliptic-height-discriminant-formula.md)
- [The quotient map from Y₃ to the projective line](shimura-curves/y3-quotient-map.md)
- [Homomorphisms of semiabelian schemes over a discrete valuation ring extend uniquely](heights/faltings-extension-lemma.md)
- [Fowler's bound for discriminants of bounded class number](cm-fibres/fowler-class-number-bound.md)
- [Silverberg and Zarhin's inertia criterion for semistable reduction](neron-models/inertia-criterion.md)
- [Local algebraicity of Hodge–Tate characters](p-adic-hodge/conrad-local-algebraicity.md)
- [Scholze's comparison theorem for H¹ of an abelian variety](p-adic-hodge/scholze-de-rham-comparison.md)
- [The first ℓ-adic cohomology of an abelian variety is dual to its Tate module](abelian-varieties/tate-module-duality.md)

## Sources

- [The decomposition](../../sources/height-decomposition-locators.md#the-decomposition)
