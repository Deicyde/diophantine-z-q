---
article_id: af_78010d6fcd0139911e3a7f29
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HDec.HSyn.sixContactMin_of_open38
---

# The minimal height hypothesis from thirty-seven statements

The [minimal height hypothesis](../main/six-contact-min.md) follows from the thirty-seven statements
of this chapter taken together: theorems from the literature, grouped by the theory they come from
([Shimura curves of discriminant 6](shimura-curves/README.md),
[abelian varieties](abelian-varieties/README.md),
[Néron models, semistable reduction and monodromy](neron-models/README.md),
[schemes and group schemes over a field](group-schemes/README.md),
[Faltings 1983 and Faltings heights](heights/README.md),
[p-adic Hodge theory](p-adic-hodge/README.md),
[Galois representations of modular forms](modular-galois/README.md)). Of the thirty-seven statements
from the literature, nineteen are published statements, some of them specialized or weakened;
thirteen are consequences of published theorems, which take further theorems to reach from the
print; and five combine several published theorems. The project's strict convention, which counts a
published statement only once its reading against the print is checked, counts sixteen of the
thirty-seven as published. None of the thirty-seven is proved here.

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
- [The Hodge–Tate decomposition of an abelian variety](p-adic-hodge/hodge-tate-decomposition.md)
- [The de Rham comparison for an abelian variety](p-adic-hodge/de-rham-comparison.md)
- [Pan's Fontaine–Mazur theorem, with Berger's theorem](p-adic-hodge/pan-fontaine-mazur.md)
- [Hodge–Tate weights of the representation of a newform](modular-galois/kato-hodge-tate-weights.md)
- [Carayol's theorem on the conductor](modular-galois/carayol-conductor.md)
- [Bost's lower bound for the Faltings height](heights/bost-lower-bound.md)
- [Javanpeykar's bound for curves with a Belyi function](heights/javanpeykar-bound.md)
- [Pazuki's comparison of the theta height with the Faltings height](heights/pazuki-bound.md)
- [The isogeny theorem of Gaudron and Rémond](heights/gaudron-remond-isogeny-bound.md)
- [González–Rotger: residue fields of CM points on X₆](shimura-curves/gonzalez-rotger-residue-fields.md)
- [González–Rotger: the number of CM points on X₆](shimura-curves/gonzalez-rotger-cm-count.md)
- [Semistable reduction gives unipotent inertia](neron-models/semistable-unipotent-inertia.md)
- [Shimura's Main Theorem I on Y₃ in Deligne's form](shimura-curves/shimura-main-theorem-y3.md)
- [Shimura's abelian varieties attached to newforms](modular-galois/shimura-abelian-varieties.md)
- [Elkies' coordinate on X₆/W](shimura-curves/elkies-coordinate.md)
- [The identity component of a smooth group scheme contains a neighbourhood of the identity](group-schemes/identity-component-neighbourhood.md)
- [Semistable reduction persists under base change](neron-models/semistable-base-change.md)
- [Raynaud's criterion for semistable reduction](neron-models/raynaud-criterion.md)
- [Mumford's theorem: families of abelian varieties are abelian schemes](abelian-varieties/mumford-group-law.md)
- [Néron models commute with unramified base change](neron-models/neron-models-and-unramified-base-change.md)
- [The criterion of Néron–Ogg–Shafarevich](neron-models/neron-ogg-shafarevich.md)
- [Deligne's Galois representations of eigenforms](modular-galois/deligne-representations.md)
- [The coefficients of an eigenform generate a number field](modular-galois/coefficient-field-finite.md)
- [The Deligne–Serre theorem](modular-galois/deligne-serre.md)
- [Torsion points over an algebraically closed field](abelian-varieties/torsion-points.md)
- [Homomorphisms of abelian varieties and Tate modules](abelian-varieties/homomorphisms-and-tate-modules.md)
- [The characteristic polynomial of an endomorphism](abelian-varieties/characteristic-polynomial.md)
- [Poincaré's complete reducibility](abelian-varieties/poincare-complement.md)
- [GAGA for homomorphisms of complex abelian varieties](abelian-varieties/gaga-for-homomorphisms.md)
- [Néron models over rings of integers](neron-models/neron-models-exist.md)
- [The Picard scheme of an abelian variety](abelian-varieties/picard-scheme-exists.md)
- [The identity component of the Picard scheme is an abelian variety](abelian-varieties/identity-component-of-picard.md)
- [The Weil pairing](abelian-varieties/weil-pairing.md)
- [The kernel of an ample line bundle is finite](abelian-varieties/ample-kernel-finite.md)
- [Translation-invariant line bundles come from an ample one](abelian-varieties/phi-onto-pic-zero.md)

## Sources

- [The decomposition](../../sources/height-decomposition-locators.md#the-decomposition)
