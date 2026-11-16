---
article_id: af_78010d6fcd0139911e3a7f29
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HDec.HSyn.sixContactMin_of_open35
---

# The minimal height hypothesis from forty-five statements

The [minimal height hypothesis](../main/six-contact-min.md) follows from the forty-five statements
of this chapter taken together: forty-four statements from the literature, grouped by the theory
they come from ([Shimura curves of discriminant 6](shimura-curves/README.md),
[theta constants of genus 2](theta-constants/README.md),
[abelian varieties](abelian-varieties/README.md),
[Néron models, semistable reduction and monodromy](neron-models/README.md),
[schemes and group schemes over a field](group-schemes/README.md),
[Faltings 1983 and Faltings heights](heights/README.md),
[p-adic Hodge theory](p-adic-hodge/README.md),
[Galois representations of modular forms](modular-galois/README.md)), and one step of the project's
own argument, [local inertia of tame covers of the line](local-inertia-of-tame-covers.md). Of the
forty-four statements from the literature, thirty-four are published statements, some of them
specialized or weakened; six are consequences of published theorems, which take further theorems to
reach from the print; and four combine several published theorems. None of the forty-five is proved
here.

The proof follows the manuscript's proof of its Theorem 4.1 at the one instance the main theorem
uses, which the project has split into named steps, each proved from these statements and the steps
before it. Among them are the existence of an unramified vertical prime above each prime $p>324$ in
the Hecke cover, from the local inertia statement and the moduli description of the Shimura curves;
the inequalities between heights, from the analytic uniformization, the existence of Néron models,
the bounds of the section on heights and the results on semistable reduction and Néron models; the
Galois representation of a newform as a subrepresentation of the Tate module of $J_1(N)$, with its
semisimplicity and its conductor; and the last stretch, from the level bound, the theta point and
the height inequalities to the minimal height hypothesis.

## Depends on

- [The minimal height hypothesis](../main/six-contact-min.md)

## Proof depends on

- [The criterion of Néron–Ogg–Shafarevich](neron-models/neron-ogg-shafarevich.md)
- [Faltings' semisimplicity theorem](heights/faltings-semisimplicity.md)
- [Faltings' theorem on Tate's conjecture](heights/faltings-tate-conjecture.md)
- [The Hodge–Tate decomposition of an abelian variety](p-adic-hodge/hodge-tate-decomposition.md)
- [The de Rham comparison for an abelian variety](p-adic-hodge/de-rham-comparison.md)
- [Pan's Fontaine–Mazur theorem, with Berger's theorem](p-adic-hodge/pan-fontaine-mazur.md)
- [Hodge–Tate weights of the representation of a newform](modular-galois/kato-hodge-tate-weights.md)
- [The Deligne–Serre theorem](modular-galois/deligne-serre.md)
- [Carayol's theorem on the conductor](modular-galois/carayol-conductor.md)
- [Bost's lower bound for the Faltings height](heights/bost-lower-bound.md)
- [Javanpeykar's bound for curves with a Belyi function](heights/javanpeykar-bound.md)
- [Pazuki's comparison of the theta height with the Faltings height](heights/pazuki-bound.md)
- [The isogeny theorem of Gaudron and Rémond](heights/gaudron-remond-isogeny-bound.md)
- [Mumford's theorem: families of abelian varieties are abelian schemes](abelian-varieties/mumford-group-law.md)
- [The identity component of a smooth group scheme is open](group-schemes/identity-component-open.md)
- [González–Rotger: residue fields of CM points on X₆](shimura-curves/gonzalez-rotger-residue-fields.md)
- [Raynaud's criterion for semistable reduction](neron-models/raynaud-criterion.md)
- [González–Rotger: the number of CM points on X₆](shimura-curves/gonzalez-rotger-cm-count.md)
- [Néron models commute with strict henselization](neron-models/neron-models-and-strict-henselization.md)
- [Semistable reduction persists under base change](neron-models/semistable-base-change.md)
- [Semistable reduction gives unipotent inertia](neron-models/semistable-unipotent-inertia.md)
- [Shimura's Main Theorem I on Y₃ in Deligne's form](shimura-curves/shimura-main-theorem-y3.md)
- [Shimura's abelian varieties attached to newforms](modular-galois/shimura-abelian-varieties.md)
- [Elkies' coordinate on X₆/W](shimura-curves/elkies-coordinate.md)
- [Deligne's Galois representations of eigenforms](modular-galois/deligne-representations.md)
- [Torsion points over an algebraically closed field](abelian-varieties/torsion-points.md)
- [Homomorphisms of abelian varieties and Tate modules](abelian-varieties/homomorphisms-and-tate-modules.md)
- [The characteristic polynomial of an endomorphism](abelian-varieties/characteristic-polynomial.md)
- [Poincaré's complete reducibility](abelian-varieties/poincare-complement.md)
- [Cartier's theorem](group-schemes/cartier-theorem.md)
- [A connected scheme with a rational point is geometrically connected](group-schemes/geometrically-connected.md)
- [Group schemes over a field are equidimensional](group-schemes/group-schemes-equidimensional.md)
- [The analytic uniformization of a complex abelian variety](abelian-varieties/analytic-uniformization.md)
- [GAGA for homomorphisms of complex abelian varieties](abelian-varieties/gaga-for-homomorphisms.md)
- [Néron models over rings of integers](neron-models/neron-models-exist.md)
- [Ratios of theta constants are algebraic](theta-constants/theta-ratios-algebraic.md)
- [Tate's theorem on the invariants of the twists of C_p](p-adic-hodge/invariants-of-tate-twists.md)
- [The Ax–Sen–Tate theorem](p-adic-hodge/ax-sen-tate.md)
- [A quasi-inverse of an isogeny](abelian-varieties/isogeny-quasi-inverse.md)
- [Properness spreads out from a limit](group-schemes/properness-spreads-out.md)
- [The Picard scheme of an abelian variety](abelian-varieties/picard-scheme-exists.md)
- [The identity component of the Picard scheme is an abelian variety](abelian-varieties/identity-component-of-picard.md)
- [The polarization of an ample line bundle is an isogeny](abelian-varieties/polarization-isogeny.md)
- [The Weil pairing](abelian-varieties/weil-pairing.md)
- [Local inertia of tame covers of the line](local-inertia-of-tame-covers.md)

## Sources

- [The decomposition](../../sources/height-decomposition-locators.md#the-decomposition)
