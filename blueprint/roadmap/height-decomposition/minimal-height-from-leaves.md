---
article_id: af_78010d6fcd0139911e3a7f29
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HDec.HSyn.sixContactMin_of_open58
---

# The minimal height hypothesis from thirty-one statements

The [minimal height hypothesis](../main/six-contact-min.md) follows from the thirty-one statements
of this chapter taken together: theorems from the literature, grouped by the theory they come from
([Shimura curves of discriminant 6](shimura-curves/README.md),
[abelian varieties](abelian-varieties/README.md),
[Néron models, semistable reduction and monodromy](neron-models/README.md),
[Faltings 1983 and Faltings heights](heights/README.md),
[p-adic Hodge theory](p-adic-hodge/README.md),
[Galois representations of modular forms](modular-galois/README.md)). Of the thirty-one statements,
the project classes twenty-three as published statements, some of them specialized or weakened; five are consequences of published theorems, which take further
theorems to reach from the print; and three combine several published theorems. The project's
strict convention, which counts a published statement only once its reading against the print is
checked, counts fifteen of the thirty-one as published. AI raters assigned these classes, and no
person has yet confirmed a statement against its source. None of the thirty-one is proved here. The
list changes as statements are proved or restated; `docs/one-proof/OPEN.md` is the current one.
Two statements that the chapter used to assume, on
[torsion points](abelian-varieties/torsion-points.md) and on
[GAGA for homomorphisms](abelian-varieties/gaga-for-homomorphisms.md), are now proved.

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
- [Bost's lower bound for the Faltings height](heights/bost-lower-bound.md)
- [Javanpeykar's bound for curves with a Belyi map](heights/javanpeykar-bound.md)
- [Pazuki's comparison of the theta height with the Faltings height](heights/pazuki-bound.md)
- [The isogeny theorem of Gaudron and Rémond](heights/gaudron-remond-isogeny-bound.md)
- [Chevalley's structure theorem over a perfect field](heights/chevalley-structure-theorem.md)
- [The Hodge–Tate decomposition of an abelian variety](p-adic-hodge/hodge-tate-decomposition.md)
- [The Tate module of an abelian variety is de Rham](p-adic-hodge/de-rham-comparison.md)
- [The Galois invariants of the ring of de Rham periods](p-adic-hodge/bdr-galois-invariants.md)
- [Pan's Fontaine–Mazur theorem](p-adic-hodge/pan-fontaine-mazur.md)
- [Berger's theorem: de Rham representations are potentially semistable](p-adic-hodge/berger-de-rham-potentially-semistable.md)
- [Hodge–Tate weights of the representation of a newform](modular-galois/kato-hodge-tate-weights.md)
- [Carayol's theorem on the conductor](modular-galois/carayol-conductor.md)
- [Shimura's abelian varieties attached to newforms](modular-galois/shimura-abelian-varieties.md)
- [Deligne's Galois representations of eigenforms](modular-galois/deligne-representations.md)
- [Cusp forms with integral Fourier coefficients](modular-galois/coefficient-field-finite.md)
- [Hecke operators and rational Fourier coefficients](modular-galois/hecke-operators-rational-coefficients.md)
- [The Deligne–Serre theorem](modular-galois/deligne-serre.md)
- [González–Rotger: residue fields of CM points on X₆](shimura-curves/gonzalez-rotger-residue-fields.md)
- [X₀(6,1) as a coarse moduli scheme](shimura-curves/x6-coarse-moduli.md)
- [Shimura's Main Theorem I on Y₃ in Deligne's form](shimura-curves/shimura-main-theorem-y3.md)
- [Elkies' coordinate on X₆/W](shimura-curves/elkies-coordinate.md)
- [Semistable reduction gives unipotent inertia](neron-models/semistable-unipotent-inertia.md)
- [Semistable reduction persists under base change](neron-models/semistable-base-change.md)
- [Raynaud's criterion for semistable reduction](neron-models/raynaud-criterion.md)
- [Néron models over Dedekind domains](neron-models/neron-models-exist.md)
- [The criterion of Néron–Ogg–Shafarevich](neron-models/neron-ogg-shafarevich.md)
- [Torsion points over an algebraically closed field](abelian-varieties/torsion-points.md)
- [The characteristic polynomial of an endomorphism](abelian-varieties/characteristic-polynomial.md)
- [GAGA for homomorphisms of complex abelian varieties](abelian-varieties/gaga-for-homomorphisms.md)
- [The Picard scheme of an abelian variety](abelian-varieties/picard-scheme-exists.md)
- [The identity component of the Picard scheme is proper](abelian-varieties/picard-identity-component-proper.md)

## Sources

- [The decomposition](../../sources/height-decomposition-locators.md#the-decomposition)
