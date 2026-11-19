---
article_id: af_6712e6e911643bcd49514cbb
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves71.faltingsLemma1DVRPrint
---

# Homomorphisms of semiabelian schemes over a discrete valuation ring extend uniquely

The *extension statement for semiabelian schemes* is the following assertion. Let $K$ be a field,
$\mathcal O\subseteq K$ a valuation ring of $K$ that is a discrete valuation ring, with residue
field $k$, and $A$ and $B$ abelian varieties over $K$. Let $G$ and $H$ be smooth, separated,
quasi-compact group schemes over $\mathcal O$ with isomorphisms of group schemes $G_K\cong A$ and
$H_K\cong B$ from their generic fibres, and suppose that the special fibres $G_k$ and $H_k$ are
connected and semiabelian: each has an open connected subgroup scheme $U$ with a flat surjective
homomorphism $U\to C$ onto an abelian variety $C$ over $k$ whose kernel becomes isomorphic as a
group scheme to $\mathbb G_m^r$, for some $r\ge0$, after base change to an algebraic closure
$\bar k$ of $k$; that is, for every $\bar k$-algebra $R$ there is an isomorphism of groups from
$(R^\times)^r$ onto the kernel of $U(R)\to C(R)$, natural in $R$. Then for every homomorphism of
group schemes $f:G_K\to H_K$ over $K$ there is exactly one morphism of $\mathcal O$-schemes
$g:G\to H$ whose base change to $K$ is $f$.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Faltings states the lemma over any normal base $S$ with a dense open subscheme $U$, for a
homomorphism over $U$ between two semiabelian varieties over $S$: smooth algebraic groups whose
fibres are all connected of one common dimension $g$ and are extensions of an abelian variety by a
torus. The statement is the case of the spectrum of a discrete valuation ring and its generic point,
for models whose generic fibres are abelian varieties. Its hypotheses imply Faltings' definition.
The generic fibre is an abelian variety, hence connected and an extension of itself by the trivial
torus. A smooth model is flat, so its generic fibre is dense in it and the model is connected;
smoothness then makes the relative dimension constant on the model, so both fibres have the same
dimension. The project rates it a published statement in its printed form, a leaf: an AI reader read
p. 350 verbatim from the page image and found the statement a direct instance, an AI reviewer rated
it a leaf, and a third AI skeptic pass, checking fidelity to the print and the meaning of the formal
statement, could not refute it. It replaced the statement that the semistable height does not change
under extension of the base field, which is proved here from it, with Silverberg–Zarhin's criterion
and the existence of Néron models over a Dedekind base. The manuscript lists Faltings' paper and
cites it for other results, not for this lemma. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Faltings 1983 Lemma 1](../../../sources/height-decomposition-locators.md#faltings-1983-lemma-1)
