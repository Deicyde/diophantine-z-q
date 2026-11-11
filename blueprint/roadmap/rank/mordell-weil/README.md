---
article_id: af_a19a0d9b2e9e5df639a79112
---

# Mordell–Weil by two-isogeny descent

For a positive integer $n$ let $C_n:y^2=x^3-n^2x$ and $C'_n:y^2=x^3+4n^2x$ over $\mathbb Q$. When
$\mathrm{Sel}_2(C_n)$ has order $8$, a point of infinite order on $C_n$ yields every 2-Selmer
class of $C_n$, but only once $C_n(\mathbb Q)$ is known to be finitely generated. This section proves that by the classical route. The two-isogeny
descent shows that $2C_n(\mathbb Q)$ has finite index, and the descent theorem with the naive
height turns the finite index into finite generation, as for the generator curve in
[Mordell–Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md).

The descent uses the Kummer map $\alpha_b$, the two-isogeny $\varphi_b:E_b\to E_{-4b}$ and the
rescaling $\lambda_b:E_{16b}\to E_b$ of the [descent chapter](../../model/descent/README.md), for
the curves $E_b:y^2=x^3+bx$; here $C_n=E_{-n^2}$ and $C'_n=E_{4n^2}$. Over the number field $K_0$
the index $[E(K_0):2E(K_0)]$ was computed exactly. Here only its finiteness is needed, and it
follows from the finiteness of the two Kummer images over $\mathbb Q$.

This section writes $n$ for the positive integer of the curve; the rest of the positive-rank
chapter, following the Proposition 0 chapter, writes $d$ and $C_d$ for the same curves, and the
statement of finite generation is also given in that form.

## Two-torsion

$C_n$ has full rational two-torsion, of order four. The
[two-torsion lemma of the 2-descent](../two-descent/two-torsion.md) proves the same count over any
field in which $2\ne0$, as a separate statement.

- [The two-torsion of $C_n(\mathbb Q)$](two-torsion.md)

## The two-isogeny is a homomorphism

The finite-index argument needs $\varphi_b$ to be additive. Collinear points with nonzero
abscissas go to collinear points whose abscissas sum to the square of the new slope, and on
$E_{-4b}$ this forces the images to add up. The point at infinity, the point $(0,0)$ and the
degenerate sums are treated separately.

- [The two-isogeny maps a chord to a chord](isogeny-chords.md)
- [Addition along a line on $E_c$](addition-along-a-line.md)
- [The two-isogeny on chord sums and doubles](isogeny-chord-sums.md)
- [The two-isogeny is a homomorphism](isogeny-homomorphism.md)

## The index of $2C_n(\mathbb Q)$

Over any field of characteristic different from $2$, the dual isogeny factors doubling, so
$2E_b(K)$ has finite index once both Kummer images are finite. Over $\mathbb Q$ the Kummer image
of $E_c$ lies in the classes of the signed divisors of $c$, by a count of $p$-adic valuations.
Applied to $C_n$ and $C'_n$, this gives the weak Mordell–Weil theorem.

- [The index of $2E_b(K)$ from the two Kummer images](index-from-kummer-images.md)
- [The Kummer image over $\mathbb Q$ is finite](kummer-image-finite.md)
- [The weak Mordell–Weil theorem for $C_n$](weak-mordell-weil.md)

## Finite generation

The naive height on $\mathbb Q$ completes the descent.

- [Mordell–Weil for the congruent number curves](finite-generation.md)
