---
article_id: af_666d246a72a909c31243d8d6
---

# Multiplication and the finite false-triple guard

The multiplication template is the arithmetic core of the construction: it must accept a
triple of rational $5$-tuples exactly when they are the codes $\iota(a),\iota(b),\iota(ab)$ of
integer multiples of the generator $P_0$ of $2E(K_0)$. Its $35{,}134$ witnesses consist of
three rational constants fixing $P_0$, four fixed scalar multiples by $c_*=4M_0$, one height
certificate of $27$ slope certificates with six test groups each, and one inverse of a
finite guard product. This chapter proves input M of the assembly lemma.

The proof is asymmetric. *Soundness* (accepted triples are true) works on arbitrary
rational inputs and uses the six-contact height estimate H: at every odd contact prime of
every slope outside $S_{\rm mul}$, the certificate forces $n_1n_2\equiv n_3$ modulo $p^{25}$, so
H bounds a false triple to the box $[-T,T]^3$ with $T=(48A_{\rm ht})^{13}$, where the guard
excludes it. *Completeness* (true triples are accepted) uses the twenty-two-prime pattern
22P to choose slopes with controlled contact primes and pole completeness PC to supply the
pole witnesses. Both directions use the generator certificate $2E(K_0)=\mathbb ZP_0$, whose
Mordell-Weil input is proved by the two-isogeny descent. The astronomically large constants $c_*$, $\ell_0$,
$A_{\rm ht}$ and $T$ appear only symbolically; the finite computations of the chapter are a
few small closed identities and inequalities.

## The pole obstruction

Write $\Phi(B)$ for the rational solubility of the pole polynomial $Q_{\rm pole}$ with input
$B$. For $B\ne0$ the witnesses give a signed divisor $m$ of $2730$ and points
$(A,r_1)\in C_e$, $(Az^2,zr_2)\in C_{eH}$ on the congruent number curves
$C_\ell:y^2=x(x-\ell)(x+\ell)$ (the manuscript has $x+3\ell$), and a
parity argument on the valuation of the abscissa shows that $\Phi(B)$ is impossible when
$v_p(B)$ is negative and odd at a prime $p\notin\{2,3,5,7,13\}$. This elementary direction is
what soundness uses; the converse, pole completeness, is used only for completeness, and the
[Route K chapter](../route-k/README.md) proves it from the certified rank hypothesis.

- [Parity of the abscissa on $y^2=x(x-\ell)(x+\ell)$](abscissa-parity.md)
- [The one-sided pole obstruction](pole-obstruction.md)

## Local conventions

The local parameter $z=-x/y$, the inverse abscissa $w=1/x$, the formal group, the formal
logarithm and its isometry range, the explicit binomial series of the logarithm of $E$, the
truncated logarithm $L$ and its error $v(\epsilon_z)\ge28$ at primes $p>324$ are developed in
their own section.

- [Local conventions: the formal group and the truncated logarithm](local/README.md)

## The certificate

The constants and prime sets of the certificate, the twelve tests, the slope predicate and
the semantics of each template are in their own section.

- [The certificate and its semantics](certificate/README.md)

## Soundness

The pole obstruction and the trace force the congruence $n_1n_2\equiv n_3\pmod{p^{25}}$ at
odd contact primes outside $S_{\rm mul}$, the six-contact estimate turns these congruences into
the finite-box deduction (Proposition 6.1), and the guard closes the box.

- [Soundness: accepted triples are true](soundness/README.md)

## Completeness

The prime pattern, the choice of shifts at the selected primes, weak approximation and pole
completeness produce the witnesses for every true triple.

- [Completeness: true triples are accepted](completeness/README.md)

## The multiplication statement

- [Correctness of the multiplication template](multiplication-template.md)
