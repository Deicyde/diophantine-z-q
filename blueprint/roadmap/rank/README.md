---
article_id: af_7e4dd9c7081349458077d6b1
---

# The rank hypothesis as positive rank

The forms CR₃^Sel, CR₃^5b, CR₃^TYZ and CR₃^TYZ_Cl of the certified rank hypothesis met so far
conclude that every 2-Selmer class of $C_d:y^2=x^3-d^2x$ comes from a rational point, and CR₃
itself that one given class does. The theorems behind them (Tian–Yuan–Zhang as completed by
Proposition N, which is not refereed, and Gross–Zagier with an auxiliary field; Kriz's 2-converse
with the corank lemma is an alternative that is not needed) give a rank statement
($\operatorname{rank}C_d(\mathbb Q)\ge1$), not a statement about Selmer classes. This chapter proves the step between the two, RK9, by the
complete 2-descent. The descent map $\delta_d$ has kernel $2C_d(\mathbb Q)$ and image in
$\mathrm{Sel}_2(C_d)$, and $C_d(\mathbb Q)[2]$ has order $4$. So when $C_d(\mathbb Q)$ is finitely
generated, a point of infinite order gives $|C_d(\mathbb Q)/2C_d(\mathbb Q)|\ge8$, and when
$\mathrm{Sel}_2(C_d)$ has order $8$ the image is all of it. So CR₃^Sel, CR₃^TYZ and CR₃^TYZ_Cl have
positive-rank forms that ask only for a point of infinite order on $C_d$. With Mordell–Weil for every $C_d$, proved in its own section, the positive-rank
forms imply the original ones, and the positive-rank form of CR₃^Sel implies CR₃. A section
derives CR₃^TYZ_Cl,Rk from three statements about L-series of elliptic curves. The proof of pole completeness applies the hypothesis at only two curves, those of
a slot choice, and a further section states the positive-rank hypothesis for exactly those curves. A
last section restates the positive-rank hypotheses with the conclusion that the equation
$y^2=x^3-d^2x$ has infinitely many rational solutions, which mentions no group law.

Throughout, $C_d$ is the curve $E_{-d^2}$, $\mathrm{Sel}_2(C_d)$ is the Selmer group of the
[Proposition 0 chapter](../selmer/README.md), and $u\equiv v$ means that $u/v$ is a nonzero
square. The Mordell–Weil section writes $C_n$ for a positive integer $n$, as the row-5b chapter
does; elsewhere in this chapter the letter is $d$.

## The complete 2-descent

The Kummer maps at the roots $0$ and $d$ of $x^3-d^2x$ make up the descent map $\delta_d$. Over
$\mathbb Q$ its kernel is $2C_d(\mathbb Q)$, its image lies in the 2-Selmer group, and RK9 follows
by counting.

- [The complete 2-descent on a congruent number curve](two-descent/README.md)

## Mordell–Weil for the congruent number curves

RK9 needs $C_d(\mathbb Q)$ to be finitely generated. The two-isogeny descent and the descent
theorem with the naive height prove it for every $d\ne0$.

- [Mordell–Weil by two-isogeny descent](mordell-weil/README.md)

## The hypotheses in positive-rank form

Three positive-rank hypotheses: CR₃^Rk keeps the premises of CR₃^Sel, CR₃^TYZ,Rk asks, for squarefree $d\equiv5\pmod 8$, only for an
odd genus sum of Rédei's bits, and CR₃^TYZ_Cl,Rk for an odd genus sum of class numbers, as in Tian,
Yuan and Zhang's own statement. CR₃^TYZ_Cl,Rk implies CR₃^TYZ,Rk by Rédei's formula, and
CR₃^TYZ,Rk implies CR₃^Rk by Corollary 4.4 and Theorem 3.6.

- [The certified rank hypothesis in positive-rank form](certified-rank-rk.md)
- [The Tian–Yuan–Zhang hypothesis in positive-rank form](certified-rank-tyz-rk.md)
- [The class-number hypothesis in positive-rank form](certified-rank-tyz-cl-rk.md)
- [CR₃^TYZ,Rk implies CR₃^Rk](certified-rank-rk-of-tyz-rk.md)
- [CR₃^TYZ_Cl,Rk implies CR₃^TYZ,Rk](certified-rank-tyz-rk-of-cl-rk.md)

## The class-number hypothesis from the literature

CR₃^TYZ_Cl,Rk follows from Tian–Yuan–Zhang's row 5b, the functional equation of $L(C_d,s)$ for
squarefree $d\equiv5\pmod8$ with root number $-1$ on the critical strip $0<\operatorname{Re}s<2$,
and the positive-rank half of Gross–Zagier; none of the three is proved here. Row 5b in turn
follows from their Theorem 3.5(2) in reading A together with Hecke's continuation of $L(C_d,s)$,
two further statements that are not proved here; reading A is printed by no refereed text
consulted here and rests on the unrefereed Proposition N.

- [CR₃^TYZ_Cl,Rk from three literature statements](literature/README.md)

## Every Selmer class from positive rank

RK9 with Mordell–Weil turns each positive-rank form into the form whose conclusion is that every
Selmer class comes from a rational point. Each implication is also stated under the assumption
that $C_d(\mathbb Q)$ is finitely generated for every $d\ne0$.

- [CR₃^Sel from CR₃^Rk](certified-rank-sel-of-rk.md)
- [CR₃ from CR₃^Rk](certified-rank-of-rk.md)
- [CR₃^TYZ from CR₃^TYZ,Rk](certified-rank-tyz-of-rk.md)
- [CR₃^TYZ_Cl from CR₃^TYZ_Cl,Rk](certified-rank-tyz-cl-of-rk.md)

## The two curves of a slot choice

Pole completeness applies the hypothesis at the two curves $C_{d_1}$ and $C_{d_2}$ of a slot
choice; this section states the positive-rank hypothesis for exactly those curves and derives pole
completeness from it.

- [The rank hypothesis on the two curves of a slot choice](two-curves/README.md)

## The hypotheses as infinitely many rational points

The positive-rank forms mention the group law on $C_d(\mathbb Q)$. For $d\ne0$, with Mordell–Weil,
a point of infinite order exists exactly when $y^2=x^3-d^2x$ has infinitely many rational
solutions, so each of CR₃^Rk, CR₃^TYZ,Rk, CR₃^TYZ_Cl,Rk and CR₃^DL,Rk is equivalent to a form with
that conclusion, which mentions no group law.

- [The rank hypotheses as infinitely many rational points](infinitely-many-points/README.md)
