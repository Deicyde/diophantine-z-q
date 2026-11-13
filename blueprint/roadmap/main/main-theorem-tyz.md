---
article_id: af_f74996c1558c73365e2fa419
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl
---

# The main theorem from the Tian–Yuan–Zhang forms of the rank hypothesis

Assume the minimal height hypothesis and the Tian–Yuan–Zhang form CR₃^TYZ of the certified rank
hypothesis. Then the target statement holds. The theorem also holds under the minimal height hypothesis and
the class-number form CR₃^TYZ_Cl.

CR₃^TYZ asks, for every squarefree positive $d\equiv5\pmod8$ with $|\mathrm{Sel}_2(C_d)|=8$ and odd
genus sum $T_{5b}(d)$ of row 5b, that every 2-Selmer class of $C_d$ come from a rational point. Here
$C_d$ is the curve $y^2=x^3-d^2x$. It differs from the row-5b form CR₃^5b only in that the condition
$\det M_{5b}=1$ is replaced by $T_{5b}(d)=1$. CR₃^TYZ_Cl is the same assertion with the genus sum
$T^{\mathrm{Cl}}_{5b}(d)=\sum_\pi\prod_{B\in\pi}\#2\mathrm{Cl}(\mathbb Q(\sqrt{-d_B}))\bmod 2$ of
Tian, Yuan and Zhang's genus class numbers in place of $T_{5b}(d)$, the sum running, as for
$T_{5b}(d)$, over the set partitions $\pi$ of the primes of $d$ with one block $d_B\equiv7$, one block
$d_B\equiv3$ and all others $d_B\equiv1\pmod8$.

**Proof sketch.** By Theorem 3.6, $\det M_{5b}=T_{5b}(d)$ for squarefree $d\equiv5\pmod8$, so
CR₃^TYZ implies CR₃^5b; CR₃^5b implies CR₃^Sel by Corollary 4.4; then apply
[the main theorem from the Selmer form of the rank hypothesis](main-theorem-selmer.md) in its form
with the minimal height hypothesis and CR₃^Sel alone. For the second form, Rédei's formula, which is
proved, gives $T^{\mathrm{Cl}}_{5b}(d)=T_{5b}(d)$ for squarefree $d\equiv5\pmod8$, so CR₃^TYZ_Cl is
equivalent to CR₃^TYZ, and the first form applies.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The certified rank hypothesis in Tian–Yuan–Zhang form](../rank-5b/certified-rank-tyz.md)
- [The certified rank hypothesis with class numbers](../redei/certified-rank-tyz-cl.md)

## Proof depends on

- [CR₃^TYZ implies CR₃^5b](../rank-5b/certified-rank-5b-of-tyz.md)
- [CR₃^5b implies CR₃^Sel](../rank-5b/certified-rank-sel-of-5b.md)
- [The main theorem from the Selmer form of the rank hypothesis](main-theorem-selmer.md)
- [CR₃ with class numbers is CR₃^TYZ](../redei/class-number-hypothesis.md)
- [Rédei's formula](../redei/redei-formula.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
- [Theorem 3.6](../../sources/rank-5b-locators.md#theorem-36)
- [Corollary 4.4](../../sources/rank-5b-locators.md#corollary-44)
- [Rédei's formulas](../../sources/redei-locators.md#redeis-formulas)
- [The hypothesis in Tian–Yuan–Zhang form](../../sources/rank-5b-locators.md#the-hypothesis-in-tian-yuan-zhang-form)
- [The hypothesis in class-number form](../../sources/redei-locators.md#the-hypothesis-in-class-number-form)
