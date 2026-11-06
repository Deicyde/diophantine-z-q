---
article_id: af_ce847f5a046049a9c3c7a217
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.pointRef_eval_generator, ZInQ.Syntax.generatorConstraints_eq_zero_iff
---

# Values of the point references

Let $x:\mathbb N\to\mathbb Q$ satisfy the three generator constraints of a model-evaluation
recipe, $8x_{g_0}=1641$, $4x_{g_1}=-15465$ and $32x_{g_2}=87483$. Then
$$\mathrm{ref}(-1)(x)=\iota(0),\qquad\mathrm{ref}(-2)(x)=\iota(1),\qquad\mathrm{ref}(-3)(x)=\iota(-1),$$
that is, the codes of $O$, $P_0$ and $-P_0$. Explicitly
$\iota(1)=(0,\ 1641/8,\ -145,\ -15465/4,\ 87483/32)$ and
$\iota(-1)=(0,\ 1641/8,\ -145,\ 15465/4,\ -87483/32)$.

**Proof sketch.** The constraints give $x_{g_0}=1641/8$, $x_{g_1}=-15465/4$,
$x_{g_2}=87483/32$. The code of $P_0=((1641-1160s)/8,(-123720+87483s)/32)$ is
$(0,1641/8,-145,-15465/4,87483/32)$ because $1160/8=145$ and $123720/32=15465/4$; the code
of $-P_0=(x,-y)$ negates the last two coordinates; the identity has code $(1,0,0,0,0)$.

## Depends on

- [Point references](point-references.md)
- [The codes of multiples of the generator](../../model/point-codes.md)

## Sources

- [Appendix C opening](../../../sources/syntax-locators.md#appendix-c-opening)
- [Section 3](../../../sources/syntax-locators.md#section-3-point-codes)
