---
article_id: af_99984859aa545bcbfbe6205f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Natural.lt_spec, ZInQ.Compiler.Natural.divides_spec, ZInQ.Compiler.Natural.alpha_spec, ZInQ.Compiler.Natural.powerSpec_hierarchical, ZInQ.Compiler.Natural.binomial_spec, ZInQ.Compiler.Natural.orthogonal_spec, ZInQ.Compiler.Natural.mask_spec, ZInQ.Compiler.Natural.bitAnd_spec
---

# Semantics of the natural macros

Let a gadget or macro of the natural constructions be run from counter $c_0$ to $c_1$ on
argument polynomials in variables below $c_0$ that take natural values at every natural
point, producing $\varphi$. For every
$x:\mathbb N\to\mathbb N$, writing $a,b,\dots$ for the values of the arguments at $x$,
$$\exists y:[c_0,c_1)\to\mathbb N,\ \ \varphi\text{ holds naturally at }x[y]$$
is equivalent to the following relation (in hierarchical mode, the template is the power
template and its calls are read as in item 3 of the compilation statement):

| Macro | Relation |
| --- | --- |
| $\mathrm{lt}(a,b)$ | $a<b$ |
| $\mathrm{divides}(a,b)$ | $a\mid b$ |
| $\mathrm{congruent}(a,M,b)$ | $a\equiv b\pmod M$ ($a=b$ if $M=0$) |
| $\mathrm{odd}(x)$ | $x$ odd |
| $\mathrm{alpha}(X,b,N)$ | $b>3$ and $X=\alpha_b(N)$ |
| $\mathrm{power}(P,Q,R)$, flat or hierarchical | $P=Q^R$ |
| $\mathrm{binomial}(C,N,K)$ | $C=\binom NK$ |
| $\mathrm{orthogonal}(a,b)$ | $a\mathbin{\mathrm{AND}}b=0$ |
| $\mathrm{mask}(a,b)$ | $a\mathbin{\mathrm{AND}}b=a$ |
| $\mathrm{bitAnd}(z,x,y)$ | $z=x\mathbin{\mathrm{AND}}y$ |

The hypothesis on the arguments holds whenever the argument polynomials have nonnegative
coefficients, as all arguments in this chapter do ($Q+4$, $R+1$, $2X$, $a+b$,
$K\cdot N_j$, $R_j+D$ and so on).

**Proof sketch.** By the compilation statement each conjunction splits along the
intervals of its conjuncts, so each macro reduces to its listed conditions with the inner
macros replaced by their relations (induction in the order lt, divides, congruent, odd;
alpha; power; binomial; orthogonal, mask; bitAnd). Then: the four equational gadgets; alpha
is the alpha formula with its strict inequalities, divisibility and congruences replaced by
the gadgets, so soundness and completeness of the alpha formula apply; power is the power
formula, whose correctness gives $P=Q^R$ (hierarchical mode: the power-template semantics);
binomial is the binomial-digit statement; orthogonal and mask are Lucas's criterion with
the odd gadget; bitAnd is the AND gadget with orthogonality.

## Depends on

- [Natural constructions and their macros](natural-constructions.md)
- [The alpha sequence](../exponential/alpha-sequence.md)

## Proof depends on

- [Compilation and private witnesses over the naturals](natural-compilation.md)
- [The equational gadgets over the naturals](natural-atom-gadgets.md)
- [Soundness of the alpha formula](../exponential/alpha-equations-sound.md)
- [Completeness of the alpha formula](../exponential/alpha-equations-complete.md)
- [The power formula expresses exponentiation](../exponential/power-equations-correct.md)
- [Binomial coefficients as base-B digits](../exponential/binomial-digit.md)
- [Lucas's criterion for bit inclusion and disjointness](../exponential/lucas-bits.md)
- [The bitwise AND gadget](../exponential/bit-and.md)
- [Semantics of the power template](power-template-semantics.md)

## Sources

- [Section 10.2 binomial and bits](../../../../sources/compiler-natural-locators.md#section-102-binomial-and-bits)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
