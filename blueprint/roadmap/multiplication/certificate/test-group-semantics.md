---
article_id: af_6bdaa52fe1d398a192eaf759
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.testGroup_rel_iff, ZInQ.Mult.testGroup_rel_iff_codes
---

# Semantics of the test-group template

For all $c_0,c_1,c_2,c_3\in\mathbb Z$ and all
rational pairs $D_1,\dots,D_{12}$,
$$\mathrm{Rel}_{\mathtt{test\_group}}\bigl(\iota(c_0),\iota(c_1),\iota(c_2),\iota(c_3),D_1,\dots,D_{12}\bigr)
\iff\exists\,h,z_1,z_2,z_3\in\mathbb Z:\ h\ne0,\ h\ne c_0,\ [D_j]=\tau_j(h,z;c)\ (1\le j\le12).$$
(The template's output pairs $D_0,\dots,D_{11}$ are $D_1,\dots,D_{12}$ here.) The four
inputs must be canonical codes, as they are in every use: the raw addition contract is only
valid on canonical codes.

**Proof sketch.** By the evaluation of calls and the lifting of private blocks, the relation
holds iff there are values of the $162$ witnesses satisfying every conjunct. ($\Rightarrow$)
The membership calls make each $F_i$ a code $\iota(f_i)$ (accepted inputs have unique
indices). Since $\operatorname{neg}(\iota(c_i))=\iota(-c_i)$ is canonical, raw addition gives
$V_i=\iota(f_i-c_i)$. The atoms $\operatorname{fin}(F_0)$ and $\operatorname{fin}(V_0)$ say
$f_0\ne0$ and $f_0\ne c_0$. By the local-template semantics the three calls on each of the
eight points give $\zeta_i=z(\Pi_i)$, $\lambda_i=L(\zeta_i)$ and $\rho_i=1/x(\Pi_i)$; the
inverse atoms give $\lambda_0,\lambda_4\ne0$; the ratio equations give
$q_{\sigma,i}=\lambda_{4\sigma+i}/\lambda_{4\sigma}$; and the final pair equations say
$[D_j]=\tau_j$. Take $h=f_0$, $z_i=f_i$. ($\Leftarrow$) Put $F_0=\iota(h)$, $F_i=\iota(z_i)$,
$V_0=\iota(h-c_0)$, $V_i=\iota(z_i-c_i)$, choose the member and raw-addition blocks by
completeness of those templates, $\zeta,\lambda,\rho$ as computed, the inverse witnesses
$1/N(\lambda_0)$ and $1/N(\lambda_4)$, which exist by the nonvanishing lemma, and the ratios.

## Depends on

- [The test-group template](../../syntax/templates/template-test-group.md)
- [The twelve local tests](twelve-tests.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Accepted inputs have unique indices](../../model/membership-indices.md)
- [Polynomial membership in the doubled group](../../model/membership.md)
- [Raw addition](../../model/raw-addition.md)
- [Semantics of the local-parameter, inverse-abscissa and logarithm templates](local-templates.md)
- [The truncated logarithm does not vanish on nonzero multiples of $P_0$](../local/logarithm-nonvanishing.md)
- [Pair arithmetic represents the quadratic field](../../syntax/field-pair-arithmetic.md)
- [Evaluation of a template call](../../syntax/language/call-semantics.md)
- [Private witness blocks](../../syntax/language/existential-lifting.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)
- [The generator certificate](../../model/generator.md)
- [Mordell-Weil for $E/K_0$ from the descent](../../model/descent/mordell-weil-from-descent.md)

## Sources

- [Twelve tests](../../../sources/multiplication-locators.md#twelve-tests)
- [Multiplication certificate generator](../../../sources/multiplication-locators.md#multiplication-certificate-generator)
