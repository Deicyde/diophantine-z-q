---
article_id: af_ab56121ec985cb71290b9a86
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.testGroupTemplate, ZInQ.Syntax.testGroupBuild_formula
---

# The test-group template

The template $\mathtt{test\_group}$ has $44$ parameters and $162$ witnesses ($206$
variables). Parameters: points $C_0,\dots,C_3$ ($C_i=(X_{5i},\dots,X_{5i+4})$) and output pairs
$D_0,\dots,D_{11}$ ($D_j=(X_{20+2j},X_{21+2j})$). Witnesses in allocation order:

- points $F_i=(X_{44+5i},\dots,X_{48+5i})$ and $V_i=(X_{64+5i},\dots,X_{68+5i})$, $i=0,\dots,3$;
- for $i=0,\dots,3$: a $\mathtt{member}$ block of $7$ and a $\mathtt{raw\_add}$ block of $6$
  (starts $84,91,97,104,110,117,123,130$);
- for $i=0,\dots,7$, with base $b=136+7i$: pairs $\zeta_i=(X_b,X_{b+1})$, $\lambda_i=(X_{b+2},X_{b+3})$,
  $\rho_i=(X_{b+4},X_{b+5})$, then a $\mathtt{raw\_z}$ block $\{X_{b+6}\}$ and empty
  $\mathtt{log25}$ and $\mathtt{raw\_inverse\_x}$ blocks at $b+7$;
- inverse witnesses $u_1=X_{192}$, $u_2=X_{193}$;
- ratio pairs $q_{0,1},q_{0,2},q_{0,3},q_{1,1},q_{1,2},q_{1,3}$ at $X_{194},\dots,X_{205}$.

Let $\Pi_i=F_i$ and $\Pi_{4+i}=V_i$ ($i=0,\dots,3$), and let the twelve tests be
$$\tau=\bigl(\rho_0,\rho_1,\rho_2,\rho_3,\ \bar\rho_4,\bar\rho_5,\bar\rho_6,\bar\rho_7,\ q_{0,1}-\bar q_{1,1},\ q_{0,2}-\bar q_{1,2},\ q_{0,3}-\bar q_{1,3},\ q_{0,1}\cdot q_{0,2}-q_{0,3}\bigr).$$
The formula is the conjunction of the following items, in this order:

1. for $i=0,\dots,3$: $\langle\mathtt{member}[F_i]\rangle$ and
   $\langle\mathtt{raw\_add}[F_i,\mathrm{neg}(C_i),V_i]\rangle$;
2. $\mathrm{fin}(F_0)$ and $\mathrm{fin}(V_0)$;
3. for $i=0,\dots,7$: $\langle\mathtt{raw\_z}[\Pi_i,\zeta_i]\rangle$,
   $\langle\mathtt{log25}[\zeta_i,\lambda_i]\rangle$, $\langle\mathtt{raw\_inverse\_x}[\Pi_i,\rho_i]\rangle$;
4. $N(\lambda_0)\,u_1\doteq1$ and $N(\lambda_4)\,u_2\doteq1$;
5. for $\sigma=0,1$ and $i=1,2,3$: $\lambda_{4\sigma}\cdot q_{\sigma,i}\doteq\lambda_{4\sigma+i}$;
6. for $j=0,\dots,11$: $D_j\doteq\tau_j$.

Each call uses its block listed above. The polynomial is $\kappa$ of this conjunction,
squared.

With $V_i=F_i-C_i$, the tests are four inverse abscissas at $F_0,\dots,F_3$, the conjugates
of the inverse abscissas at $V_0,\dots,V_3$, three differences of $L$-ratios and the product
test; their use is the multiplication chapter's.

This is a definition (template index $6$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [The membership template](../template-member.md)
- [The raw addition template](../template-raw-add.md)
- [The local parameter template](template-raw-z.md)
- [The truncated logarithm template](template-log25.md)
- [The inverse abscissa template](template-raw-inverse-x.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
