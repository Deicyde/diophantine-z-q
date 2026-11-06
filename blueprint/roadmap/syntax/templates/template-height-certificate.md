---
article_id: af_8091b9cd8013f74357a38a5c
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.heightTemplate, ZInQ.Syntax.heightBuild_formula
---

# The height certificate template

The template $\mathtt{height\_certificate}$ has $36$ parameters and $35106$ witnesses
($35142$ variables). Parameters: points $P_0,P_1,P_2$ ($P_i=(X_{5i},\dots,X_{5i+4})$),
$\ell=X_{15}$ and points $C_0,\dots,C_3$ ($C_i=(X_{16+5i},\dots,X_{20+5i})$). Witnesses in
allocation order:

- for $i=0,1,2$ with base $b=36+11i$: a $\mathtt{member}$ block $[b,b+7)$, then
  $a_{i0}=X_{b+7}$, $a_{i1}=X_{b+8}$, $b_i=X_{b+9}$ and the inverse witness $u_i=X_{b+10}$;
- for $k=0,\dots,8$ with base $c=69+3897k$: slopes $s_{k,0},s_{k,1},s_{k,2}=X_c,X_{c+1},X_{c+2}$
  and three $\mathtt{slope}$ blocks $[c+3+1298l,\ c+1301+1298l)$, $l=0,1,2$.

The nine quantities are $Q=(a_{00},a_{01},b_0,a_{10},a_{11},b_1,a_{20},a_{21},b_2)$. The formula
is the conjunction of, in this order:

1. for $i=0,1,2$: $\langle\mathtt{member}[P_i]\rangle$, $b_iu_i\doteq1$,
   $b_i\,(P_i)_1\doteq a_{i0}$, $b_i\,(P_i)_2\doteq a_{i1}$;
2. for $k=0,\dots,8$: $s_{k,0}+s_{k,1}+s_{k,2}\doteq Q_k$, and
   $\langle\mathtt{slope}[s_{k,l},\ell,C_0,\dots,C_3]\rangle$ for $l=0,1,2$.

The polynomial is $\kappa$ of this conjunction, squared. It writes the three abscissas as
$a_{i0}/b_i+(a_{i1}/b_i)s$ with $b_i\ne0$, expresses each of the nine rational quantities as
a sum of three slopes, and imposes the slope certificate on all $27$ slopes; it is the
unguarded certificate, and false triples in the finite box are excluded separately.

This is a definition (template index $8$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [The membership template](../template-member.md)
- [The slope template](template-slope.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
