---
article_id: af_1d325a779752858862833df4
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.closeRecipe, ZInQ.Syntax.mainRecipe, ZInQ.Syntax.valueUnionRecipe, ZInQ.Syntax.valueRecipe, ZInQ.Syntax.integersRecipe
---

# The outer composition recipes

Five composition recipes assemble the ordinary-value relation; each is built with one
allocation counter starting at its parameter count, fresh ranges first, then the calls in
order. Write $\mathbf X_a=(X_a,\dots,X_{a+4})$.

1. $\mathtt{close}$ (sum of squares), parameters $N=\mathbf X_0$, $K=\mathbf X_5$, $t=X_{10}$.
   Fresh points $A=\mathbf X_{11}$, $L=\mathbf X_{16}$, $J=\mathbf X_{21}$ and
   $E_0,\dots,E_4=\mathbf X_{26},\mathbf X_{31},\dots,\mathbf X_{46}$. Calls:
   $\mathtt{value.signed\_encode}[\Sigma_i,E_i]$ for $(\Sigma_0,\dots,\Sigma_4)=(N,K,A,L,J)$ (starts
   $51+140654i$); $\mathtt{precision}[E_0,\dots,E_4]$ (start $703321$);
   $\mathtt{value.close\_coordinates}[A,L,J,t]$ (start $292890196157$). $11$ parameters,
   $292890196199$ witnesses.
2. $\mathtt{main}$ (sum of squares), parameters $N=\mathbf X_0$, $t=X_5$. Fresh point
   $K=\mathbf X_6$. Calls: $\mathtt{close}[N,K,t]$ (start $11$) and
   $\mathtt{value.test}[N,K,t]$ (start $292890196210$). $6$ parameters, $292890231486$
   witnesses.
3. $\mathtt{value\_union}$ (product), parameters $N=\mathbf X_0$, $t=X_5$. Calls:
   $\mathtt{value.exceptions}[N,t]$ (start $6$) and $\mathtt{main}[N,t]$ (start $412$). $6$
   parameters, $292890231892$ witnesses.
4. $\mathtt{value}$ (sum of squares), parameters $N=\mathbf X_0$, $t=X_5$. Calls:
   $\mathtt{member}[N]$ (start $6$) and $\mathtt{value\_union}[N,t]$ (start $13$). $6$ parameters,
   $292890231899$ witnesses.
5. $\mathtt{integers}$ (sum of squares), parameter $t=X_0$. Fresh point $N=\mathbf X_1$. Call:
   $\mathtt{value}[N,t]$ (start $6$). $1$ parameter, $292890231904$ witnesses.

Thus, with call polynomials as in the semantics of recipes,
$$[\![\mathtt{integers}]\!]=\mathtt{value}[X_1,\dots,X_5,X_0;6]^2,\qquad
[\![\mathtt{value}]\!]=\mathtt{member}[\mathbf X_0;6]^2+\mathtt{value\_union}[\mathbf X_0,X_5;13]^2,$$
$$[\![\mathtt{value\_union}]\!]=\mathtt{value.exceptions}[\mathbf X_0,X_5;6]\cdot\mathtt{main}[\mathbf X_0,X_5;412],$$
and similarly for $\mathtt{main}$ and $\mathtt{close}$. The same coordinates of $K$ occur in
$\mathtt{close}$ and $\mathtt{value.test}$; the exceptional branch and the main branch have
disjoint private blocks.

The starts and witness counts from the precision call on are those for a precision recipe
with $292{,}889{,}492{,}836$ witnesses, the bound of the precision recipe; in general each of
them shifts with the witness count of the recipe called (for instance $\mathtt{close}$ has
$703310+w+53$ witnesses when precision has $w$), so the displayed values are upper bounds.

This is a definition.

## Depends on

- [Semantics of templates and recipes](../template-semantics.md)
- [The precision recipe](recipe-precision.md)
- [The signed-encoding template](../templates/template-signed-encode.md)
- [The coordinate-window template](../templates/template-close-coordinates.md)
- [The value-test template](../templates/template-value-test.md)
- [The exceptional-values template](../templates/template-exceptions.md)
- [The membership template](../template-member.md)

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
