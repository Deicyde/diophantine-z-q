---
article_id: af_d0e912d16601dc066c2d89a6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.recipe_heights
---

# Recipe heights

Let $B$ satisfy the hypotheses of the template heights: $B\ge2^{20}$, the constructors satisfy
the uniform bounds at $B$, every index $n$ of a division-polynomial constructor of the library
satisfies $|n|+1\le B$, $|\ell|+1\le B$, and $0\le T$, $T+1\le B$. Let the natural precision
circuit have the shape of the compiler chapter, in the form of upper bounds: five inputs, at
most $54{,}056$ explicit variables of which at least five are inputs, at most $125{,}327$
additions, $98{,}382$ multiplications and $15{,}845$ calls, and constants among
$0,1,-1,c_3,2,4,1399$. Then
$$\mathrm{Maj}_B(228,[\![\mathtt{power\_value}]\!]),\quad\mathrm{Maj}_B(233,[\![\mathtt{precision}]\!]),\quad
\mathrm{Maj}_B(235,[\![\mathtt{close}]\!]),\quad\mathrm{Maj}_B(251,[\![\mathtt{main}]\!]),$$
$$\mathrm{Maj}_B(252,[\![\mathtt{value\_union}]\!]),\quad\mathrm{Maj}_B(254,[\![\mathtt{value}]\!]),\quad
\mathrm{Maj}_B(256,[\![\mathtt{integers}]\!]).$$

**Proof sketch.** By the template majorant and the template heights (with monotonicity),
every template satisfies the majorant at its tabulated height. Then apply the recipe
rules in recipe order.

- $\mathtt{power\_value}$ has $3+79+3+196+190+5=476$ constraints (generator equations,
  natural rows for the $79$ witnesses, three constant definitions, $196$ additions,
  $190$ multiplications, root differences); its callees are $\mathtt{natural}$ ($223$),
  $\mathtt{raw\_add}$ ($21$), $\mathtt{multiply}$ ($214$) and three fixed-scalar templates
  ($17$): height $\max(4,223+3)+2=228$.
- $\mathtt{precision}$ has at most $3+54056+4+125327+98382+15845+5=293622\le2^{20}$ constraints; its
  callees add the power recipe ($228$): height $228+3+2=233$.
- $\mathtt{close}$ (sum of squares, $7$ calls: five signed encodings ($230$), the precision
  recipe ($233$), the coordinate window ($34$)): $233+2=235$.
- $\mathtt{main}$ (sum of squares, $\mathtt{close}$ and $\mathtt{value.test}$ ($249$)): $249+2=251$.
- $\mathtt{value\_union}$ (product, $\mathtt{value.exceptions}$ ($43$) and $\mathtt{main}$): $251+1=252$.
- $\mathtt{value}$ (sum of squares, $\mathtt{member}$ ($18$) and $\mathtt{value\_union}$): $252+2=254$.
- $\mathtt{integers}$ (sum of squares, one call of $\mathtt{value}$): $254+2=256$.

All constraint counts are at most $2^{20}\le B$. The counts for the two model-evaluation
recipes come from the translation and the shape of the natural circuit.

## Depends on

- [Syntax heights](syntax-height.md)
- [The power-value recipe](../../syntax/recipes/recipe-power-value.md)
- [The precision recipe](../../syntax/recipes/recipe-precision.md)
- [The outer composition recipes](../../syntax/recipes/outer-recipes.md)
- [The template library](../../syntax/templates/template-library.md)

## Proof depends on

- [Templates satisfy the height majorant](node-majorant.md)
- [Recipes satisfy the height majorant](recipe-majorant.md)
- [Template heights](template-heights.md)
- [Closure rules for the height majorant](majorant-rules.md)
- [Translation of a natural circuit into a model-evaluation recipe](../../syntax/recipes/model-evaluation-translation.md)
- [Shape of the natural precision circuit](../../compiler/natural/universal/circuit-node-counts.md)

## Sources

- [Section 12.1 syntax heights](../../../sources/size-locators.md#section-121-syntax-heights)
- [Section 12.1 checked facts](../../../sources/size-locators.md#section-121-checked-facts)
- [Height traversal](../../../sources/size-locators.md#height-traversal)
