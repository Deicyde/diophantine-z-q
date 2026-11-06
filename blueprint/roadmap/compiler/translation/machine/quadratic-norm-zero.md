---
article_id: af_21c478969889e662f347eaad
declaration: lemma
origin: cited
---

# Norm zero implies zero

For $a,b\in\mathbb Q$, if $a^2-2b^2=0$ then $a=b=0$. Equivalently, an element $a+bs$ of
$K_0$ is zero exactly when its norm $\operatorname N(a+bs)=a^2-2b^2$ is zero, so the exact test
"norm is zero" decides whether a field element given by its pair of components vanishes.

**Proof sketch.** Clear denominators: if $(a,b)\ne(0,0)$, scale to a primitive integer
solution of $a^2=2b^2$. Then $a$ is even, $a=2a'$, so $b^2=2a'^2$ and $b$ is even too,
contradicting primitivity. (Equivalently, $2$ is not a square in $\mathbb Q$.)

## Depends on

None.

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-translation-locators.md#section-103-precision-ir)
