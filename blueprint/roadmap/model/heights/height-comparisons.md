---
article_id: af_b3cd8e30bf3a4afbb6988ca8
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.height_comparisons
---

# Two explicit integer comparisons

The following inequalities between natural numbers hold:
$$41^3\cdot676\cdot392^{36}<9^{108},\qquad 392<41^3 .$$
Equivalently $\frac{\log(41^3\cdot676)}{108}+\frac{\log392}{3}<\log9$ and
$\log41>\frac{\log392}{3}$. This is a finite computation: the two sides of the first
inequality have $102$ and $104$ decimal digits.

**Proof sketch.** Evaluate both sides; $41^3=68921$. The logarithmic forms follow by
monotonicity of $\log$ after multiplying the first by $108$ and the second by $3$.

## Depends on

None.

## Sources

- [Height comparison](../../../sources/model-locators.md#height-comparison)
