---
article_id: af_106a3a57d021fd5dd896df13
declaration: theorem
origin: cited
---

# Node statistics of the halting circuit and the power template

1. The node list of the universal halting circuit $\mathcal H$ has $293{,}568$ nodes:
   $54{,}049$ variable nodes, $6$ constant nodes with values $0,1,2,4,1399,-1$ in node order,
   $125{,}307$ additions, $98{,}361$ multiplications and $15{,}845$ calls. Its first two nodes are
   the variable nodes of $X_0$ and $X_1$.
2. The node list of the power template $\mathcal P$ has $474$ nodes: $82$ variable nodes, $6$
   constant nodes with values $0,1,4,2,3,-1$ in node order, $196$ additions,
   $190$ multiplications and no calls.

Both items are closed decidable statements about the hash-consed node encodings of two
explicit constructions: the packed construction of the explicit interpreter, and the flat
power macro. They are finite computations; they do not involve $c_3$ or any astronomically
large constant.

## Depends on

- [The universal halting circuit](halting-polynomial.md)
- [The power template](../formulas/power-template.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
