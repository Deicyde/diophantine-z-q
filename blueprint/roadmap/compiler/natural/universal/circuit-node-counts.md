---
article_id: af_858623715689082574247d1b
declaration: theorem
origin: cited
---

# Node statistics of the compiled circuits

1. The universal halting circuit $\mathcal H$ has $293{,}568$ nodes: $54{,}049$ variable nodes,
   $6$ constant nodes (with values $0,1,2,4,1399,-1$ in order of first occurrence),
   $125{,}307$ additions, $98{,}361$ multiplications and $15{,}845$ calls.
2. The natural precision circuit $\mathcal N$ has $293{,}620$ nodes: $54{,}056$ variable nodes,
   $10$ constant nodes (values $c_3,0,1,2,4,1399,-1,1,2,-1$ in node order), $125{,}327$
   additions, $98{,}382$ multiplications and $15{,}845$ calls; its constants other than
   $0,1,-1$ are, in order of first occurrence, $c_3,2,4,1399$.
3. The power template has $474$ nodes: $82$ variable nodes, $6$ constant nodes (values
   $0,1,4,2,3,-1$), $196$ additions and $190$ multiplications.

Item 1 is a closed decidable statement about the hash-consed node encoding of the packed
construction of the explicit interpreter, and item 3 about that of the power macro; item 2
follows from item 1 and the definition of $\mathcal N$ (the appended part has $8$ variable
nodes, $3$ constants, $20$ additions and $21$ multiplications), together with
$c_3\notin\{0,1,-1,2,4,1399\}$. The constant $c_3$ is never evaluated.

## Depends on

- [The universal halting circuit](halting-polynomial.md)
- [The five-input natural precision circuit](precision-circuit.md)
- [The power template](../formulas/power-template.md)

## Proof depends on

- [Size of the program literal](wrapper-code-size.md)

## Sources

- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
