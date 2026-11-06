---
article_id: af_858623715689082574247d1b
declaration: theorem
origin: cited
---

# Shape of the natural precision circuit

The five-input natural precision circuit $\mathcal N$ has:

1. $5$ inputs and $54{,}056$ explicit variables, namely $0,\dots,8$ followed by the explicit
   witnesses of $\mathcal H$ shifted by $7$ (so $54{,}051$ explicit witnesses);
2. $15{,}845$ calls of the power template, with private blocks of $79$ variables, and
   variable count $54{,}056+79\cdot15{,}845=1{,}305{,}811$, so a natural zero with inputs
   $c\in\mathbb N^5$ has $1{,}305{,}806$ witness coordinates;
3. $293{,}620$ nodes: $54{,}056$ variable nodes, $10$ constant nodes with values
   $c_3,0,1,2,4,1399,-1,1,2,-1$ in node order, $125{,}327$ additions, $98{,}382$
   multiplications and $15{,}845$ calls;
4. constants other than $0,1,-1$ which are, in order of first occurrence, $c_3,2,4,1399$,
   and these four values are distinct.

The syntax chapter's [statement on the shape of the natural precision circuit](../../../syntax/recipes/natural-circuit-statistics.md)
records items 2 to 4 for the recipe translation; this statement is their proof from the
finite checks on $\mathcal H$, the power template and the wrapper. The constant $c_3$ is
never evaluated.

**Proof sketch.** From the definition of $\mathcal N$ and the counts of $\mathcal H$: the
explicit variables are the $9$ new ones and the $54{,}047$ shifted witnesses of $\mathcal H$;
the calls are those of $\mathcal H$ with shifted blocks. For the nodes: the modified copy of
the node list of $\mathcal H$ has the same length and kinds except that the variable node of
$X_0$ becomes the constant node $c_3$ (so $54{,}048$ variable and $7$ constant nodes, values
$c_3,0,1,2,4,1399,-1$, by the node-statistics check); the appended part has $8$ variable nodes,
$3$ constants $1,2,-1$, four pairing polynomials of $8$ nodes each ($4$ additions and $4$
multiplications) and the sum of five squares ($5$ multiplications and $4$ additions), that
is $20$ additions and $21$ multiplications. Item 4 needs only $c_3>1399$, from the size of
the program literal.

## Depends on

- [The five-input natural precision circuit](precision-circuit.md)
- [Natural semantics of a natural circuit](../formulas/natural-circuit-semantics.md)

## Proof depends on

- [Counts of the universal halting circuit](halting-circuit-counts.md)
- [Node statistics of the halting circuit and the power template](halting-node-check.md)
- [Size of the program literal](wrapper-code-size.md)

## Sources

- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
