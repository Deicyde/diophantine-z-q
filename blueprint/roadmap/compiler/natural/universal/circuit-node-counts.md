---
article_id: af_858623715689082574247d1b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.precisionCircuit_counts, ZInQ.Compiler.Universal.precisionCircuitOf_explicitVars, ZInQ.Compiler.Universal.precisionCircuit_addMulBound, ZInQ.Compiler.Universal.precisionCircuitOf_countKind_call, ZInQ.Compiler.Universal.precisionCircuit_consts
---

# Shape of the natural precision circuit

The five-input natural precision circuit $\mathcal N$ has:

1. $5$ inputs and $54{,}056$ explicit variables, namely $0,\dots,8$ followed by the explicit
   witnesses of $\mathcal H$ shifted by $7$ (so $54{,}051$ explicit witnesses);
2. $15{,}845$ calls of the power template, with private blocks of $79$ variables, and
   variable count $54{,}056+79\cdot15{,}845=1{,}305{,}811$, so a natural zero with inputs
   $c\in\mathbb N^5$ has $1{,}305{,}806$ witness coordinates;
3. at most $125{,}327$ additions and at most $98{,}382$ multiplications, and $15{,}845$ calls;
4. constants among $0,1,-1,c_3,2,4,1399$, where $c_3,2,4,1399$ are distinct.

The specification chapter's [witness accounting](../../../syntax/recipes/witness-accounting.md)
uses items 2 to 4 for the recipe translation; this statement proves them from the node
statistics of $\mathcal H$ and the size of the program literal. The constant $c_3$ is never
evaluated.

**Proof sketch.** From the definition of $\mathcal N$ and the counts of $\mathcal H$: the
explicit variables are the $9$ new ones and the $54{,}047$ shifted witnesses of $\mathcal H$;
the calls are those of $\mathcal H$ with shifted blocks. The modified copy of the node list of
$\mathcal H$ has the same additions and multiplications; the appended part has four pairing
polynomials ($4$ additions and $4$ multiplications each) and the sum of five squares ($5$
multiplications and $4$ additions), that is $20$ additions and $21$ multiplications, so the
bounds of $\mathcal H$ give item 3. The constants of $\mathcal H$ are among $0,1,2,4,-1,1399$;
the copy replaces the variable node of $X_0$ by the constant node $c_3$, and the appended part
adds $1,2,-1$. Item 4 needs only $c_3>1399$, from the size of the program literal.

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
