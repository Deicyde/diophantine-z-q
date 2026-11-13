---
article_id: af_04c6f9fa0fb007bf6f3af069
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.NodeCheck.HaltingAddMulCheck, ZInQ.Compiler.NodeCheck.haltingAddMulCheck, ZInQ.Compiler.Universal.HaltingNodeCheck, ZInQ.Compiler.NodeCheck.haltingNodeCheck, ZInQ.Compiler.NodeCheck.haltingNodeCheck_of_addMul, ZInQ.Compiler.Universal.haltingCircuit_nodeStats
---

# Exact node statistics of the halting circuit

The node list of the universal halting circuit $\mathcal H$ has exactly $125{,}307$ additions
and $98{,}361$ multiplications, hence $293{,}568$ nodes in all.

So the bounds of the [node statistics](halting-node-check.md) are attained. Apart from a form of the
main theorem that takes it as a hypothesis, no other statement uses the equality.

**Proof sketch.** A closed computation: run the construction with its hash-consing table and
count the node kinds. The bounds give one inequality; the other needs every request not
counted as a repeat to create a new node. The run is checked in $89$ consecutive pieces by a
builder without a table: pinned data says, for each request, whether its node already exists
and where, and the builder confirms each claimed new node by comparing it with recent nodes
or with sorted lists of older ones. A simulation argument shows that this builder makes the
same requests and creates the same nodes as the hash-consing one.

## Depends on

- [The universal halting circuit](halting-polynomial.md)
- [Node statistics of the halting circuit and the power template](halting-node-check.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
