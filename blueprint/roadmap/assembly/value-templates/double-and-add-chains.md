---
article_id: af_ade280875002b2b1c6820ac7
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Assembly.chain_value, ZInQ.Assembly.chain_satisfiable, ZInQ.Assembly.chainBuild_binDigits_value, ZInQ.Assembly.chainCount_contacts
---

# Double-and-add chains

Let $m\in\mathbb Z$, $k\in\mathbb N$, and consider the double-and-add chain for $k$ on the point
$p=\iota(m)$, as defined for the exceptional-values template: starting from
$\mathrm{out}=O$, $\mathrm{base}=p$, it takes for each odd bit a fresh point $\sigma_i$ with the call
$\langle\mathtt{raw\_add}[\mathrm{out},\mathrm{base},\sigma_i]\rangle$ and for each further bit a fresh point
$\delta_i$ with $\langle\mathtt{raw\_add}[\mathrm{base},\mathrm{base},\delta_i]\rangle$. Then:

1. for every assignment of rational $5$-tuples to the fresh points such that all raw-addition
   relations of the chain hold, the value of the chain (its final $\mathrm{out}$) is
   $\iota(km)$;
2. there is such an assignment.

The number of raw additions is the number of one bits of $k$ plus the bit length of $k$
minus one ($0$ for $k=0$). For $k=0,15,20,24,30,60$ this gives $0,7,6,6,8,9$.

**Proof sketch.** Induction along the chain with the invariant that after $i$ steps
$\mathrm{base}=\iota(2^im)$ and $\mathrm{out}=\iota(k_im)$, where $k_i=k\bmod2^i$. Both inputs of
every raw addition are then canonical codes, so raw addition forces the fresh output to be
$\iota(k_im+2^im)$ or $\iota(2^{i+1}m)$, which preserves the invariant; at the end $k_i=k$. For
2, assign each fresh point the code forced in this way; raw addition is complete on
canonical codes. Initially $\mathrm{out}=O=\iota(0)$ is the literal code. No property of $P_0$
beyond lying on $E$ is used.

## Depends on

- [The exceptional-values template](../../syntax/templates/template-exceptions.md)
- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Raw addition](../../model/raw-addition.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)

## Sources

- [Section 10.4 translation](../../../sources/assembly-locators.md#section-104-translation)
- [Saved specification outer recipes](../../../sources/assembly-locators.md#saved-specification-outer-recipes)
