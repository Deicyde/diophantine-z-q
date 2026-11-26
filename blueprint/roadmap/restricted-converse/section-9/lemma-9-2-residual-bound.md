---
article_id: af_3ebc56590748296774071a2b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Lim.ex_limits_residual_bound_final_lim, ZInQ.Manuscript.RC.GlueSweep.Lim.card_primeSetT_le_lim, ZInQ.Manuscript.RC.GlueSweep.Lim.card_places_add_ram_le_lim
---

# Lemma 9.2: the reduced generic residual rank bound

Assume four specializations of statements of Milne's *Arithmetic Duality Theorems* (PRINT), each read
through GLUE: Theorems I.4.10 and I.5.1 for totally complex fields, and Corollary I.2.3 and Theorem
I.2.8 for $\mathbb F_2$-modules (trivial ones for I.2.3) over finite extensions of $\mathbb Q_p$. The
two global ones are not checked against the print; none is proved, and none is an input of the reduction
of Theorem 5.3. Assume also the Kummer sequence for $H^1(G_{K,S_T},\mathbb F_2)$ with the $S$-unit
theorem (`kummer`, GLUE); the genus bound `genus` (ELLIOT: the manuscript proves it); the manuscript's
table of local condition dimensions at the charged places (`hcond`, ELLIOT); rank bounds for finite free
models of the global and local terms of the Selmer cone (`hG`, `hL`, ELLIOT: the manuscript gets them
from Lemma 9.1); Nekovář's support comparison, Proposition 7.8.8(ii) (`SupportChangeInput`, GLUE); and a
change of local conditions at the active places (ELLIOT) whose quotient $W$ is acyclic (`hW`, ELLIOT).

Let $K=\mathbb Q(\sqrt k)$ be imaginary quadratic with $\omega(k)\le A$, let $N\ne0$, and let $j$ be the
number of derivative primes. After the support change and the change of conditions at the active
places, the original-support Selmer complex $C$ over a local coefficient ring has total residual
cohomology dimension
$$N(E,A,j)\le56\,\omega(2N)+8A+56j+70,$$
whatever the number and size of the active primes.

With $v=\omega(2N)$, let $T$ be the set of rational primes below the places above $2N$, the moving prime
and the derivative primes, together with the primes ramified in $K$; put $s=|T|$, let $S_T$ be the
places of $K$ above $T$ and $r$ the number of ramified primes. Then
$$s\le v+A+1+j,\tag{5.1a}$$
$$|S_T|\le2s-r,\qquad\dim_{\mathbb F_2}\mathrm{Cl}(\mathcal O_{K,S_T})[2]\le r-1.\tag{5.1b}$$
Lean proves (5.1a) for the actual ramified primes with no input (`card_primeSetT_le_lim`) and the place
count of (5.1b) as $|S_T|+r\le2s$ (`card_places_add_ram_le_lim`). Lean never states the class-group
half of (5.1b): the dimension `clDim` is a free number, and `kummer` and `genus` together say only
$h^1(G_{K,S_T},\mathbb F_2)\le|S_T|+r$.

The manuscript bounds the rank of the generic model obtained by reducing to characteristic two and
inverting $t$; the Lean statement works over any local coefficient ring and bounds the total residual
cohomology dimension, which is the rank of a minimal model. The Lean Selmer data `SelData S` are
arbitrary and $E$ never appears; only `hG`, `hL` and `hcond` tie the complex to the cohomology of $K$.

The reduction of Theorem 5.3 does not use this theorem: the field `PreLeaves.eq35` of [the remaining
hypotheses](../remaining-hypotheses.md) asks directly for models of size at most the cap of (5.1).

**Proof sketch.** The global complex over the smaller support has total residual dimension at most
$8s+2$, by the Kummer sequence, (5.1b), inflation and the global Euler characteristic. Local duality
and the table charge at most $48$ for each charged rational prime, and the complex place at most four.
With (5.1a) this is [(5.1)](equation-5-1-total-rank.md) for the smaller-support cone. The support
comparison and the acyclicity of the active quotient after inverting $t$ carry the bound to the
original support.

## Depends on

None.

## Proof depends on

- [(5.1): the total rank of the smaller-support cone](equation-5-1-total-rank.md)

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
