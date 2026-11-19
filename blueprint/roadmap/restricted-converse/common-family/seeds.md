---
declaration: theorem
origin: cited
---

# Finite realization, unit seeds and contraction certificates

A *unit seed* is a finite compatible typed graph with symbol one, and a *minimum nonempty seed* one with
the least positive number of vertices (the empty configuration may also be a unit). A nonempty prime list is
*partitionable* if its vertices can be partitioned into nonempty clusters, each with a contraction tree,
whose contracted graph is a unit seed; the trees with the resulting types and incidences form a
*contraction certificate*. This makes no assertion about a Selmer group.

For a symbol satisfying the coefficient rules:

1. *(Finite realization.)* With finitely many old prime vertices and their mutual data fixed, any
   individually realizable types for new vertices and any prescription of the independent bits involving
   them are realized by distinct fresh primes outside a prescribed finite set; a contracted template can be
   replaced by a fresh prime with the same type and external incidences.
2. *(Minimum seeds.)* The value of a seed of least positive size is independent of its internal pair bits
   and depends only on its vertex types.
3. *(Certificates.)* A contraction certificate for a nonempty list makes its polynomial in the independent
   pair bits nonzero. In particular, a list with the same total type as a minimum nonempty seed of size $r$
   is partitionable as soon as it contains anchors for the first $r-1$ seed types and a nonempty remainder.

**Proof sketch.** (1) A fixed type is a reduced residue condition modulo a number supported on the label
set, including $8$, and a residue bit at an old prime is a nonzero residue class there. Choose the new
primes one at a time by the Chinese remainder theorem and Dirichlet's theorem, avoiding all earlier primes;
reciprocity gives the reverse bits, and graph dependence of the symbol makes the fresh representative
legitimate. (2) If $r\ge2$, a nonzero derivative in an internal bit would, by the contraction rule, give a
unit on $r-1$ nonempty vertices, against minimality. (3) Iterating the contraction identity along a forest
computes the contracted symbol; an output one shows that the original polynomial is nonzero. For the last
claim keep the $r-1$ anchors and merge the remainder into one cluster: equality of total types forces its
type to be the last seed type, and the internal bits of a minimum seed do not matter.

## Depends on

- [Compatible typed graphs and coefficient symbols](coefficient-symbols.md)

## Proof depends on

- [Arithmetic realization of the coefficient rules](coefficient-rules.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-realization` (L2151–2175),
  `ex:sec7-seed-partition` (L2176–2187) and `ex:sec7-seed-certificate` (L2188–2208)

## Manuscript check

Read in full by AI review as part of the step map of Section 7; these are finite combinatorial arguments,
and no step was found to fail. They are not yet checked line by line.
