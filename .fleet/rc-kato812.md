# Appendix E: Kato 8.12 handoff

**Verdict:** the Lean range gap at tex 7089 is filled conditional on the
draft `KatoProp812Print`. `finite_e1_812` proves the same finite (E.1)
product for every admissible family, using the (K5) smoothers and the
existing weighted transfer laws. In particular, odd primes of the fixed
level may divide the family support and occur in the full odd part of
every constituent conductor. The norm has no factor at such a prime:
Proposition 8.12 indexes its product by the difference of omitted
supports, and primes of the form level already belong to the lower
support. No manuscript error was found in this range.

All three modules under `ZInQKernel/Contrib/OneProof/RC/Kato812/` compile.
`KatoZetaInterface812.toOld` recovers the old bundle for every old exclusion
set; the wider norm also gives the repeated-two descent at a fixed odd
conductor. The scratch check reports only `propext`, `Classical.choice`,
and `Quot.sound` for every new theorem. No existing module or statement
was changed.

The print draft is UNVERIFIED and is not a LEAF. The reading desk should
check the original p. 186 and the inherited conditions listed in
[the report](../docs/research/rc-kato812.md). The identification with the
actual retained cohomology classes (`FixedKatoFiniteComparison`) and the
family-indexed reciprocity scalar remain separate.
