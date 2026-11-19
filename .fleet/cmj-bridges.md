# Fowler's singular modulus degree

**Scoped stop.** `CMjDegreePrint` states the equality over ℚ of Fowler §2·1,
p. 613, using the normalized modular j, the primitive period discriminant, and
the proper ideal class number. The reading is recorded on fork issue #14,
comment 6973419601. The open glue is `CMPeriodJDescends`: for an actual CM
elliptic curve over L and a period at σ, its analytic j-value belongs to σ(L).
An existing theorem comparing this value with the j of a Weierstrass model of
that same scheme over L was not found.

**VERIFIED.** The complex pullback, full endomorphism ring, period,
multiplier ring ℤ[aτ], primitive discriminant, Picard cardinal and degree bound
all compile. The group-model uniformization and surjectivity checks also
compile. The conditional proof uses only the standard axioms; the live
discharge scan shows that it still assumes both the printed equality and the
one open comparison.

No fold was applied. Both counts remain 4 LEAF / 25 GLUE; the read-only preview
gives 5 LEAF / 24 GLUE once j descent is proved. See
[`docs/research/cmj-bridges.md`](../docs/research/cmj-bridges.md) for the exact gap
and [the verification files](../scratch/cmj-bridges/).
