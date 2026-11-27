# Retired review rows

`reviews-retired.tsv` keeps the rows of `reviews.tsv` whose field is no longer an open hypothesis: the field was
replaced by a fold on wip/leaf-fold33b before the review landed on main (kleimanPicZeroProper by
kleimanPicZeroProper954, bostLowerBoundPrinted and gaudronRemondThm14Printed by the r3-residual `An` leaves,
javanpeykarPrintedMapHF by javanpeykarThm111, elkiesX6StarEvery by elkiesX6StarEveryIdeal, hGZ by hGZss). The
readings were of the old statements and do not rate the new ones; they are kept here as a record.

Later (batch TailZ72): the rows of gonzalezRotgerThm512X6 (replaced by gonzalezRotgerThm512X6RCF, gr512-bridge), bergerPrintedV (replaced by bergerPrintedVT, pb-pst) and modularHTPrinted (replaced
by modularHTCoeff, htnew-assembly) moved here for the same reason.

Later (fold-b105, pb-p1): the row of panPrintedP (replaced by panPrintedF, Pan over Fontaine's B_st as printed) moved here for the same reason.

Later (ds965-reroute-fold, #197): the rows of dsThm965AtPrimes moved here. The field was removed by a reroute (its readers now use modularHTCoeff and dsThm966Printed), with no replacement leaf; the readings, one of them a human reading of the characteristic-equation clause, are kept here as a record.

Later (item-m-fold, the rows of #219): the row of gaudronRemondSec9LowerAnSS moved here. The field was replaced by
gaudronRemondSec9LowerGR1Weak, Cor. 8.4 of Gaudron-Rémond (Comment. Math. Helv. 89 (2014)) weakened in Lean over the
height of a semi-abelian model, and gaudronRemondThm14Printed by gaudronRemondThm14GR1, the same theorem over that
height, with the leaf egaIV_9_7_7_OL; with it the new rows imply the old fields in Lean, and the converse is not
proved. gaudronRemondThm14Printed had no row in reviews.tsv (its earlier reading, of a different statement under the
same name, is the e1b31749 row above). The readings of the new rows are in docs/research/item-m-adversarial-readings.md.

Later (y3-f2-1127, the rows of #222 and #225): the rows of buzzardThm21Cor23V15 and serreRigidityLevel3 moved here.
Both were consequence rows of the y3FullThreeRepZ30 fold (#212). #225 replaces buzzardThm21Cor23V15 by
buzzardXDV15Lit, Buzzard's Thm 2.1 with Cor. 2.3 at V1(5) stated with his own level structures, and proves the old
statement from it in Lean; #222 proves, over Z[1/30], the fibre rigidity the chain took from serreRigidityLevel3,
from buzzardLemma22Full5 (Buzzard's Lemma 2.2) and milneThm125Pts (Milne's Thm 12.5) together with the rows
milneTorsionCount and milneZeroPreservingHomLN. With them
y3FullThreeRepZ30 is Y3Buzzard.y3FullThreeRepZ30_of_printed_xdv15 of eight rows. The readings of the old rows were of
the old statements; those of the new rows are sections 8 and 9 of docs/research/y3-adversarial-readings.md.
