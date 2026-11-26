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

Later (hct-cassels-fold): the row of hCT moved here. The field keeps its name, but its statement changed from
Poonen–Stoll's restatement of Cassels' theorem in the introduction (`PoleS12.CasselsTatePairingCurves`) to the
weaker form printed by Poonen–Stoll (`PoleS12.CasselsTatePairingCurvesPS`), which Lean proves from Cassels (1962),
Theorem 1.1, read as `SelmerTwoPower.CasselsIVThm11Elliptic`. The reading was of the old statement and does not rate
the new one; the reading of Cassels's theorem is in reviews.tsv (docs/research/cassels-adversarial-readings.md).
