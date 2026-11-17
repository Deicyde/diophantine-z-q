# kleiman-proper fold spec: no fold

No open hypothesis is discharged or rerouted. `kleimanPicZeroProper` stays (docs/research/kleiman-proper.md §1).
The two possible replacements, `KleimanProper.KleimanPicZeroProperAbVar0` (narrowed) and
`KleimanProper.PicZeroDimLeAbVar0` (dimension core), are consequences (strict GLUE in kinds.tsv), so either fold
would turn one LEAF into one GLUE; autofold would refuse it without --allow-rise. Not written.
