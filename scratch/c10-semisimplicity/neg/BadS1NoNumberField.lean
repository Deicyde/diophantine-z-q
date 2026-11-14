/-
UNCOMPILED PRIVATE NEGATIVE CONTROL (must be REJECTED).
`semisimple_rL_of_globalTateComparison` invokes `PkgI3.FaltingsSemisimple`, which holds only over
a NUMBER FIELD. The intended rejection is the missing `NumberField` instance for a field that is
not one — not an import, parser or unrelated synthesis error.
-/
import S1Mapped

example : NumberField ℚ_[3] := inferInstance
