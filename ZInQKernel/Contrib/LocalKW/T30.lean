import ZInQKernel.Contrib.LocalKW.LocalKW
import ZInQKernel.Contrib.LocalKW.SqrtCrit

/-!
# Leaf T30 (L-B2c), the local square-root criterion, proved

`GlueDescent.B2Q.LeafSqrtCrit` follows from local Kronecker–Weber at every prime
(`ZInQ.Contrib.LocalKW.SqrtCrit.leafSqrtCrit_of_t16a`, t30-adelic's derivation, copied in
`SqrtCrit.lean`), and local Kronecker–Weber is `ZInQ.Contrib.localKroneckerWeber`.
-/

/-- **Leaf T30 (L-B2c), the local square-root criterion, proved**: local Kronecker–Weber
(`ZInQ.Contrib.localKroneckerWeber`) at every prime, fed to the t30-adelic derivation. -/
theorem ZInQ.Contrib.leafSqrtCrit : GlueDescent.B2Q.LeafSqrtCrit :=
  ZInQ.Contrib.LocalKW.SqrtCrit.leafSqrtCrit_of_t16a fun p _ => ZInQ.Contrib.localKroneckerWeber p
