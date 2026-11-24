# Deligne–Serre finite-group lifting

`DS966Small.exists_complex_character_lift` lifts a two-dimensional representation of a finite group of order prime to ℓ from the algebraic closure of Fℓ to ℂ on the **same group**. If the coefficient number field contains the roots of unity of an exponent divisible by the group order, the complex and residual traces and determinants come from the same integral sums and products of two such roots. The comparison uses the specified reduction on the ring of integers, not an unspecified residue-field automorphism.

The proof uses the completion at the kernel of that reduction, realizes the finite matrix coefficient field by an unramified extension, lifts the matrices by square-zero averaging and adic completeness, and specializes their character to ℂ by Zariski's lemma. No embedding of a completed local field into ℂ is assumed.

This is a dependency for `DSThm966EV.DSThm966Printed`, not a proof of that board row. In particular, it does not supply the weight-one residual representations or bound the density of exceptional traces.

To check the endpoint, build `+ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966ComplexLift`. Import that module in a scratch file and run `#print axioms DS966Small.exists_complex_character_lift`; the result is `propext`, `Classical.choice`, and `Quot.sound` only. The headline build need not import this module while the Deligne–Serre row remains open.
