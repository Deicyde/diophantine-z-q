import ZInQKernel.Density.Abel
import ZInQKernel.Density.PrimeTail
import ZInQKernel.Density.Lattice
import ZInQKernel.Density.Residues
import ZInQKernel.Density.PropD
import ZInQKernel.Density.PropDFinal

/-!
# Proposition D modulo the uniform bad-prime bound (pd-paper §§2–5)

Root module of `ZInQKernel/Density/` (task pd-lean-2): Abel summation, the residue set `A_L`,
the prime tail, the lattice count and the conditional assembly
`goodPrimeDensity_of_uniformBadBound`. `PropDFinal` combines it with pd-sieve's
`uniformBadBound` into the unconditional `goodPrimeDensity : GoodPrimeDensity`.
-/
