import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.InfRes
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.LocalDescent
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Kummer
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.LocalDescentInput
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Transfer
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.AdjustedRep
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Shapiro
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.ShapiroInput
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Witness
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Cartesian
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.MackeyCor

/-!
# HeegnerCohomology: the cohomological layer of `ex:arith-finite-heegner` (tex 2834–3410)

Index of the area (all `PROVED`, standard axioms):

* `InfRes`: (H8) five-term sequence over continuous cohomology with transgression; (H9);
  RC10's `InfResInput` (`infResInputGenuine`, `infResInputTorsion`); node `H8H9Node`.
* `LocalDescent`: (H10) successive-correction argument (Lang's theorem and the formal-group
  structure as hypotheses), `H¹(Gal(L/K), L) = 0` from the normal basis, component bound; nodes
  `H10Node`, `AdditiveH90Node`; RC10 fields `hH10`, `exInf`.
* `Kummer`: the `Gal(M_I/H_f)`-equivariant Kummer sequence over `M_I`; RC10's `KummerSequence`;
  node `KummerNode`.
* `LocalDescentInput`: RC10's `LocalDescentInput`, all fields genuine; integral local descent.
* `Transfer`: (H21) `d𝒯_θ = 𝒯_θ d` in every degree; Kummer of the weighted sum; decomposition-group
  orbit terms (local Mackey decomposition); node `TransferCommNode`.
* `AdjustedRep`: the adjusted representative at a derivative prime (tex 3122–3128).
* `Shapiro`, `ShapiroInput`: (H20)–(H21) Shapiro then coefficient map, in every degree; `Sh` is a
  section of Shapiro's map; RC10's `ShapiroTransferInput`; node `ShapiroNode`.
* `Witness`: (H22) Selmer-cone witnesses.
* `Cartesian`: restriction and corestriction commute in Cartesian squares; node `CartesianNode`.
* `MackeyCor`: each Mackey orbit term is the local corestriction of the transported cocycle; node
  `MackeyCorNode`.
-/
