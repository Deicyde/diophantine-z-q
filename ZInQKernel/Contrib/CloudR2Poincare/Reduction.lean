import ZInQKernel.Contrib.CloudR2Poincare.Skeleton
import ZInQKernel.Contrib.CloudR2Poincare.L3.KernelComplementProof
import ZInQKernel.Contrib.CloudR2Poincare.L4.ComplementIsogeny

/-!
# H-72: `PoincareComplement` reduced to the single input `PolarizationRetract`

Round 2, 2026-11-14.

Two of the three obligations of `Skeleton.lean` are **proved**:
* `ZInQ.Contrib.CloudR2Poincare.L3.KernelComplement_proof : KernelComplement` (lane L3): the reduced identity
  component of the kernel of a homomorphism `φ : J → D` is an abelian subvariety with `dim J ≤ dim Z + dim D`
  (Cartier smoothness in characteristic `0`, Stacks 04KV, the closed-point dimension formula, all ported from
  AxiomMath/Stacks with notices);
* `ZInQ.Contrib.CloudR2Poincare.L4.ComplementIsogeny_proof : ComplementIsogeny` (lane L4): the sum map
  `B × Z → J` is finite and surjective.

Hence `PoincareComplement` follows from `PolarizationRetract` alone. This is a **conditional** reduction: it is
not a proof of `PoincareComplement`, and `PolarizationRetract` is not assumed anywhere as a fact.
`PolarizationRetract` (a homomorphism `φ : J → D` with `φ ∘ i` an isogeny and `dim D ≤ dim B`) is the
polarization input: classically `D = B^∨` and `φ = i^∨ ∘ φ_L` (Mumford, *Abelian varieties*, §6 Application 1,
§8 Thm 1, §19 Thm 1; Milne 1986 §§8-12). Lanes L1/L2 proved large parts of it.
-/

namespace ZInQ.Contrib.CloudR2Poincare

/-- **H-72 reduced to the polarization input.** `PolarizationRetract → PoincareComplement`, using the proved
`KernelComplement` and `ComplementIsogeny`. -/
theorem poincareComplement_of_polarizationRetract (hP : PolarizationRetract) :
    ZInQ.Contrib.AVB1.PoincareComplement :=
  poincareComplement_of_obligations hP L3.KernelComplement_proof L4.ComplementIsogeny_proof

end ZInQ.Contrib.CloudR2Poincare
