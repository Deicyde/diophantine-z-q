import ZInQKernel.Contrib.CloudR2CM.SerreTate.CMFieldOfDefinition
import ZInQKernel.Contrib.CloudR2CM.SerreTate.NOSAdapter
import ZInQKernel.Contrib.CloudR2CM.SerreTate.ProperModelStatements
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron

/-!
# The assembly: `CMPotentialGood` by the Serre–Tate route

Statement only; it supplies no proof. `HDec.CMBranch.CMPotentialGood` (CM elliptic curves have
potentially good reduction; Serre–Tate, Ann. of Math. 88 (1968), §6, Thm 7; numbers UNVERIFIED) is
stated to follow from the five route statements and the open field
`ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind`, used unchanged and only as the premise of
P4. The target is used unchanged.

Route, for `E/L` of dimension `1` with `IsCMBy E k R`:
* P0 (`CMFieldOfDefinition`): a finite `L'/L` over which every geometric endomorphism is defined;
* P2 (`P2TorsionField`, with `2²` and `3`): a finite `L₁/L` receiving `L'`, with `E[4]` and `E[3]`
  rational over `L₁`; P0 at `M = L₁` gives `End(E_{L₁}) ≅ R`;
* at each finite place `O` of `L₁`, one of `2, 3` is a unit in `O` (two coprime integers cannot both
  lie in the maximal ideal of a local ring); for that `ℓ`, with `w` over `O`:
  P1 (`P1FiniteInertia`) gives a finite inertia image on `T_ℓ(E_{L₁})`, the rational torsion gives
  inertia trivial on `E[ℓ^k]`, `ℓ^k ∈ {4, 3}`, and P2 (`P2InertiaRigidity`) gives inertia trivial on
  `T_ℓ`; P3 (`P3GoodReduction`) gives good reduction at `O`;
* P4 (`P4ProperModel`, with the open field as its premise): from good reduction at every finite
  place of `L₁`, a group model of `E` over `𝓞_{L₁}` that is proper, which is `CMPotentialGood`'s
  conclusion.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.CMSerreTate

/-- **Assembly (signature only).** P0, P1, P2, P3, P4 and the open field
`NeronSchemeExtensionDedekind` give `HDec.CMBranch.CMPotentialGood`. -/
def CMPotentialGoodAssembly : Prop :=
  CMFieldOfDefinition → P1FiniteInertia → P2SerreChoice → P3GoodReduction → P4ProperModel →
    _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind →
    HDec.CMBranch.CMPotentialGood

end HDec.CMSerreTate
