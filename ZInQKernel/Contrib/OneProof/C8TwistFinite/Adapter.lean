import ZInQKernel.Contrib.OneProof.C8TwistFinite.GlobalSplit
import ZInQKernel.Contrib.OneProof.ConradBridges
import ZInQKernel.Contrib.OneProof.C8Dicts

/-! # C8 without Conrad: the adapter to the chain's statements

`c8TwistFinite_proof` proves step C8's conclusion `C8Conrad.C8TwistFinite` (diophantine_zq.tex
L758-766: the twisting character of Pan's theorem has finite image) from R14
(`HSyn.EigenformRepExists`) and R13 (`PkgI4.EigenformHT`) alone, the inputs the consumer already
reads. It does not use `ConradAppB` (Conrad, App. B), `ConradAppBQp`, `ConradPropB3Qp`,
`LocAlgExponentEqWeight` or `TateTwistInvariantsInertia`. Inputs, all proved in the tree:

* `twistCharHTWt0_proof` (`C8Twist`): `ψ|G_{ℚ_5}` takes values in a finite `E/ℚ_5` and is
  Hodge–Tate of weight `0`; `Bridges.pureHT_of_hasHTWeights` turns that into the equivariant
  splitting `PureHT`;
* `finiteOfLocAlgTrivialQNoRam_of_dicts inertiaAtPDecomp_proof minkowskiInertiaQ_proof`
  (`C8CFT`, `C8Dicts`) at `k = 0`: class field theory over `ℚ`;
* `range_finite_of_pureHT` (this directory): the global splitting of `ψ` and Tate's theorem.

`g12DetPZ_proof` is the consumer's statement `G12DetPZ` with the inputs of
`C8Conrad.g12DetPZ_of_inputs` minus the bundle `C8Inputs`. -/

noncomputable section

namespace ZInQ.Contrib.C8TwistFinite

/-- Class field theory over `ℚ` in the unit form used here, from the tree's
`FiniteOfLocAlgTrivialQNoRam` at `k = 0`. -/
theorem noRamUnits_five : NoRamUnits 5 := by
  intro β hβ
  exact HDec.G0Galois.C8Conrad.finiteOfLocAlgTrivialQNoRam_of_dicts
    HDec.G0Galois.C8Conrad.inertiaAtPDecomp_proof HDec.G0Galois.C8Conrad.minkowskiInertiaQ_proof
    5 β ⟨0, fun u _ σ hσ => hβ u σ hσ⟩

/-- **Step C8 without Conrad's App. B**: the twist has finite image, from R13 and R14. -/
theorem c8TwistFinite_proof (hR : HDec.HSyn.EigenformRepExists)
    (hHT : HDec.PkgI4.EigenformHT) : HDec.G0Galois.C8Conrad.C8TwistFinite := by
  intro r N χ g ψ ιC ιL S hN hg hr hatt
  obtain ⟨E, hE, ψE, hlift, hwt⟩ :=
    HDec.G0Galois.C8Conrad.twistCharHTWt0_proof hR hHT r N χ g ψ ιC ιL S hN hg hr hatt
  exact range_finite_of_pureHT 5 noRamUnits_five ψ E.val.toRingHom ψE hlift
    (HDec.G0Galois.C8Conrad.Bridges.pureHT_of_hasHTWeights 5 ψE 0 hwt)

/-- **C8's consumer `G12DetPZ` without `C8Inputs`** (the replacement for
`g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`). -/
theorem g12DetPZ_proof (hR : HDec.HSyn.EigenformRepExists) (hHT : HDec.PkgI4.EigenformHT)
    (h9 : HDec.G0Galois.G9GlueNoT23) (hdR : HDec.PkgI4.DeRhamComparison) :
    HDec.G0Galois.G12DetPZ :=
  HDec.G0Galois.C8Conrad.g12DetPZ_of_twistFinite (c8TwistFinite_proof hR hHT) h9 hdR

end ZInQ.Contrib.C8TwistFinite
