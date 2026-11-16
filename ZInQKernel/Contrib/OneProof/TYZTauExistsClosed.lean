import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.LegendreThreeSquares
import ZInQKernel.Contrib.OneProof.JonesPall

/-!
# Closed TYZ admissible-quaternion embedding supplier

This is a direct consumer of the exact Legendre and Jones–Pall suppliers,
not a new proof of either representation theorem. The defining module and
both proof modules are imported; `ZInQKernel.OneProof.Main` is not imported.

Specification source: fork `2880fef1e827a05ab9238cd200e555c585f00e30`,
`TYZLemma29Mod2.lean:617–637, 776–780, 864–867`. The later public source
base `0caafe66103a89994198e26d8d68af6ae227ed0e` changes only STATUS.md.
Supplier sources: Legendre draft PR36 at `47ca4df214d1402caa3de40c7d6f661567120fcd`
and Jones–Pall draft PR38 at `a9bc2e35c42a34a2be1cc3eeccb33cbc41de53c4`.
The shared Atlas module is included once at its canonical path.

The first two exports have no additional mathematical input. The final
assembly explicitly retains four TYZ hypotheses; it is not an unconditional
H29 or H10 theorem. Verification and publication status are recorded separately.
-/

set_option autoImplicit false

namespace ZInQ.Contrib.OneProof.TYZTauExistsClosed

open ZInQ.Contrib.TYZDecomp.H29Split

/-- Exact composite three-square statement, with no caller-supplied premise. -/
theorem legendreJonesPall_proof : LegendreJonesPall :=
  legendreJonesPall_of
    ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
    ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof

/-- Exact existence of an admissible quaternion embedding on the original objects. -/
theorem tyzTauExists_proof : TYZTauExists :=
  tyzTauExists_of_legendreJonesPall legendreJonesPall_proof

/-- Conditional H29 assembly: every remaining TYZ hypothesis is an explicit input. -/
theorem tyzLemma29Mod2_of_fourLeaves
    (hfx : TYZTestVectorExists) (hNe3 : TYZLemma29PrintedNe3)
    (h31 : TYZThm21At31) (h23 : TYZProp23Printed) :
    ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2 :=
  tyzLemma29Mod2_of_sixLeaves
    ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
    ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof
    hfx hNe3 h31 h23

end ZInQ.Contrib.OneProof.TYZTauExistsClosed
