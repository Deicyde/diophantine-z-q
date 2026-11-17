/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_ClassicalModularPolynomials
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def phiTwoC2 : Polynomial ℤ := -Polynomial.X ^ 2 + 1488 * Polynomial.X - 162000

def phiTwoC1 : Polynomial ℤ :=
  1488 * Polynomial.X ^ 2 + 40773375 * Polynomial.X + 8748000000

def phiTwoC0 : Polynomial ℤ :=
  Polynomial.X ^ 3 - 162000 * Polynomial.X ^ 2 + 8748000000 * Polynomial.X
    - 157464000000000

def phiTwo : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 3 + Polynomial.C phiTwoC2 * Polynomial.X ^ 2
    + Polynomial.C phiTwoC1 * Polynomial.X + Polynomial.C phiTwoC0

def phiThreeC3 : Polynomial ℤ :=
  -Polynomial.X ^ 3 + 2232 * Polynomial.X ^ 2 - 1069956 * Polynomial.X + 36864000

def phiThreeC2 : Polynomial ℤ :=
  2232 * Polynomial.X ^ 3 + 2587918086 * Polynomial.X ^ 2 + 8900222976000 * Polynomial.X
    + 452984832000000

def phiThreeC1 : Polynomial ℤ :=
  -1069956 * Polynomial.X ^ 3 + 8900222976000 * Polynomial.X ^ 2
    - 770845966336000000 * Polynomial.X + 1855425871872000000000

def phiThreeC0 : Polynomial ℤ :=
  Polynomial.X ^ 4 + 36864000 * Polynomial.X ^ 3 + 452984832000000 * Polynomial.X ^ 2
    + 1855425871872000000000 * Polynomial.X

def phiThree : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 4 + Polynomial.C phiThreeC3 * Polynomial.X ^ 3
    + Polynomial.C phiThreeC2 * Polynomial.X ^ 2
    + Polynomial.C phiThreeC1 * Polynomial.X + Polynomial.C phiThreeC0

def intFibre (Φ : Polynomial (Polynomial ℤ)) (n : ℤ) : Polynomial ℤ :=
  Φ.map (Polynomial.evalRingHom n)

end ModularCurve
