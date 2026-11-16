/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_HopfAlgebra_CartierDualInstances
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace CartierDual

universe u v

section
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

instance instIsCocommViaBialgebra :
    @Coalgebra.IsCocomm R (CartierDual R A) _ _ _ (@Bialgebra.toCoalgebra R (CartierDual R A) _ _ (instBialgebra R A)) :=
  instIsCocomm R A

instance instModuleFiniteViaBialgebra :
    @Module.Finite R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFinite R A

instance instModuleFreeViaBialgebra :
    @Module.Free R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFree R A

end

section Test

universe w
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

theorem test_bialgebra_mixins {C : Type w} [Semiring C] [Bialgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

theorem test_commring_hopf_mixins {C : Type w} [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

example [Bialgebra R A] [Module.Finite R A] [Module.Free R A] : True :=
  test_bialgebra_mixins R (C := CartierDual R A)

example [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] : True :=
  test_commring_hopf_mixins R (C := CartierDual R A)

example [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] : True :=
  test_commring_hopf_mixins R (C := CartierDual R (CartierDual R A))

end Test

end CartierDual
