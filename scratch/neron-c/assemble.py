"""neron-c: assemble scratch/neron-c/Check.lean. The two leaf statements are sliced verbatim from
the kernel files (which leaf-fold3's Leaves3.lean copies verbatim; see py/verbatim_check.py) into
fresh namespaces, and the theorems of ZInQKernel/Contrib/NeronC are applied to the copies.
Run from the repository root: python3 scratch/neron-c/assemble.py"""
import re, importlib.util
spec = importlib.util.spec_from_file_location("vc", "scratch/neron-c/py/verbatim_check.py")
src = open('scratch/neron-c/py/verbatim_check.py').read()
block_src = src[src.index('def block'):src.index('obj = ')]
exec(block_src)
t3 = block('ZInQKernel/HDecomp/Objects.lean', r"def NeronMappingAbelianScheme : Prop", 0)
t41 = block('ZInQKernel/HDecomp/Faltings/H5Neron.lean', r"def NeronModelExists : Prop", 0)
out = f'''import ZInQKernel.Contrib.NeronC.NMPInjective
import ZInQKernel.Contrib.NeronC.NeronGroup

/-! neron-c single-file check (assembled by `scratch/neron-c/assemble.py`; do not edit by hand).
The leaf statements T3 and T41 are copied verbatim (sliced from the kernel files, whose text
leaf-fold3's `Leaves3.lean` repeats verbatim) into the namespaces `NeronCCheck.PkgI2` and
`NeronCCheck.H5Neron`, and the reductions of `ZInQKernel/Contrib/NeronC` are applied to the copies. -/

namespace NeronCCheck.PkgI2

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj
open _root_.PkgI2

{t3}

end NeronCCheck.PkgI2

namespace NeronCCheck.H5Neron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

{t41}

end NeronCCheck.H5Neron

/-- T3 (verbatim copy) from its surjective half. -/
theorem NeronCCheck.t3_of_surj (h : ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{{0}}) :
    NeronCCheck.PkgI2.NeronMappingAbelianScheme.{{0}} :=
  ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj h

/-- The copy is the kernel's statement. -/
theorem NeronCCheck.t3_iff : NeronCCheck.PkgI2.NeronMappingAbelianScheme.{{0}} ↔
    _root_.PkgI2.NeronMappingAbelianScheme.{{0}} := Iff.rfl

/-- T41 (verbatim copy) from the scheme-level existence theorem. -/
theorem NeronCCheck.t41_of_scheme (h : ZInQ.Contrib.NeronC.NeronSchemeModelExists) :
    NeronCCheck.H5Neron.NeronModelExists :=
  ZInQ.Contrib.NeronC.neronModelExists_of_scheme h

/-- T41 (verbatim copy) from the existence half of the scheme-level theorem. -/
theorem NeronCCheck.t41_of_extension (h : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) :
    NeronCCheck.H5Neron.NeronModelExists :=
  ZInQ.Contrib.NeronC.neronModelExists_of_extension h

/-- The copy is the kernel's statement. -/
theorem NeronCCheck.t41_iff : NeronCCheck.H5Neron.NeronModelExists ↔
    ZInQ.H5Neron.NeronModelExists := Iff.rfl

#print axioms NeronCCheck.t3_of_surj
#print axioms NeronCCheck.t3_iff
#print axioms NeronCCheck.t41_of_scheme
#print axioms NeronCCheck.t41_iff
#print axioms NeronCCheck.t41_of_extension
#print axioms ZInQ.Contrib.NeronC.neronSchemeExtensionExists_of_neronModelExists
#print axioms ZInQ.Contrib.NeronC.neronMappingAbelianScheme_injective
#print axioms ZInQ.Contrib.NeronC.neronMappingAbelianSchemeSurj_of_nmp
#print axioms ZInQ.Contrib.NeronC.neronSchemeModelExists_of_neronModelExists
'''
open('scratch/neron-c/Check.lean', 'w').write(out)
print("wrote scratch/neron-c/Check.lean")
