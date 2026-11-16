"""Assemble scratch/flt-cqj/ModEq.lean = header + Count.lean body + ModEqMain.part."""
import re
c = open('scratch/flt-cqj/Count.lean').read()
body = c[c.index('/-! # flt-cqj: cyclic subgroups'):]
hdr = '''import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Reduction
import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_prime_pow

'''
open('scratch/flt-cqj/ModEq.lean', 'w').write(hdr + body + open('scratch/flt-cqj/ModEqMain.part').read())
