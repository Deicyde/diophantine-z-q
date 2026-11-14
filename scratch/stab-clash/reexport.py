# Replace a vendored commit-5a01f5fe file's body by a public import of the vendored module that
# supersedes it (keeps copyright header + provenance line, adds the Modified line).
import sys
path, newmod, why = sys.argv[1], sys.argv[2], sys.argv[3]
L = open(path).read().split('\n')
assert L[5].startswith('-- Vendored from Tau Ceti'), path
head = '\n'.join(L[:6])
mod = 'ZInQKernel.Contrib.TauCeti.' + newmod
body = f"""{head}
-- Modified for the Z-in-Q kernel: every declaration removed and the module {mod} (vendored), {why}, publicly imported instead (task stab-clash: the two modules declared the same names, so no file could import both).
module

public import {mod}

/-!
This commit-5a01f5fe module is superseded by `{mod}`, which declares every one of its names
({why}). It is kept as a re-export so that every module of `ZInQKernel/Contrib/` can be imported
in one Lean environment (task stab-clash).
-/
"""
open(path, 'w').write(body)
