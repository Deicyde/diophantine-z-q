#!/usr/bin/env python3
"""Write a Backport/ file: header + selected line ranges of a commit-97a5b235 Tau Ceti module.
usage: mkbackport.py MODULE DSTNAME 'imports;...' 'prelude' 'ranges' 'postlude'
ranges like 51-58,60-129 (1-based, inclusive, of the nov01 source)."""
import sys, os
mod, dstname, imports, prelude, ranges, postlude = [a for a in sys.argv[1:] if a != "--force"]
src = os.path.expanduser('~/tc-nov01/' + mod.replace('.', '/') + '.lean')
lines = open(src).read().split('\n')
body = []
for r in ranges.split(','):
    a, b = map(int, r.split('-'))
    body += lines[a-1:b] + ['']
rel = mod[len('TauCeti.'):]
hdr = f'''/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- {mod}), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.{rel}` (task ring-class).
module

'''
imps = '\n'.join(i.strip() for i in imports.split(';') if i.strip())
out = hdr + imps + '\n\n' + prelude.replace('\\n', '\n') + '\n\n' + '\n'.join(body) + '\n' + postlude.replace('\\n', '\n') + '\n'
dst = 'ZInQKernel/Contrib/TauCeti/Backport/' + dstname.replace('.', '/') + '.lean'
assert not os.path.exists(dst) or '--force' in sys.argv, dst
os.makedirs(os.path.dirname(dst), exist_ok=True)
open(dst, 'w').write(out)
print('wrote', dst)
