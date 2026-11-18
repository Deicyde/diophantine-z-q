#!/usr/bin/env python3
"""d2a6b: PruneScan (pi0-fold's scratch/pi0-fold/PruneScan.lean, adapted) on the bypass module.
Writes scratch/d2a6b/PruneScanBypass.lean = the bypass module (BypassFold.lean) + `import Lean` + the scan,
run on two roots: the base top `sixContactMin_of_open76` (control) and the bypass top `sixContactMin_of_open77`.
Bundles = Prop structures of ZInQKernel.OneProof.*, ZInQKernel.Contrib.OneProof.* and this file.
Usage: python3 scratch/d2a6b/gen/gen_prunescan.py [BYPASS.lean] [TOP]"""
import sys
byp = sys.argv[1] if len(sys.argv) > 1 else 'scratch/d2a6b/BypassFold.lean'
top = sys.argv[2] if len(sys.argv) > 2 else 'sixContactMin_of_open77'
L = open(byp).read().split('\n')
imps = [l for l in L if l.startswith('import ')] + ['import Lean']
body = [l for l in L if not l.startswith('import ') and not l.startswith('#print')]
tail = open('scratch/d2a6b/gen/prunescan_tail.lean').read()
calls = ('\nopen Lean in\nrun_cmd PruneScan.scan `HDec.HSyn.sixContactMin_of_open76 "base"\n'
         f'open Lean in\nrun_cmd PruneScan.scan `HDec.HSyn.{top} "bypass"\n')
open('scratch/d2a6b/PruneScanBypass.lean', 'w').write('\n'.join(imps + body) + '\nopen Lean\n\n' + tail + calls)
print('wrote scratch/d2a6b/PruneScanBypass.lean')
